/-
# Completed transfer on the finite-character packet colimit

The finite SU(2) character packets already form a cutoff-coherent algebraic
colimit with the exact interacting Wilson Gram.  This file makes the next
functional-analytic step constructive: the physical diagonal packet transfer
is linear and contractive for that colimit GNS datum, hence descends to its
explicit Cauchy completion.  The completed operator is self-adjoint, positive,
and contractive, and its distinguished vacuum is the nonzero trivial-character
packet fixed by transfer.

Honest scope: this is the completed all-character one-link sector.  It is not
yet the overlapping four-dimensional finite-volume observable algebra, and it
does not supply a thermodynamic or continuum limit.
-/

import YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS
import YMGap.Continuum.LinearTransferOperator

namespace YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit
open YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS

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

/-! ## Exact scalar module and carrier linearity -/

theorem stagedSmul_sub (q : Q') (A B : StagedPacket) :
    StagedEqv
      (stagedSmul q (packetColimitGNS.sub A B))
      (packetColimitGNS.sub (stagedSmul q A) (stagedSmul q B)) := by
  intro s
  refine Q'.eqv_trans _
    (q * (coeffAt A.packet s + -(coeffAt B.packet s))) _ ?_ ?_
  · refine Q'.eqv_trans _ (q * coeffAt (stagedAdd A (stagedNeg B)).packet s) _
      (coeffAt_stagedSmul q (stagedAdd A (stagedNeg B)) s) ?_
    exact Q'.mul_eqv_congr_left q _ _
      (Q'.eqv_trans _
        (coeffAt A.packet s + coeffAt (stagedNeg B).packet s) _
        (coeffAt_stagedAdd A (stagedNeg B) s)
        (Q'.add_eqv_congr_left _ _ _ (coeffAt_stagedNeg B s)))
  · refine Q'.eqv_trans _
      (q * coeffAt A.packet s + -(q * coeffAt B.packet s)) _ (by ring_qeqv) ?_
    refine Q'.eqv_trans _
      (coeffAt (stagedSmul q A).packet s +
        -(coeffAt (stagedSmul q B).packet s)) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.eqv_symm (coeffAt_stagedSmul q A s))
        (Q'.neg_eqv_congr _ _
          (Q'.eqv_symm (coeffAt_stagedSmul q B s)))
    · refine Q'.eqv_trans _
        (coeffAt (stagedSmul q A).packet s +
          coeffAt (stagedNeg (stagedSmul q B)).packet s) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm (coeffAt_stagedNeg (stagedSmul q B) s))
      · exact Q'.eqv_symm
          (coeffAt_stagedAdd (stagedSmul q A)
            (stagedNeg (stagedSmul q B)) s)

/-- The exact packet-colimit GNS datum with genuine rational scalar action. -/
def packetColimitSmulGNS : SmulGNSData where
  toGNSData := packetColimitGNS
  smul_sub := stagedSmul_sub

theorem stagedTransfer_add (A B : StagedPacket) :
    StagedEqv (stagedTransfer (stagedAdd A B))
      (stagedAdd (stagedTransfer A) (stagedTransfer B)) := by
  intro s
  refine Q'.eqv_trans _
    (packetEigen s * coeffAt (stagedAdd A B).packet s) _
    (coeffAt_packetTransfer (stagedAdd A B).packet s) ?_
  refine Q'.eqv_trans _
    (packetEigen s *
      (coeffAt A.packet s + coeffAt B.packet s)) _
    (Q'.mul_eqv_congr_left _ _ _ (coeffAt_stagedAdd A B s)) ?_
  refine Q'.eqv_trans _
    (packetEigen s * coeffAt A.packet s +
      packetEigen s * coeffAt B.packet s) _ (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    (coeffAt (stagedTransfer A).packet s +
      coeffAt (stagedTransfer B).packet s) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_symm (coeffAt_packetTransfer A.packet s))
      (Q'.eqv_symm (coeffAt_packetTransfer B.packet s))
  · exact Q'.eqv_symm
      (coeffAt_stagedAdd (stagedTransfer A) (stagedTransfer B) s)

theorem stagedTransfer_smul (q : Q') (A : StagedPacket) :
    StagedEqv (stagedTransfer (stagedSmul q A))
      (stagedSmul q (stagedTransfer A)) := by
  intro s
  refine Q'.eqv_trans _
    (packetEigen s * coeffAt (stagedSmul q A).packet s) _
    (coeffAt_packetTransfer (stagedSmul q A).packet s) ?_
  refine Q'.eqv_trans _
    (packetEigen s * (q * coeffAt A.packet s)) _
    (Q'.mul_eqv_congr_left _ _ _ (coeffAt_stagedSmul q A s)) ?_
  refine Q'.eqv_trans _
    (q * (packetEigen s * coeffAt A.packet s)) _ (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    (q * coeffAt (stagedTransfer A).packet s) _
    (Q'.mul_eqv_congr_left q _ _
      (Q'.eqv_symm (coeffAt_packetTransfer A.packet s))) ?_
  exact Q'.eqv_symm (coeffAt_stagedSmul q (stagedTransfer A) s)

theorem stagedTransfer_sub (A B : StagedPacket) :
    StagedEqv
      (stagedTransfer (packetColimitGNS.sub A B))
      (packetColimitGNS.sub (stagedTransfer A) (stagedTransfer B)) := by
  intro s
  refine Q'.eqv_trans _
    (packetEigen s *
      (coeffAt A.packet s + -(coeffAt B.packet s))) _ ?_ ?_
  · refine Q'.eqv_trans _
      (packetEigen s *
        coeffAt (stagedAdd A (stagedNeg B)).packet s) _
      (coeffAt_packetTransfer (stagedAdd A (stagedNeg B)).packet s) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _
        (coeffAt A.packet s + coeffAt (stagedNeg B).packet s) _
        (coeffAt_stagedAdd A (stagedNeg B) s)
        (Q'.add_eqv_congr_left _ _ _ (coeffAt_stagedNeg B s)))
  · refine Q'.eqv_trans _
      (packetEigen s * coeffAt A.packet s +
        -(packetEigen s * coeffAt B.packet s)) _ (by ring_qeqv) ?_
    refine Q'.eqv_trans _
      (coeffAt (stagedTransfer A).packet s +
        -(coeffAt (stagedTransfer B).packet s)) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.eqv_symm (coeffAt_packetTransfer A.packet s))
        (Q'.neg_eqv_congr _ _
          (Q'.eqv_symm (coeffAt_packetTransfer B.packet s)))
    · refine Q'.eqv_trans _
        (coeffAt (stagedTransfer A).packet s +
          coeffAt (stagedNeg (stagedTransfer B)).packet s) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm (coeffAt_stagedNeg (stagedTransfer B) s))
      · exact Q'.eqv_symm
          (coeffAt_stagedAdd (stagedTransfer A)
            (stagedNeg (stagedTransfer B)) s)

/-! ## Exact packet and staged contraction -/

private theorem eigen_square_le_one (s : Nat) :
    packetEigen s * packetEigen s ≤ (1 : Q') := by
  have h0 := packetEigen_nonneg s
  have h1 := packetEigen_le_one s
  have hm1 := Q'.mul_le_mul_of_nonneg_right _ _ (packetEigen s) h1 h0
  have hm2 := Q'.mul_le_mul_of_nonneg_left _ _ (1 : Q') h1 (by decide)
  exact Q'.le_trans' _ ((1 : Q') * packetEigen s) _ hm1
    (Q'.le_trans' _ ((1 : Q') * 1) _ hm2
      (Q'.le_of_eqv (Q'.mul_one_eqv 1)))

private theorem transfer_term_le {N : Nat}
    (P : CharacterPacket N) (s : Nat) :
    packetEigen s *
        ((packetEigen s * coeffAt P s) *
          (packetEigen s * coeffAt P s)) ≤
      packetEigen s * (coeffAt P s * coeffAt P s) := by
  let lam := packetEigen s
  let c := coeffAt P s
  let base := lam * (c * c)
  have hbase : (0 : Q') ≤ base :=
    Q'.mul_nonneg _ _ (packetEigen_nonneg s)
      (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg c)
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ base
    (eigen_square_le_one s) hbase
  dsimp [lam, c, base] at hm ⊢
  refine Q'.le_trans' _
    ((packetEigen s * packetEigen s) *
      (packetEigen s * (coeffAt P s * coeffAt P s))) _
    (Q'.le_of_eqv (by ring_qeqv)) ?_
  exact Q'.le_trans' _
    ((1 : Q') *
      (packetEigen s * (coeffAt P s * coeffAt P s))) _ hm
    (Q'.le_of_eqv (Q'.one_mul_eqv _))

theorem packetTransfer_contraction {N : Nat} (P : CharacterPacket N) :
    packetWilsonGram (packetTransfer P) (packetTransfer P) ≤
      packetWilsonGram P P := by
  have hsum := fsum_le_fsum (transfer_term_le P) (N + 1)
  exact le_of_eqv_le (packetWilsonGram_transfer_diagonal P)
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (Q'.eqv_symm (packetWilsonGram_diagonal P P))))

theorem stagedGram_self_eq_packet (A : StagedPacket) :
    stagedGram A A ≈ packetWilsonGram A.packet A.packet := by
  refine Q'.eqv_trans _
    (packetWilsonGram
      (padPacket (Nat.le_refl A.cutoff) A.packet)
      (padPacket (Nat.le_refl A.cutoff) A.packet)) _
    (stagedGram_pad_to A A (Nat.le_refl _) (Nat.le_refl _)) ?_
  exact packetWilsonGram_congr (padPacket_refl A.packet)
    (padPacket_refl A.packet)

theorem stagedTransfer_contraction (A : StagedPacket) :
    stagedGram (stagedTransfer A) (stagedTransfer A) ≤ stagedGram A A := by
  refine le_of_eqv_le (stagedGram_self_eq_packet (stagedTransfer A)) ?_
  exact Q'.le_trans' _ _ _ (packetTransfer_contraction A.packet)
    (Q'.le_of_eqv (Q'.eqv_symm (stagedGram_self_eq_packet A)))

theorem stagedGram_smul_self (q : Q') (A : StagedPacket) :
    stagedGram (stagedSmul q A) (stagedSmul q A) ≈
      (q * q) * stagedGram A A := by
  refine Q'.eqv_trans _
    (q * stagedGram A (stagedSmul q A)) _
    (stagedGram_smul_left q A (stagedSmul q A)) ?_
  refine Q'.eqv_trans _
    (q * stagedGram (stagedSmul q A) A) _
    (Q'.mul_eqv_congr_left q _ _
      (stagedGram_symm A (stagedSmul q A))) ?_
  refine Q'.eqv_trans _
    (q * (q * stagedGram A A)) _
    (Q'.mul_eqv_congr_left q _ _ (stagedGram_smul_left q A A)) ?_
  ring_qeqv

/-- The exact cutoff-independent spectral edge on the algebraic colimit:
every vacuum-free staged packet contracts at least as strongly as scalar
multiplication by `1/8`. -/
theorem stagedVacuumFree_edge_contraction (A : StagedPacket)
    (hA : StagedVacuumFree A) :
    stagedGram (stagedTransfer A) (stagedTransfer A) ≤
      stagedGram
        (stagedSmul SU2PeterWeylWilsonBlock.eighth A)
        (stagedSmul SU2PeterWeylWilsonBlock.eighth A) := by
  let e := SU2PeterWeylWilsonBlock.eighth
  have hfinite := staged_vacuumfree_uniform_contraction A hA
  refine le_of_eqv_le (stagedGram_self_eq_packet (stagedTransfer A)) ?_
  refine Q'.le_trans' _
    ((e * e) * packetWilsonGram A.packet A.packet) _ hfinite ?_
  refine Q'.le_trans' _
    ((e * e) * stagedGram A A) _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left (e * e) _ _
      (Q'.eqv_symm (stagedGram_self_eq_packet A)))) ?_
  exact Q'.le_of_eqv
    (Q'.eqv_symm (stagedGram_smul_self e A))

theorem stagedTransfer_distSq_contraction (A B : StagedPacket) :
    packetColimitGNS.distSqQ (stagedTransfer A) (stagedTransfer B) ≤
      packetColimitGNS.distSqQ A B := by
  have hsub := stagedTransfer_sub A B
  exact le_of_eqv_le
    (Q'.eqv_symm (packetColimitGNS.B_diag_congr hsub))
    (stagedTransfer_contraction (packetColimitGNS.sub A B))

/-- The physical packet transfer as a contractive diagonal symbol on the
colimit GNS carrier. -/
def packetColimitDiagonalSymbol : DiagonalTransferSymbol packetColimitSmulGNS where
  Dv := stagedTransfer
  Dv_congr := stagedTransfer_congr
  distSqQ_Dv := stagedTransfer_distSq_contraction
  Dv_add := stagedTransfer_add
  Dv_smul := stagedTransfer_smul

/-! ## Carrier Osterwalder--Schrader laws -/

theorem stagedTransfer_selfAdjoint (A B : StagedPacket) :
    stagedGram (stagedTransfer A) B ≈ stagedGram A (stagedTransfer B) := by
  let K := Nat.max A.cutoff B.cutoff
  have hA : A.cutoff ≤ K := Nat.le_max_left _ _
  have hB : B.cutoff ≤ K := Nat.le_max_right _ _
  refine Q'.eqv_trans _
    (packetWilsonGram
      (padPacket hA (stagedTransfer A).packet)
      (padPacket hB B.packet)) _
    (stagedGram_pad_to (stagedTransfer A) B hA hB) ?_
  refine Q'.eqv_trans _
    (packetWilsonGram
      (packetTransfer (padPacket hA A.packet))
      (padPacket hB B.packet)) _
    (packetWilsonGram_congr
      (by simpa only [stagedTransfer] using padPacket_transfer hA A.packet)
      (fun _ => Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _
    (packetWilsonGram
      (padPacket hA A.packet)
      (packetTransfer (padPacket hB B.packet))) _
    (packetTransfer_selfAdjoint _ _) ?_
  refine Q'.eqv_trans _
    (packetWilsonGram
      (padPacket hA A.packet)
      (padPacket hB (stagedTransfer B).packet)) _
    (packetWilsonGram_congr (fun _ => Q'.eqv_refl _)
      (packetEqv_symm (by
        simpa only [stagedTransfer] using padPacket_transfer hB B.packet))) ?_
  exact Q'.eqv_symm
    (stagedGram_pad_to A (stagedTransfer B) hA hB)

theorem stagedTransfer_positive (A : StagedPacket) :
    (0 : Q') ≤ stagedGram (stagedTransfer A) A := by
  have hA : A.cutoff ≤ A.cutoff := Nat.le_refl _
  have he : stagedGram (stagedTransfer A) A ≈
      packetWilsonGram
        (packetTransfer (padPacket hA A.packet))
        (padPacket hA A.packet) := by
    refine Q'.eqv_trans _
      (packetWilsonGram
        (padPacket hA (stagedTransfer A).packet)
        (padPacket hA A.packet)) _
      (stagedGram_pad_to (stagedTransfer A) A hA hA) ?_
    exact packetWilsonGram_congr
      (by simpa only [stagedTransfer] using padPacket_transfer hA A.packet)
      (fun _ => Q'.eqv_refl _)
  exact Q'.le_trans' _ _ _
    (packetTransfer_positive (padPacket hA A.packet))
    (Q'.le_of_eqv (Q'.eqv_symm he))

/-! ## Descent to the explicit Cauchy completion -/

/-- The physical packet transfer on the completed all-character colimit. -/
def completedPacketTransfer :
    GNSCompletionSpace packetColimitGNS →
      GNSCompletionSpace packetColimitGNS :=
  packetColimitDiagonalSymbol.TqSymb

theorem completedPacketTransfer_embed (A : StagedPacket) :
    completedPacketTransfer (embedV packetColimitGNS A) =
      embedV packetColimitGNS (stagedTransfer A) :=
  packetColimitDiagonalSymbol.TqSymb_embed A

theorem cinnerRep_selfAdjoint
    (x y : CauchyGNS packetColimitGNS) :
    CReal.Equiv
      (packetColimitGNS.cinnerRep
        (packetColimitDiagonalSymbol.cDiagCauchy x) y)
      (packetColimitGNS.cinnerRep x
        (packetColimitDiagonalSymbol.cDiagCauchy y)) := by
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ'
      (packetColimitGNS.cInnerSeq
        (packetColimitDiagonalSymbol.cDiagCauchy x) y n))
    (bSeq := fun n => CReal.ofQ'
      (packetColimitGNS.cInnerSeq x
        (packetColimitDiagonalSymbol.cDiagCauchy y) n))
    (fun n =>
      PositiveTimeCompressedTransfer.PositiveTimeCompression.lifted_eqv
        (stagedTransfer_selfAdjoint (x.seq n) (y.seq n))) ?_ ?_
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

theorem completedPacketTransfer_selfAdjoint
    (x y : GNSCompletionSpace packetColimitGNS) :
    packetColimitGNS.cinnerCompl (completedPacketTransfer x) y =
      packetColimitGNS.cinnerCompl x (completedPacketTransfer y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  exact cinnerRep_selfAdjoint u v

theorem completedPacketTransfer_positive
    (x : GNSCompletionSpace packetColimitGNS) :
    CReal.RCnonneg
      (packetColimitGNS.cinnerCompl (completedPacketTransfer x) x) := by
  refine Quotient.inductionOn x ?_
  intro u
  show CReal.leEv CReal.czero
    (packetColimitGNS.cinnerRep
      (packetColimitDiagonalSymbol.cDiagCauchy u) u)
  exact CReal.leEv_ofQ'_of_approx_ge
    (fun _ => stagedTransfer_positive (u.seq _))

theorem cinnerRep_contraction (x : CauchyGNS packetColimitGNS) :
    CReal.leEv
      (packetColimitGNS.cinnerRep
        (packetColimitDiagonalSymbol.cDiagCauchy x)
        (packetColimitDiagonalSymbol.cDiagCauchy x))
      (packetColimitGNS.cinnerRep x x) := by
  refine CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_ofQ'CauchySeq _ _) ?_
  intro epsilon hepsilon
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _
    (stagedTransfer_contraction (x.seq n))
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩

/-- The `1/8` edge estimate survives completion for every Cauchy sequence
whose representatives are exactly vacuum-free.  The hypothesis is data on the
chosen constructive representative; no classical orthogonal projection is
used. -/
theorem cinnerRep_vacuumFree_edge_contraction
    (x : CauchyGNS packetColimitGNS)
    (hx : ∀ n, StagedVacuumFree (x.seq n)) :
    CReal.leEv
      (packetColimitGNS.cinnerRep
        (packetColimitDiagonalSymbol.cDiagCauchy x)
        (packetColimitDiagonalSymbol.cDiagCauchy x))
      (packetColimitGNS.cinnerRep
        (packetColimitSmulGNS.cSmulCauchy
          SU2PeterWeylWilsonBlock.eighth x)
        (packetColimitSmulGNS.cSmulCauchy
          SU2PeterWeylWilsonBlock.eighth x)) := by
  refine CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_ofQ'CauchySeq _ _) ?_
  intro epsilon hepsilon
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _
    (stagedVacuumFree_edge_contraction (x.seq n) (hx n))
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩

theorem completedPacketTransfer_contraction
    (x : GNSCompletionSpace packetColimitGNS) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketTransfer x) (completedPacketTransfer x))
      (packetColimitGNS.cinnerCompl x x) := by
  refine Quotient.inductionOn x ?_
  intro u
  exact cinnerRep_contraction u

/-- Completed `1/8` norm-edge estimate on the explicitly presented
vacuum-free completion. -/
theorem completedPacketTransfer_vacuumFree_edge_contraction
    (x : CauchyGNS packetColimitGNS)
    (hx : ∀ n, StagedVacuumFree (x.seq n)) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketTransfer
          (Quotient.mk (cauchySetoid packetColimitGNS) x))
        (completedPacketTransfer
          (Quotient.mk (cauchySetoid packetColimitGNS) x)))
      (packetColimitGNS.cinnerCompl
        (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth
          (Quotient.mk (cauchySetoid packetColimitGNS) x))
        (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth
          (Quotient.mk (cauchySetoid packetColimitGNS) x))) :=
  cinnerRep_vacuumFree_edge_contraction x hx

/-! ## Distinguished vacuum and completed linear operator -/

def stagedVacuum : StagedPacket := ⟨0, vacuumPacket 0⟩

def completedPacketVacuum : GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS stagedVacuum

/-- The completed all-character physical packet transfer, including its
constructive representative lift and exact rational linearity. -/
def completedPacketLinearTransfer :
    LinearTransferOperator packetColimitSmulGNS :=
  packetColimitDiagonalSymbol.toLinearTransfer
    completedPacketVacuum
    completedPacketTransfer_selfAdjoint
    completedPacketTransfer_positive
    completedPacketTransfer_contraction

theorem stagedVacuum_eigen :
    StagedEqv (stagedTransfer stagedVacuum) stagedVacuum := by
  intro s
  cases s with
  | zero =>
      refine Q'.eqv_trans _
        (packetEigen 0 * coeffAt stagedVacuum.packet 0) _
        (coeffAt_packetTransfer stagedVacuum.packet 0) ?_
      rw [packetEigen_zero]
      exact Q'.one_mul_eqv _
  | succ s =>
      have hz : coeffAt stagedVacuum.packet (s + 1) = 0 :=
        by
          change coeffAt (vacuumPacket 0) (s + 1) = 0
          exact coeffAt_of_gt (vacuumPacket 0) (by omega)
      refine Q'.eqv_trans _
        (packetEigen (s + 1) * coeffAt stagedVacuum.packet (s + 1)) _
        (coeffAt_packetTransfer stagedVacuum.packet (s + 1)) ?_
      rw [hz]
      exact Q'.mul_zero_eqv _

theorem completedPacket_vacuum_eigen :
    completedPacketLinearTransfer.toTransferOperator.T completedPacketVacuum =
      completedPacketVacuum := by
  refine Eq.trans (completedPacketTransfer_embed stagedVacuum) ?_
  apply Quotient.sound
  exact embed_null_of_rad packetColimitGNS
    (rad_of_veq packetColimitGNS stagedVacuum_eigen)

theorem stagedSub_zero (A : StagedPacket) :
    StagedEqv (packetColimitGNS.sub A packetColimitGNS.zero) A := by
  have hneg : StagedEqv (stagedNeg stagedZero) stagedZero := by
    intro s
    refine Q'.eqv_trans _ (-(coeffAt stagedZero.packet s)) _
      (coeffAt_stagedNeg stagedZero s) ?_
    refine Q'.eqv_trans _ (-(0 : Q')) _
      (Q'.neg_eqv_congr _ _ (coeffAt_stagedZero s)) ?_
    exact Q'.eqv_trans _ 0 _ (by decide)
      (Q'.eqv_symm (coeffAt_stagedZero s))
  refine stagedEqv_trans (stagedAdd_congr (stagedEqv_refl A) hneg) ?_
  exact stagedEqv_trans (stagedAdd_comm A stagedZero) (stagedZero_add A)

theorem stagedVacuum_gram_one :
    stagedGram stagedVacuum stagedVacuum ≈ (1 : Q') := by
  refine Q'.eqv_trans _
    (packetWilsonGram stagedVacuum.packet stagedVacuum.packet) _
    (stagedGram_self_eq_packet stagedVacuum) ?_
  refine Q'.eqv_trans _
    (fsum (fun s => packetEigen s *
      (coeffAt stagedVacuum.packet s * coeffAt stagedVacuum.packet s)) 1) _
    (packetWilsonGram_diagonal stagedVacuum.packet stagedVacuum.packet) ?_
  decide

theorem stagedVacuum_qmk_ne_zero :
    packetColimitGNS.qmk stagedVacuum ≠
      packetColimitGNS.qmk packetColimitGNS.zero := by
  intro h
  have hr : packetColimitGNS.rad stagedVacuum packetColimitGNS.zero :=
    Quotient.exact h
  have hdiag := packetColimitGNS.B_diag_congr (stagedSub_zero stagedVacuum)
  have hzero : stagedGram stagedVacuum stagedVacuum ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hdiag) hr
  have honezero : (1 : Q') ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm stagedVacuum_gram_one) hzero
  exact (by decide : ¬ ((1 : Q') ≈ 0)) honezero

theorem completedPacket_vacuum_ne_zero :
    completedPacketVacuum ≠ embedV packetColimitGNS packetColimitGNS.zero := by
  intro h
  apply stagedVacuum_qmk_ne_zero
  exact embedQuot_injective packetColimitGNS h

end YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer

#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.stagedSmul_sub
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.packetColimitSmulGNS
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.stagedTransfer_add
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.stagedTransfer_smul
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.packetTransfer_contraction
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.stagedTransfer_distSq_contraction
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.stagedVacuumFree_edge_contraction
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.packetColimitDiagonalSymbol
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.stagedTransfer_selfAdjoint
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.stagedTransfer_positive
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.completedPacketTransfer
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.completedPacketTransfer_selfAdjoint
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.completedPacketTransfer_positive
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.completedPacketTransfer_contraction
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.completedPacketTransfer_vacuumFree_edge_contraction
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.completedPacketLinearTransfer
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.completedPacket_vacuum_eigen
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.stagedVacuum_gram_one
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer.completedPacket_vacuum_ne_zero
