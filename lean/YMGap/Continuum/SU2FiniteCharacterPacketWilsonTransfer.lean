/-
# Finite all-character same-state SU(2) Wilson transfer

The completed two-mode Peter--Weyl block has the correct vacuum/fundamental
indexing, but its carrier stops at `chi_1`.  This module extends the same
construction to every finite Chebyshev-character packet.

For a packet coefficient `c_s`, the transfer multiplies by the physical Schur
weight

    lambda_s = w^(s(s+2)),       w = 1/2.

The interacting Gram is not an independent diagonal model: it is the already
proved fusion-Haar pairing of the transferred first packet with the second.
It is also literally the bare-polynomial Haar value after exact packet
synthesis and ordinary polynomial multiplication, and its diagonal weights
are the `coeffW/dim` Peter--Weyl contractions.  Applying the transfer once more
therefore produces the two-link moment from the same coefficient table.

At cutoff one, coefficient projection is an exact Gram/transfer intertwiner
to `SU2PeterWeylWilsonBlockCompleted`, including its constructive GNS
completion.  At every cutoff, all vacuum-free packets obey the same squared
norm contraction `1/64`; this is a finite-packet spectral localization theorem
with no cutoff dependence.

Honest scope: this is the exact one-link character sector and its iterated
same-link kernel.  It does not identify these packets with the full overlapping
four-dimensional plaquette observable algebra; shared-link recoupling remains
the separate finite-network route.

The module obeys the repository's constructive kernel contract.
-/

import YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted
import YMGap.Continuum.SpectralLocalizationCrux
import YMGap.Continuum.CubeRatioBounds

namespace YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialHaarDescent

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

private theorem fsum_le_fsum {f g : Nat → Q'}
    (h : ∀ s, f s ≤ g s) : ∀ N, fsum f N ≤ fsum g N
  | 0 => Q'.le_refl' 0
  | N + 1 => Q'.add_le_add (fsum_le_fsum h N) (h N)

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## The physical all-mode packet transfer -/

/-- The actual vacuum-normalized Peter--Weyl eigenvalue at `w = 1/2`. -/
def packetEigen (s : Nat) : Q' :=
  eigA SU2PeterWeylWilsonBlock.coupling s

theorem packetEigen_eq_phys (s : Nat) :
    packetEigen s =
      PeterWeylRealWeight.physLinkWeight
        SU2PeterWeylWilsonBlock.coupling s := rfl

theorem packetEigen_zero : packetEigen 0 = 1 :=
  eigA_zero SU2PeterWeylWilsonBlock.coupling

theorem packetEigen_one :
    packetEigen 1 ≈ SU2PeterWeylWilsonBlock.eighth := by decide

theorem packetEigen_nonneg (s : Nat) : (0 : Q') ≤ packetEigen s :=
  eigA_nonneg (by decide) s

theorem packetEigen_le_one (s : Nat) : packetEigen s ≤ (1 : Q') :=
  eigA_le_one (by decide) (by decide) s

/-- The fundamental mode is the exact spectral edge for every finite cutoff. -/
theorem packetEigen_excited_le_eighth {s : Nat} (hs : 1 ≤ s) :
    packetEigen s ≤ SU2PeterWeylWilsonBlock.eighth :=
  Q'.le_trans' _ _ _
    (gapEdge_dominates (by decide) (by decide) hs)
    (Q'.le_of_eqv packetEigen_one)

/-- Coefficientwise action of one further copy of the same Wilson link kernel. -/
def packetTransfer {N : Nat} (P : CharacterPacket N) : CharacterPacket N where
  coeff i := packetEigen i.val * P.coeff i

theorem coeffAt_packetTransfer {N : Nat} (P : CharacterPacket N) (s : Nat) :
    coeffAt (packetTransfer P) s ≈ packetEigen s * coeffAt P s := by
  by_cases hs : s < N + 1
  · rw [coeffAt_of_lt (packetTransfer P) hs, coeffAt_of_lt P hs]
    exact Q'.eqv_refl _
  · rw [coeffAt, dif_neg hs, coeffAt, dif_neg hs]
    exact Q'.eqv_symm (Q'.mul_zero_eqv _)

/-- Setoid equality of coefficient-bearing packets. -/
def PacketEqv {N : Nat} (P Q : CharacterPacket N) : Prop :=
  ∀ i, P.coeff i ≈ Q.coeff i

def packetScale {N : Nat} (a : Q') (P : CharacterPacket N) : CharacterPacket N where
  coeff i := a * P.coeff i

/-- Every character basis packet is an exact eigenpacket. -/
theorem packetTransfer_basis_eigen {N : Nat} (i : Fin (N + 1)) :
    PacketEqv (packetTransfer (basisPacket i))
      (packetScale (packetEigen i.val) (basisPacket i)) := by
  intro j
  change packetEigen j.val * (if j.val = i.val then 1 else 0) ≈
    packetEigen i.val * (if j.val = i.val then 1 else 0)
  by_cases h : j.val = i.val
  · rw [if_pos h]
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_of_eq (congrArg packetEigen h))
  · rw [if_neg h]
    exact Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _)
      (Q'.eqv_symm (Q'.mul_zero_eqv _))

/-! ## Interacting Gram from the closed fusion-Haar state -/

/-- The one-link interacting reflection Gram.  The definition uses the closed
fusion packet state itself: first evolve by the physical Wilson coefficient,
then take the exact Clebsch--Gordan vacuum coefficient. -/
def packetWilsonGram {N : Nat} (P Q : CharacterPacket N) : Q' :=
  fusionHaar (packetTransfer P) Q

/-- Exact diagonal Peter--Weyl form at arbitrary cutoff. -/
theorem packetWilsonGram_diagonal {N : Nat} (P Q : CharacterPacket N) :
    packetWilsonGram P Q ≈
      fsum (fun s => packetEigen s * (coeffAt P s * coeffAt Q s)) (N + 1) := by
  refine Q'.eqv_trans _ _ _
    (fusionHaar_eq_diagonal (packetTransfer P) Q) ?_
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (coeffAt_packetTransfer P s))
      (Q'.mul_assoc_eqv (packetEigen s) (coeffAt P s) (coeffAt Q s))) (N + 1)

/-- The same Gram written with the literal Schur-contracted heat-kernel table
`coeffW * (1/dim)`, rather than with its simplified eigenvalue. -/
def packetSchurGram {N : Nat} (P Q : CharacterPacket N) : Q' :=
  fsum (fun s =>
    SU2PeterWeylWilsonBlock.contractedLinkEntry
      SU2PeterWeylWilsonBlock.coupling s s *
        (coeffAt P s * coeffAt Q s)) (N + 1)

theorem packetWilsonGram_eq_schur {N : Nat} (P Q : CharacterPacket N) :
    packetWilsonGram P Q ≈ packetSchurGram P Q := by
  refine Q'.eqv_trans _ _ _ (packetWilsonGram_diagonal P Q) ?_
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
    Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm
        (SU2PeterWeylWilsonBlock.contractedLinkEntry_diag
          SU2PeterWeylWilsonBlock.coupling s))) (N + 1)

/-- The packet Gram is literally the descended bare-polynomial Haar functional
on ordinary polynomial multiplication, after applying the Wilson transfer to
the first packet.  Thus neither the state nor multiplication is a surrogate. -/
theorem barePolynomial_same_state_identification {N : Nat}
    (P Q : CharacterPacket N) :
    bareVacuumHaar
      (pmul (synthesis (packetTransfer P)) (synthesis Q)) ≈
        packetWilsonGram P Q := by
  refine Q'.eqv_trans _
    (bareVacuumHaar (synthesis (fusionPacket (packetTransfer P) Q))) _ ?_ ?_
  · exact bareVacuumHaar_congr
      (peqv_symm (synthesis_fusionPacket_product (packetTransfer P) Q))
  · refine Q'.eqv_trans _
      (vacuumHaar (fusionPacket (packetTransfer P) Q)) _
      (bareVacuumHaar_synthesis_packet
        (fusionPacket (packetTransfer P) Q)) ?_
    exact vacuumHaar_fusionPacket (packetTransfer P) Q

theorem packetWilsonGram_nonneg {N : Nat} (P : CharacterPacket N) :
    (0 : Q') ≤ packetWilsonGram P P := by
  have hs : (0 : Q') ≤
      fsum (fun s => packetEigen s * (coeffAt P s * coeffAt P s)) (N + 1) :=
    fsum_nonneg (fun s => Q'.mul_nonneg _ _ (packetEigen_nonneg s)
      (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg (coeffAt P s))) (N + 1)
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_of_eqv (Q'.eqv_symm (packetWilsonGram_diagonal P P)))

/-! ## Same-state two-link compatibility -/

/-- Two copies of the same physical link coefficient table. -/
def packetTwoLinkMoment {N : Nat} (P Q : CharacterPacket N) : Q' :=
  fsum (fun s => (packetEigen s * packetEigen s) *
    (coeffAt P s * coeffAt Q s)) (N + 1)

/-- Applying the packet transfer in the one-link Gram gives exactly the
two-link moment constructed from the same eigenvalue table. -/
theorem packet_same_state_compression {N : Nat} (P Q : CharacterPacket N) :
    packetWilsonGram (packetTransfer P) Q ≈ packetTwoLinkMoment P Q := by
  refine Q'.eqv_trans _ _ _
    (packetWilsonGram_diagonal (packetTransfer P) Q) ?_
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (packetEigen s) _ _
        (Q'.mul_eqv_congr_right _ _ _ (coeffAt_packetTransfer P s)))
      (by ring_qeqv)) (N + 1)

theorem packetWilsonGram_symmetric {N : Nat} (P Q : CharacterPacket N) :
    packetWilsonGram P Q ≈ packetWilsonGram Q P := by
  refine Q'.eqv_trans _ _ _ (packetWilsonGram_diagonal P Q) ?_
  refine Q'.eqv_trans _
    (fsum (fun s => packetEigen s * (coeffAt Q s * coeffAt P s)) (N + 1)) _
    (CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      Q'.mul_eqv_congr_left (packetEigen s) _ _
        (Q'.mul_comm_eqv (coeffAt P s) (coeffAt Q s))) (N + 1)) ?_
  exact Q'.eqv_symm (packetWilsonGram_diagonal Q P)

theorem packetTransfer_selfAdjoint {N : Nat} (P Q : CharacterPacket N) :
    packetWilsonGram (packetTransfer P) Q ≈
      packetWilsonGram P (packetTransfer Q) := by
  refine Q'.eqv_trans _ _ _ (packet_same_state_compression P Q) ?_
  refine Q'.eqv_trans _
    (fsum (fun s => packetEigen s *
      (coeffAt P s * (packetEigen s * coeffAt Q s))) (N + 1)) _ ?_ ?_
  · exact CubeRatioBounds.fsum_eqv_congr _ _ (fun _ => by ring_qeqv) (N + 1)
  · refine Q'.eqv_trans _
      (fsum (fun s => packetEigen s *
        (coeffAt P s * coeffAt (packetTransfer Q) s)) (N + 1)) _ ?_ ?_
    · exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
        Q'.mul_eqv_congr_left (packetEigen s) _ _
          (Q'.mul_eqv_congr_left (coeffAt P s) _ _
            (Q'.eqv_symm (coeffAt_packetTransfer Q s)))) (N + 1)
    · exact Q'.eqv_symm (packetWilsonGram_diagonal P (packetTransfer Q))

theorem packetTransfer_positive {N : Nat} (P : CharacterPacket N) :
    (0 : Q') ≤ packetWilsonGram (packetTransfer P) P := by
  have hs : (0 : Q') ≤ packetTwoLinkMoment P P :=
    fsum_nonneg (fun s =>
      Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (packetEigen_nonneg s) (packetEigen_nonneg s))
        (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg (coeffAt P s))) (N + 1)
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_of_eqv (Q'.eqv_symm (packet_same_state_compression P P)))

/-! ## Uniform finite-packet spectral localization -/

theorem packetWilsonGram_transfer_diagonal {N : Nat} (P : CharacterPacket N) :
    packetWilsonGram (packetTransfer P) (packetTransfer P) ≈
      fsum (fun s => packetEigen s *
        ((packetEigen s * coeffAt P s) *
          (packetEigen s * coeffAt P s))) (N + 1) := by
  refine Q'.eqv_trans _ _ _
    (packetWilsonGram_diagonal (packetTransfer P) (packetTransfer P)) ?_
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
    Q'.mul_eqv_congr_left (packetEigen s) _ _
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (coeffAt_packetTransfer P s))
        (Q'.mul_eqv_congr_left (packetEigen s * coeffAt P s) _ _
          (coeffAt_packetTransfer P s)))) (N + 1)

private theorem eigen_square_le_eighth_square {s : Nat} (hs : 1 ≤ s) :
    packetEigen s * packetEigen s ≤
      SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth := by
  have h0 := packetEigen_nonneg s
  have he := packetEigen_excited_le_eighth hs
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _ (packetEigen s) he h0
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _
    SU2PeterWeylWilsonBlock.eighth he (by decide)
  exact Q'.le_trans' _ _ _ h1 h2

private theorem vacuumfree_transfer_term_le {N : Nat}
    (P : CharacterPacket N) (h0 : coeffAt P 0 ≈ 0) (s : Nat) :
    packetEigen s *
        ((packetEigen s * coeffAt P s) * (packetEigen s * coeffAt P s)) ≤
      (SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth) *
        (packetEigen s * (coeffAt P s * coeffAt P s)) := by
  cases s with
  | zero =>
      rw [packetEigen_zero]
      have hc : coeffAt P 0 * coeffAt P 0 ≈ 0 :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv _)
      have hl : (1 : Q') * ((1 * coeffAt P 0) * (1 * coeffAt P 0)) ≈ 0 := by
        have he :
            (1 : Q') * ((1 * coeffAt P 0) * (1 * coeffAt P 0)) ≈
              coeffAt P 0 * coeffAt P 0 :=
          Q'.eqv_trans _ _ _
            (Q'.one_mul_eqv ((1 : Q') * coeffAt P 0 * (1 * coeffAt P 0)))
            (q_mul_congr (Q'.one_mul_eqv _) (Q'.one_mul_eqv _))
        exact Q'.eqv_trans _ _ _ he hc
      have hr :
          (SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth) *
            ((1 : Q') * (coeffAt P 0 * coeffAt P 0)) ≈ 0 := by
        have he :
            (SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth) *
                ((1 : Q') * (coeffAt P 0 * coeffAt P 0)) ≈
              (SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth) *
                (coeffAt P 0 * coeffAt P 0) :=
          Q'.mul_eqv_congr_left
            (SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth)
            _ _ (Q'.one_mul_eqv _)
        refine Q'.eqv_trans _
          ((SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth) *
            (coeffAt P 0 * coeffAt P 0)) _ he ?_
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            (SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth)
            _ _ hc) (Q'.mul_zero_eqv _)
      exact Q'.le_trans' _ 0 _ (Q'.le_of_eqv hl)
        (Q'.le_of_eqv (Q'.eqv_symm hr))
  | succ k =>
      let lam := packetEigen (k + 1)
      let c := coeffAt P (k + 1)
      have hlam0 : (0 : Q') ≤ lam := packetEigen_nonneg (k + 1)
      have hc0 : (0 : Q') ≤ c * c :=
        YMGap.Constructive.SumOfSquares.q_mul_self_nonneg c
      have hbase0 : (0 : Q') ≤ lam * (c * c) :=
        Q'.mul_nonneg _ _ hlam0 hc0
      have hsq := eigen_square_le_eighth_square (s := k + 1) (by omega)
      have hm := Q'.mul_le_mul_of_nonneg_right _ _
        (lam * (c * c)) hsq hbase0
      dsimp [lam, c] at hm ⊢
      have heL :
          packetEigen (k + 1) *
              ((packetEigen (k + 1) * coeffAt P (k + 1)) *
                (packetEigen (k + 1) * coeffAt P (k + 1))) ≈
            ((packetEigen (k + 1) * packetEigen (k + 1)) *
              (packetEigen (k + 1) *
                (coeffAt P (k + 1) * coeffAt P (k + 1)))) := by ring_qeqv
      have heR :
          (SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth) *
              (packetEigen (k + 1) *
                (coeffAt P (k + 1) * coeffAt P (k + 1))) ≈
            (SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth) *
              (packetEigen (k + 1) *
                (coeffAt P (k + 1) * coeffAt P (k + 1))) := Q'.eqv_refl _
      exact Q'.le_trans' _
        ((packetEigen (k + 1) * packetEigen (k + 1)) *
          (packetEigen (k + 1) *
            (coeffAt P (k + 1) * coeffAt P (k + 1)))) _
        (Q'.le_of_eqv heL)
        (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv heR))

/-- **Uniform packet spectral localization.**  At every cutoff, a packet with
zero vacuum coefficient contracts in the interacting Wilson Gram by the exact
cutoff-independent squared edge factor `(1/8)^2 = 1/64`. -/
theorem vacuumfree_packet_uniform_contraction {N : Nat}
    (P : CharacterPacket N) (h0 : coeffAt P 0 ≈ 0) :
    packetWilsonGram (packetTransfer P) (packetTransfer P) ≤
      (SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth) *
        packetWilsonGram P P := by
  have hsum := fsum_le_fsum (vacuumfree_transfer_term_le P h0) (N + 1)
  refine Q'.le_trans' _ _ _
    (le_of_eqv_le (packetWilsonGram_transfer_diagonal P) hsum) ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _
    ((SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth) *
      fsum (fun s => packetEigen s * (coeffAt P s * coeffAt P s)) (N + 1)) _
    (Q'.eqv_symm (CubeRatioBounds.fsum_const_mul _ _ _)) ?_
  exact Q'.mul_eqv_congr_left
    (SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth) _ _
    (Q'.eqv_symm (packetWilsonGram_diagonal P P))

/-! ## Exact cutoff-one connector to the corrected completed carrier -/

def cutoffZero : Fin 2 := ⟨0, by decide⟩
def cutoffOne : Fin 2 := ⟨1, by decide⟩

def toCorrectedMode (P : CharacterPacket 1) :
    SU2PeterWeylWilsonBlock.ModeVec :=
  (P.coeff cutoffZero, P.coeff cutoffOne)

theorem toCorrectedMode_transfer (P : CharacterPacket 1) :
    SU2PeterWeylWilsonBlock.modeEqv
      (toCorrectedMode (packetTransfer P))
      (SU2PeterWeylWilsonBlock.sameStateTransfer (toCorrectedMode P)) := by
  constructor
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (packetEigen 0) _ _ (Q'.eqv_refl _)) (by
        rw [packetEigen_zero]
        exact Q'.one_mul_eqv _)
  · exact Q'.mul_eqv_congr_right _ _ _ packetEigen_one

theorem cutoffOne_packetWilsonGram (P Q : CharacterPacket 1) :
    packetWilsonGram P Q ≈
      SU2PeterWeylWilsonBlock.wilsonModeGNS.B
        (toCorrectedMode P) (toCorrectedMode Q) := by
  refine Q'.eqv_trans _ _ _ (packetWilsonGram_diagonal P Q) ?_
  have hsum :
      fsum (fun s => packetEigen s * (coeffAt P s * coeffAt Q s)) 2 ≈
        P.coeff cutoffZero * Q.coeff cutoffZero +
          SU2PeterWeylWilsonBlock.eighth *
            (P.coeff cutoffOne * Q.coeff cutoffOne) := by
    change
      (0 + packetEigen 0 *
          (P.coeff cutoffZero * Q.coeff cutoffZero)) +
        packetEigen 1 * (P.coeff cutoffOne * Q.coeff cutoffOne) ≈
      P.coeff cutoffZero * Q.coeff cutoffZero +
        SU2PeterWeylWilsonBlock.eighth *
          (P.coeff cutoffOne * Q.coeff cutoffOne)
    rw [packetEigen_zero]
    have hfirst :
        0 + (1 : Q') * (P.coeff cutoffZero * Q.coeff cutoffZero) ≈
          P.coeff cutoffZero * Q.coeff cutoffZero :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left 0 _ _ (Q'.one_mul_eqv _))
        (QPoly.q_zero_add_eqv _)
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hfirst)
      (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _ packetEigen_one))
  refine Q'.eqv_trans _
    (P.coeff cutoffZero * Q.coeff cutoffZero +
      SU2PeterWeylWilsonBlock.eighth *
        (P.coeff cutoffOne * Q.coeff cutoffOne)) _ hsum ?_
  exact Q'.eqv_symm
    (SU2PeterWeylWilsonBlock.reflectedWilsonGram_diagonal
      (toCorrectedMode P) (toCorrectedMode Q))

theorem toCorrectedMode_vacuum :
    toCorrectedMode (vacuumPacket 1) = SU2PeterWeylWilsonBlock.vacuumMode := by
  decide

theorem toCorrectedMode_fundamental :
    toCorrectedMode
      (basisPacket cutoffOne) =
        SU2PeterWeylWilsonBlock.fundamentalMode := by
  decide

/-- The finite packet transfer commutes exactly with the completed, correctly
indexed Wilson block transfer on the dense cutoff-one image. -/
theorem cutoffOne_completed_transfer_intertwiner (P : CharacterPacket 1) :
    SU2PeterWeylWilsonBlockCompleted.completedSameStateTransfer
        (embedV SU2PeterWeylWilsonBlock.wilsonModeGNS (toCorrectedMode P)) =
      embedV SU2PeterWeylWilsonBlock.wilsonModeGNS
        (toCorrectedMode (packetTransfer P)) := by
  refine Eq.trans
    (SU2PeterWeylWilsonBlockCompleted.completedSameStateTransfer_embed
      (toCorrectedMode P)) ?_
  apply Quotient.sound
  exact embed_null_of_rad SU2PeterWeylWilsonBlock.wilsonModeGNS
    (rad_of_veq SU2PeterWeylWilsonBlock.wilsonModeGNS
      (SU2PeterWeylWilsonBlock.wilsonModeGNS.veq_symm
        (toCorrectedMode_transfer P)))

end YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer

#print axioms YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer.packetTransfer_basis_eigen
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer.packetWilsonGram_diagonal
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer.packetWilsonGram_eq_schur
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer.barePolynomial_same_state_identification
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer.packetWilsonGram_nonneg
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer.packet_same_state_compression
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer.packetTransfer_selfAdjoint
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer.packetTransfer_positive
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer.vacuumfree_packet_uniform_contraction
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer.cutoffOne_packetWilsonGram
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer.cutoffOne_completed_transfer_intertwiner
