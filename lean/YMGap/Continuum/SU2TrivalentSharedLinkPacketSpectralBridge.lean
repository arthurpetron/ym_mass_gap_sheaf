/-
# Trivalent shared-link fusion as an exact finite spectral packet

Three fundamental plaquettes incident on one link carry eight raw tensor
labels, but shared-link Clebsch--Gordan fusion sends them to the four channels
`chi_0,...,chi_3`.  The existing fusion calculation proves that this map is
independent of the two binary parenthesizations and records the multiplicity
two in `chi_1^3 = 2 chi_1 + chi_3`.

This module identifies that genuinely trivalent quotient with the cutoff-three
finite character packet.  Its exact Haar GNS form is a four-coordinate
orthogonal sum, its physical link transfer is the same packet transfer, and
the interacting packet Wilson form is exactly the trivalent GNS form with one
positive transfer inserted.  The existing squared-transfer located spectrum
therefore computes `corr 0` and `corr 1` for an actual eight-coordinate,
three-plaquette shared-link representative.

Honest scope: this closes a single trivalent shared-link compatibility cell.
It does not glue such local quotients consistently around all cycles of a
four-dimensional lattice.
-/

import YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
import YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization

namespace YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization
open YMGap.Continuum.SU2SharedLinkFusionBlock
open YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## Four-channel dense GNS and packet carrier -/

private def unitLine : GNSData := qWeightGNS 1 (by decide)

/-- Exact Haar GNS form on the four fused channels `chi_0,...,chi_3`. -/
abbrev tripleSharedGNS : GNSData :=
  gnsProduct unitLine (gnsProduct unitLine (gnsProduct unitLine unitLine))

theorem tripleSharedGNS_B_eq_gram (a b : TripleIrrep) :
    tripleSharedGNS.B a b ≈ tripleIrrepGram a b := by
  unfold tripleSharedGNS gnsProduct unitLine qWeightGNS tripleIrrepGram
  exact QPoly.q_add_congr (Q'.one_mul_eqv _)
    (QPoly.q_add_congr (Q'.one_mul_eqv _)
      (QPoly.q_add_congr (Q'.one_mul_eqv _) (Q'.one_mul_eqv _)))

/-- The four irreducible channels of a trivalent shared link as the exact
cutoff-three character packet. -/
def tripleIrrepPacket (a : TripleIrrep) : CharacterPacket 3 where
  coeff i :=
    if i.val = 0 then a.1
    else if i.val = 1 then a.2.1
    else if i.val = 2 then a.2.2.1
    else a.2.2.2

theorem tripleIrrepPacket_coeff_zero (a : TripleIrrep) :
    coeffAt (tripleIrrepPacket a) 0 = a.1 := by rfl

theorem tripleIrrepPacket_coeff_one (a : TripleIrrep) :
    coeffAt (tripleIrrepPacket a) 1 = a.2.1 := by rfl

theorem tripleIrrepPacket_coeff_two (a : TripleIrrep) :
    coeffAt (tripleIrrepPacket a) 2 = a.2.2.1 := by rfl

theorem tripleIrrepPacket_coeff_three (a : TripleIrrep) :
    coeffAt (tripleIrrepPacket a) 3 = a.2.2.2 := by rfl

/-- Physical heat-kernel transfer on all four fused channels. -/
def tripleIrrepTransfer (a : TripleIrrep) : TripleIrrep :=
  (packetEigen 0 * a.1,
    (packetEigen 1 * a.2.1,
      (packetEigen 2 * a.2.2.1, packetEigen 3 * a.2.2.2)))

/-- The trivalent shared-link transfer and the packet transfer agree on every
retained channel. -/
theorem tripleIrrepPacket_transfer_intertwines (a : TripleIrrep) :
    PacketEqv (tripleIrrepPacket (tripleIrrepTransfer a))
      (packetTransfer (tripleIrrepPacket a)) := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hi with h0 | h1 | h2 | h3
  · have hi0 : i = (⟨0, by decide⟩ : Fin 4) := Fin.ext h0
    subst i
    exact Q'.eqv_refl _
  · have hi1 : i = (⟨1, by decide⟩ : Fin 4) := Fin.ext h1
    subst i
    exact Q'.eqv_refl _
  · have hi2 : i = (⟨2, by decide⟩ : Fin 4) := Fin.ext h2
    subst i
    exact Q'.eqv_refl _
  · have hi3 : i = (⟨3, by decide⟩ : Fin 4) := Fin.ext h3
    subst i
    exact Q'.eqv_refl _

private theorem coeffAt_of_packetEqv {N : Nat} {P Q : CharacterPacket N}
    (h : PacketEqv P Q) (s : Nat) : coeffAt P s ≈ coeffAt Q s := by
  by_cases hs : s < N + 1
  · rw [coeffAt_of_lt P hs, coeffAt_of_lt Q hs]
    exact h ⟨s, hs⟩
  · unfold coeffAt
    rw [dif_neg hs, dif_neg hs]
    exact Q'.eqv_refl 0

private theorem packetWilsonGram_congr {N : Nat}
    {P P' Q Q2 : CharacterPacket N}
    (hP : PacketEqv P P') (hQ : PacketEqv Q Q2) :
    packetWilsonGram P Q ≈ packetWilsonGram P' Q2 := by
  refine Q'.eqv_trans _ _ _ (packetWilsonGram_diagonal P Q) ?_
  refine Q'.eqv_trans _
    (fsum (fun s => packetEigen s *
      (coeffAt P' s * coeffAt Q2 s)) (N + 1)) _ ?_ ?_
  · exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      Q'.mul_eqv_congr_left (packetEigen s) _ _
        (q_mul_congr (coeffAt_of_packetEqv hP s)
          (coeffAt_of_packetEqv hQ s))) (N + 1)
  · exact Q'.eqv_symm (packetWilsonGram_diagonal P' Q2)

/-! ## Exact same-state identification -/

/-- The interacting packet state is exactly the trivalent shared-link GNS
form with one positive physical transfer inserted. -/
theorem packetWilsonGram_eq_tripleSharedGNS (a b : TripleIrrep) :
    packetWilsonGram (tripleIrrepPacket a) (tripleIrrepPacket b) ≈
      tripleSharedGNS.B (tripleIrrepTransfer a) b := by
  refine Q'.eqv_trans _ _ _
    (packetWilsonGram_diagonal (tripleIrrepPacket a) (tripleIrrepPacket b)) ?_
  refine Q'.eqv_trans _ (tripleIrrepGram (tripleIrrepTransfer a) b) _ ?_ ?_
  · unfold tripleIrrepGram tripleIrrepTransfer
    change
      (((0 + packetEigen 0 * (a.1 * b.1)) +
        packetEigen 1 * (a.2.1 * b.2.1)) +
          packetEigen 2 * (a.2.2.1 * b.2.2.1)) +
            packetEigen 3 * (a.2.2.2 * b.2.2.2) ≈
        (packetEigen 0 * a.1) * b.1 +
          ((packetEigen 1 * a.2.1) * b.2.1 +
            ((packetEigen 2 * a.2.2.1) * b.2.2.1 +
              (packetEigen 3 * a.2.2.2) * b.2.2.2))
    ring_qeqv
  · exact Q'.eqv_symm (tripleSharedGNS_B_eq_gram (tripleIrrepTransfer a) b)

private theorem tripleIrrepTransfer_congr {a b : TripleIrrep}
    (h : TripleIrrepEq a b) :
    TripleIrrepEq (tripleIrrepTransfer a) (tripleIrrepTransfer b) :=
  ⟨Q'.mul_eqv_congr_left (packetEigen 0) _ _ h.1,
    Q'.mul_eqv_congr_left (packetEigen 1) _ _ h.2.1,
    Q'.mul_eqv_congr_left (packetEigen 2) _ _ h.2.2.1,
    Q'.mul_eqv_congr_left (packetEigen 3) _ _ h.2.2.2⟩

private theorem tripleIrrepGram_congr {a a' b b' : TripleIrrep}
    (ha : TripleIrrepEq a a') (hb : TripleIrrepEq b b') :
    tripleIrrepGram a b ≈ tripleIrrepGram a' b' :=
  QPoly.q_add_congr (q_mul_congr ha.1 hb.1)
    (QPoly.q_add_congr (q_mul_congr ha.2.1 hb.2.1)
      (QPoly.q_add_congr (q_mul_congr ha.2.2.1 hb.2.2.1)
        (q_mul_congr ha.2.2.2 hb.2.2.2)))

/-- The same identity for two raw eight-coordinate, three-plaquette
representatives.  Associativity permits either fusion parenthesization. -/
theorem packetWilsonGram_raw_parenthesization_independent (x y : TripleVec) :
    packetWilsonGram (tripleIrrepPacket (fuseFirstPairThenThird x))
        (tripleIrrepPacket (fuseFirstPairThenThird y)) ≈
      tripleSharedGNS.B
        (tripleIrrepTransfer (fuseLastPairThenFirst x))
        (fuseLastPairThenFirst y) := by
  refine Q'.eqv_trans _ _ _
    (packetWilsonGram_eq_tripleSharedGNS
      (fuseFirstPairThenThird x) (fuseFirstPairThenThird y)) ?_
  refine Q'.eqv_trans _
    (tripleIrrepGram
      (tripleIrrepTransfer (fuseFirstPairThenThird x))
      (fuseFirstPairThenThird y)) _
    (tripleSharedGNS_B_eq_gram _ _) ?_
  exact Q'.eqv_trans _
    (tripleIrrepGram
      (tripleIrrepTransfer (fuseLastPairThenFirst x))
      (fuseLastPairThenFirst y)) _
    (tripleIrrepGram_congr
      (tripleIrrepTransfer_congr (third_gluing_associative x))
      (third_gluing_associative y))
    (Q'.eqv_symm (tripleSharedGNS_B_eq_gram _ _))

/-! ## Located squared-transfer spectrum on the trivalent cell -/

/-- A raw trivalent shared-link vector whose fused vacuum channel vanishes. -/
structure TrivalentVacuumFree : Type where
  raw : TripleVec
  vacuum_zero : (fuseFirstPairThenThird raw).1 ≈ 0

def trivalentVacuumFreePacket (x : TrivalentVacuumFree) : VacuumFreePacket 3 where
  packet := tripleIrrepPacket (fuseFirstPairThenThird x.raw)
  vacuum_zero := x.vacuum_zero

/-- The all-excited three-plaquette mode is a nontrivial vacuum-free raw
trivalent vector. -/
def tripleFundamentalVacuumFree : TrivalentVacuumFree where
  raw := tripleFundamentalMode
  vacuum_zero := tripleFundamental_fusion_multiplicity.1

/-- The spectral packet retains the exact fusion multiplicity
`chi_1^3 = 2 chi_1 + chi_3`; it is not a relabelled one-mode packet. -/
theorem tripleFundamental_packet_coefficients :
    coeffAt (trivalentVacuumFreePacket tripleFundamentalVacuumFree).packet 0 ≈ 0 ∧
    coeffAt (trivalentVacuumFreePacket tripleFundamentalVacuumFree).packet 1 ≈ 2 ∧
    coeffAt (trivalentVacuumFreePacket tripleFundamentalVacuumFree).packet 2 ≈ 0 ∧
    coeffAt (trivalentVacuumFreePacket tripleFundamentalVacuumFree).packet 3 ≈ 1 := by
  change (fuseFirstPairThenThird tripleFundamentalMode).1 ≈ 0 ∧
    (fuseFirstPairThenThird tripleFundamentalMode).2.1 ≈ 2 ∧
    (fuseFirstPairThenThird tripleFundamentalMode).2.2.1 ≈ 0 ∧
    (fuseFirstPairThenThird tripleFundamentalMode).2.2.2 ≈ 1
  exact tripleFundamental_fusion_multiplicity

def trivalentSquaredSpectralModel (x : TrivalentVacuumFree) :
    SpectralGap.SpectralModel :=
  packetSquaredSpectralModel (trivalentVacuumFreePacket x)

/-- `corr 0` is the positive GNS form of the actual trivalent shared-link
state, not a disjoint-product proxy. -/
theorem trivalentGNS_eq_squaredCorr_zero (x : TrivalentVacuumFree) :
    tripleSharedGNS.B
        (tripleIrrepTransfer (fuseFirstPairThenThird x.raw))
        (fuseFirstPairThenThird x.raw) ≈
      SpectralGap.corr (trivalentSquaredSpectralModel x) 0 := by
  refine Q'.eqv_trans _
    (packetWilsonGram
      (trivalentVacuumFreePacket x).packet
      (trivalentVacuumFreePacket x).packet) _ ?_ ?_
  · exact Q'.eqv_symm
      (packetWilsonGram_eq_tripleSharedGNS
        (fuseFirstPairThenThird x.raw) (fuseFirstPairThenThird x.raw))
  · exact packetGram_eq_squaredCorr_zero (trivalentVacuumFreePacket x)

/-- `corr 1` is the same trivalent shared-link GNS form after applying the
physical transfer to both packet arguments. -/
theorem trivalentTransferredGNS_eq_squaredCorr_one
    (x : TrivalentVacuumFree) :
    tripleSharedGNS.B
        (tripleIrrepTransfer
          (tripleIrrepTransfer (fuseFirstPairThenThird x.raw)))
        (tripleIrrepTransfer (fuseFirstPairThenThird x.raw)) ≈
      SpectralGap.corr (trivalentSquaredSpectralModel x) 1 := by
  let a := fuseFirstPairThenThird x.raw
  let P := tripleIrrepPacket a
  have hT : PacketEqv (tripleIrrepPacket (tripleIrrepTransfer a))
      (packetTransfer P) := tripleIrrepPacket_transfer_intertwines a
  refine Q'.eqv_trans _
    (packetWilsonGram
      (tripleIrrepPacket (tripleIrrepTransfer a))
      (tripleIrrepPacket (tripleIrrepTransfer a))) _ ?_ ?_
  · exact Q'.eqv_symm
      (packetWilsonGram_eq_tripleSharedGNS
        (tripleIrrepTransfer a) (tripleIrrepTransfer a))
  · refine Q'.eqv_trans _
      (packetWilsonGram (packetTransfer P) (packetTransfer P)) _
      (packetWilsonGram_congr hT hT) ?_
    exact packetTransferredGram_eq_squaredCorr_one
      (trivalentVacuumFreePacket x)

/-- The inherited located separator is exactly `1/64`, uniformly on the
trivalent shared-link cell. -/
theorem trivalent_gapMargin_exact (x : TrivalentVacuumFree) :
    (packetSquaredLocatedGap (trivalentVacuumFreePacket x)).gapMargin ≈
      Q'.mkPos 63 64 (by decide) :=
  packetSquared_gapMargin_exact (trivalentVacuumFreePacket x)

end YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge

#print axioms YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge.tripleSharedGNS_B_eq_gram
#print axioms YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge.tripleIrrepPacket_coeff_zero
#print axioms YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge.tripleIrrepPacket_coeff_one
#print axioms YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge.tripleIrrepPacket_coeff_two
#print axioms YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge.tripleIrrepPacket_coeff_three
#print axioms YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge.tripleIrrepPacket_transfer_intertwines
#print axioms YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge.packetWilsonGram_eq_tripleSharedGNS
#print axioms YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge.packetWilsonGram_raw_parenthesization_independent
#print axioms YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge.tripleFundamental_packet_coefficients
#print axioms YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge.trivalentGNS_eq_squaredCorr_zero
#print axioms YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge.trivalentTransferredGNS_eq_squaredCorr_one
#print axioms YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge.trivalent_gapMargin_exact
