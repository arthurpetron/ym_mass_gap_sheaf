/-
# Finite shared-link fusion networks and the first cyclic obstruction

This module packages the local associative fusion quotient into an exact
finite link-elimination evaluator.  Each link is first fused into its
irreducible character packet; Haar elimination is its diagonal norm.  A list
specifies the link-elimination order, and the network evaluator is the exact
product of those local Haar values.

Two kinds of order independence are proved constructively:

* changing the parenthesization of three incident plaquettes does not change
  a local link value (the checked Clebsch--Gordan associativity map);
* permuting the finite link-elimination list does not change the product.

For a product of already-fused link packets, the local `1/64` squared-norm
bound lifts to the same volume-independent global `1/64` bound whenever every
listed link packet has zero vacuum coefficient.

The smallest multiple-shared-link cycle exposes the next obstruction.  Two
fundamental plaquettes sharing two links give `chi_1^2=chi_0+chi_2` on both
links.  The nominally excited plaquette configuration therefore has global
vacuum coefficient `1`; its unprojected norm cannot satisfy the excited
`1/64` contraction.  This is exact screening, not a numerical failure.

Honest scope: the product evaluator is the result after independent Haar
link eliminations.  A general plaquette superposition correlates the packets
at several links; the checked bigon shows that a plaquette-label excitation
condition does not imply global vacuum orthogonality.  A global construction
must project the fused spin-network vacuum, not merely inspect plaquette
labels.
-/

import YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum

namespace YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2SharedLinkFusionBlock
open YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## A concrete associative three-plaquette link evaluator -/

def tripleIrrepGram (a b : TripleIrrep) : Q' :=
  a.1 * b.1 +
    (a.2.1 * b.2.1 + (a.2.2.1 * b.2.2.1 + a.2.2.2 * b.2.2.2))

private theorem tripleIrrepGram_congr {a b : TripleIrrep}
    (h : TripleIrrepEq a b) :
    tripleIrrepGram a a ≈ tripleIrrepGram b b :=
  QPoly.q_add_congr (q_mul_congr h.1 h.1)
    (QPoly.q_add_congr (q_mul_congr h.2.1 h.2.1)
      (QPoly.q_add_congr (q_mul_congr h.2.2.1 h.2.2.1)
        (q_mul_congr h.2.2.2 h.2.2.2)))

def leftAssociatedLinkValue (a : TripleVec) : Q' :=
  tripleIrrepGram (fuseFirstPairThenThird a) (fuseFirstPairThenThird a)

def rightAssociatedLinkValue (a : TripleVec) : Q' :=
  tripleIrrepGram (fuseLastPairThenFirst a) (fuseLastPairThenFirst a)

theorem local_link_association_independent (a : TripleVec) :
    leftAssociatedLinkValue a ≈ rightAssociatedLinkValue a :=
  tripleIrrepGram_congr (third_gluing_associative a)

/-! ## Explicit finite link elimination and permutation independence -/

def eliminateLinks (linkValue : Nat → Q') : List Nat → Q'
  | [] => 1
  | ℓ :: order => linkValue ℓ * eliminateLinks linkValue order

/-- Link elimination is independent of every finite reordering. -/
theorem eliminateLinks_perm (linkValue : Nat → Q') :
    ∀ {A B : List Nat}, A.Perm B →
      eliminateLinks linkValue A ≈ eliminateLinks linkValue B
  | _, _, List.Perm.nil => Q'.eqv_refl 1
  | _, _, List.Perm.cons _ h =>
      Q'.mul_eqv_congr_left _ _ _ (eliminateLinks_perm linkValue h)
  | _, _, List.Perm.swap a b rest => by
      change linkValue b * (linkValue a * eliminateLinks linkValue rest) ≈
        linkValue a * (linkValue b * eliminateLinks linkValue rest)
      refine Q'.eqv_trans _
        ((linkValue b * linkValue a) * eliminateLinks linkValue rest) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((linkValue a * linkValue b) * eliminateLinks linkValue rest) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
  | _, _, List.Perm.trans h₁ h₂ =>
      Q'.eqv_trans _ _ _ (eliminateLinks_perm linkValue h₁)
        (eliminateLinks_perm linkValue h₂)

def leftFusionNetworkValue (packet : Nat → TripleVec) (order : List Nat) : Q' :=
  eliminateLinks (fun ℓ => leftAssociatedLinkValue (packet ℓ)) order

def rightFusionNetworkValue (packet : Nat → TripleVec) (order : List Nat) : Q' :=
  eliminateLinks (fun ℓ => rightAssociatedLinkValue (packet ℓ)) order

theorem fusionNetwork_association_independent (packet : Nat → TripleVec) :
    ∀ order, leftFusionNetworkValue packet order ≈
      rightFusionNetworkValue packet order
  | [] => Q'.eqv_refl 1
  | ℓ :: rest =>
      q_mul_congr (local_link_association_independent (packet ℓ))
        (fusionNetwork_association_independent packet rest)

/-- Both local fusion parenthesization and global link-elimination order may
be changed simultaneously. -/
theorem fusionNetwork_full_order_independent (packet : Nat → TripleVec)
    {A B : List Nat} (h : A.Perm B) :
    leftFusionNetworkValue packet A ≈ rightFusionNetworkValue packet B :=
  Q'.eqv_trans _ _ _ (fusionNetwork_association_independent packet A)
    (eliminateLinks_perm (fun ℓ => rightAssociatedLinkValue (packet ℓ)) h)

/-! ## Global contraction after linkwise fusion quotient -/

abbrev QuotientNetwork := Nat → Nat → Q'

def networkNorm (packet : QuotientNetwork) (cutoff : Nat → Nat) :
    List Nat → Q'
  | [] => 1
  | ℓ :: rest => modeNorm (packet ℓ) (cutoff ℓ) *
      networkNorm packet cutoff rest

def transferredNetworkNorm (packet : QuotientNetwork) (cutoff : Nat → Nat) :
    List Nat → Q'
  | [] => 1
  | ℓ :: rest => modeNorm (modeTransfer (packet ℓ)) (cutoff ℓ) *
      transferredNetworkNorm packet cutoff rest

private theorem modeNorm_nonneg (f : Nat → Q') (N : Nat) :
    (0 : Q') ≤ modeNorm f N :=
  fsum_nonneg (fun s => YMGap.Constructive.SumOfSquares.q_mul_self_nonneg (f s)) N

private theorem transferredNetworkNorm_nonneg
    (packet : QuotientNetwork) (cutoff : Nat → Nat) : ∀ order,
    (0 : Q') ≤ transferredNetworkNorm packet cutoff order
  | [] => by change (0 : Q') ≤ 1; decide
  | ℓ :: rest => Q'.mul_nonneg _ _
      (modeNorm_nonneg _ _) (transferredNetworkNorm_nonneg packet cutoff rest)

private theorem networkNorm_nonneg
    (packet : QuotientNetwork) (cutoff : Nat → Nat) : ∀ order,
    (0 : Q') ≤ networkNorm packet cutoff order
  | [] => by change (0 : Q') ≤ 1; decide
  | ℓ :: rest => Q'.mul_nonneg _ _
      (modeNorm_nonneg _ _) (networkNorm_nonneg packet cutoff rest)

private theorem local_plain_contraction (f : Nat → Q') (h0 : f 0 ≈ 0)
    (N : Nat) :
    modeNorm (modeTransfer f) N ≤ modeNorm f N := by
  have hu := finite_fused_quotient_uniform_contraction f h0 N
  have hc := Q'.mul_le_mul_of_nonneg_right
    (eighth * eighth) 1 (modeNorm f N) (by decide) (modeNorm_nonneg f N)
  exact Q'.le_trans' _ _ _ hu
    (Q'.le_trans' _ _ _ hc (Q'.le_of_eqv (Q'.one_mul_eqv _)))

private theorem network_plain_contraction
    (packet : QuotientNetwork) (cutoff : Nat → Nat)
    (h0 : ∀ ℓ, packet ℓ 0 ≈ 0) : ∀ order,
    transferredNetworkNorm packet cutoff order ≤ networkNorm packet cutoff order
  | [] => Q'.le_refl' 1
  | ℓ :: rest =>
      Q'.mul_le_mul_of_nonneg
        (local_plain_contraction (packet ℓ) (h0 ℓ) (cutoff ℓ))
        (network_plain_contraction packet cutoff h0 rest)
        (modeNorm_nonneg (packet ℓ) (cutoff ℓ))
        (transferredNetworkNorm_nonneg packet cutoff rest)

/-- **Globally compatible product-network contraction.**  For every nonempty
finite link list, if every fused link packet is vacuum-orthogonal, the whole
network contracts by the SAME `1/64`, independently of the number or order of
links. -/
theorem finite_network_uniform_contraction
    (packet : QuotientNetwork) (cutoff : Nat → Nat)
    (h0 : ∀ ℓ, packet ℓ 0 ≈ 0) (ℓ : Nat) (rest : List Nat) :
    transferredNetworkNorm packet cutoff (ℓ :: rest) ≤
      (eighth * eighth) * networkNorm packet cutoff (ℓ :: rest) := by
  have hhead := finite_fused_quotient_uniform_contraction
    (packet ℓ) (h0 ℓ) (cutoff ℓ)
  have htail := network_plain_contraction packet cutoff h0 rest
  have hm := Q'.mul_le_mul_of_nonneg hhead htail
    ((Q'.mul_nonneg _ _ (by decide) (modeNorm_nonneg (packet ℓ) (cutoff ℓ))))
    (transferredNetworkNorm_nonneg packet cutoff rest)
  exact Q'.le_trans' _ _ _ hm
    (Q'.le_of_eqv (Q'.mul_assoc_eqv (eighth * eighth)
      (modeNorm (packet ℓ) (cutoff ℓ)) (networkNorm packet cutoff rest)))

/-! ## The first cycle/multiple-shared-link obstruction -/

def bigonDoubleLocal : IrrepVec := fusionCollapse doubleMode

/-- Two shared links carrying the same double-fundamental plaquette label. -/
def bigonDoubleNorm : Q' :=
  irrepGram bigonDoubleLocal bigonDoubleLocal *
    irrepGram bigonDoubleLocal bigonDoubleLocal

def bigonDoubleTransferredNorm : Q' :=
  irrepGram (irrepTransfer bigonDoubleLocal) (irrepTransfer bigonDoubleLocal) *
    irrepGram (irrepTransfer bigonDoubleLocal) (irrepTransfer bigonDoubleLocal)

/-- Both shared links contain a vacuum summand, so the global vacuum
coefficient is exactly one. -/
theorem bigonDouble_global_vacuum_screening :
    bigonDoubleLocal.1 * bigonDoubleLocal.1 ≈ 1 := by decide

theorem bigonDouble_norm_exact : bigonDoubleNorm ≈ 4 := by decide

/-- The nominally plaquette-excited bigon does NOT obey the excited `1/64`
bound before the fused global vacuum is projected out. -/
theorem bigon_unprojected_excited_contraction_fails :
    ¬ (bigonDoubleTransferredNorm ≤
      (eighth * eighth) * bigonDoubleNorm) := by
  unfold bigonDoubleTransferredNorm bigonDoubleNorm bigonDoubleLocal
    irrepGram irrepTransfer fusionCollapse doubleMode vacuumCoord
    fundamentalCoord quadraticCoord quadraticEigen physLinkWeight coupling eighth
  decide

end YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork

#print axioms YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork.local_link_association_independent
#print axioms YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork.eliminateLinks_perm
#print axioms YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork.fusionNetwork_full_order_independent
#print axioms YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork.finite_network_uniform_contraction
#print axioms YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork.bigonDouble_global_vacuum_screening
#print axioms YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork.bigon_unprojected_excited_contraction_fails
