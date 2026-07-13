/-
# Global vacuum projection for gauge-compatible SU(2) cycles

At every bivalent vertex of a closed SU(2) spin network, the two incident
irreducible labels must agree.  Hence a finite cycle is not indexed by an
independent label at every link: its gauge-compatible quotient has one common
label `s`.  For link packets `packet l s`, the quotient coefficient is the
exact product of their common-`s` coefficients.

This file constructs that quotient with an explicit link-elimination order.
The quotient and its transfer are independent of every permutation of the
order.  Transferring before gauge collapse equals transferring the collapsed
common-label packet by the product of the link eigenvalues.

The global vacuum projection removes only the common label `s = 0`.  On every
nonempty cycle the remaining packet contracts in squared Haar norm by at
least `(1/8)^2`, uniformly in the cycle length and channel cutoff.

For the two-link bigon, two double-fundamental packets first fuse locally as
`chi_0 + chi_2`.  The bivalent gauge quotient keeps only the diagonal pairs
`(0,0)` and `(2,2)`; after global vacuum projection the result is exactly the
single quadratic loop mode.  Thus the earlier screened vacuum is removed
without incorrectly retaining the off-diagonal `(0,2)` and `(2,0)` channels.
-/

import YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork

namespace YMGap.Continuum.SU2GlobalVacuumCycleQuotient

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2SharedLinkFusionBlock
open YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    (a * b) ≈ (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem q_mul4_regroup (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

/-! ## Common-label gauge quotient and exact transfer intertwiner -/

abbrev LinkPacket := Nat → Nat → Q'

/-- The bivalent gauge quotient: all links carry the same irrep label `s`. -/
def cycleGaugeCollapse (packet : LinkPacket) (order : List Nat) (s : Nat) : Q' :=
  eliminateLinks (fun l => packet l s) order

/-- Product of the exact heat-kernel eigenvalue over the eliminated links. -/
def cycleEigen (order : List Nat) (s : Nat) : Q' :=
  eliminateLinks (fun _ => eigA coupling s) order

def transferredLinkPacket (packet : LinkPacket) : LinkPacket :=
  fun l s => eigA coupling s * packet l s

def cycleTransfer (order : List Nat) (f : Nat → Q') (s : Nat) : Q' :=
  cycleEigen order s * f s

theorem cycleGaugeCollapse_order_independent (packet : LinkPacket)
    {A B : List Nat} (h : A.Perm B) (s : Nat) :
    cycleGaugeCollapse packet A s ≈ cycleGaugeCollapse packet B s :=
  eliminateLinks_perm (fun l => packet l s) h

theorem cycleEigen_order_independent {A B : List Nat} (h : A.Perm B)
    (s : Nat) : cycleEigen A s ≈ cycleEigen B s :=
  eliminateLinks_perm (fun _ => eigA coupling s) h

theorem cycleTransfer_order_independent (f : Nat → Q')
    {A B : List Nat} (h : A.Perm B) (s : Nat) :
    cycleTransfer A f s ≈ cycleTransfer B f s :=
  Q'.mul_eqv_congr_right _ _ _ (cycleEigen_order_independent h s)

private theorem eliminateLinks_pointwise_product (a b : Nat → Q') :
    ∀ order,
      eliminateLinks (fun l => a l * b l) order ≈
        eliminateLinks a order * eliminateLinks b order
  | [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | l :: rest => by
      change (a l * b l) * eliminateLinks (fun k => a k * b k) rest ≈
        (a l * eliminateLinks a rest) * (b l * eliminateLinks b rest)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (a l * b l) _ _
          (eliminateLinks_pointwise_product a b rest)) ?_
      exact q_mul4_regroup (a l) (b l)
        (eliminateLinks a rest) (eliminateLinks b rest)

/-- Transfer on every link descends exactly to multiplication by the product
of link eigenvalues on the common-label gauge quotient. -/
theorem cycleGaugeCollapse_transfer_intertwiner (packet : LinkPacket)
    (order : List Nat) (s : Nat) :
    cycleGaugeCollapse (transferredLinkPacket packet) order s ≈
      cycleTransfer order (cycleGaugeCollapse packet order) s := by
  unfold cycleGaugeCollapse transferredLinkPacket cycleTransfer cycleEigen
  exact eliminateLinks_pointwise_product
    (fun _ => eigA coupling s) (fun l => packet l s) order

/-! ## Global vacuum projection and uniform cycle contraction -/

/-- Remove the unique gauge-compatible vacuum loop, the common label `0`. -/
def globalVacuumProject (f : Nat → Q') : Nat → Q'
  | 0 => 0
  | s + 1 => f (s + 1)

theorem globalVacuumProject_zero (f : Nat → Q') :
    globalVacuumProject f 0 ≈ 0 := Q'.eqv_refl 0

theorem globalVacuumProject_idempotent (f : Nat → Q') (s : Nat) :
    globalVacuumProject (globalVacuumProject f) s ≈
      globalVacuumProject f s := by
  cases s <;> exact Q'.eqv_refl _

theorem globalVacuumProject_transfer_commutes (order : List Nat)
    (f : Nat → Q') (s : Nat) :
    cycleTransfer order (globalVacuumProject f) s ≈
      globalVacuumProject (cycleTransfer order f) s := by
  cases s with
  | zero =>
      unfold cycleTransfer globalVacuumProject
      exact Q'.mul_zero_eqv _
  | succ s => exact Q'.eqv_refl _

private theorem cycleEigen_nonneg (order : List Nat) (s : Nat) :
    (0 : Q') ≤ cycleEigen order s := by
  induction order with
  | nil => change (0 : Q') ≤ 1; decide
  | cons l rest ih =>
      exact Q'.mul_nonneg _ _ (eigA_nonneg (by decide) s) ih

private theorem cycleEigen_le_one (order : List Nat) (s : Nat) :
    cycleEigen order s ≤ (1 : Q') := by
  induction order with
  | nil => exact Q'.le_refl' 1
  | cons l rest ih =>
      have hm := Q'.mul_le_mul_of_nonneg
        (eigA_le_one (w := coupling) (by decide) (by decide) s) ih
        (by decide : (0 : Q') ≤ 1) (cycleEigen_nonneg rest s)
      exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv 1))

private theorem cycleEigen_excited_le_eighth (l : Nat) (rest : List Nat)
    {s : Nat} (hs : 1 ≤ s) :
    cycleEigen (l :: rest) s ≤ eighth := by
  have hedge : eigA coupling s ≤ eighth :=
    Q'.le_trans' _ _ _
      (gapEdge_dominates (by decide) (by decide) hs)
      (Q'.le_of_eqv (by decide : eigA coupling 1 ≈ eighth))
  have hm := Q'.mul_le_mul_of_nonneg hedge (cycleEigen_le_one rest s)
    (by decide : (0 : Q') ≤ eighth) (cycleEigen_nonneg rest s)
  exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.mul_one_eqv eighth))

private theorem fsum_le_fsum {f g : Nat → Q'}
    (h : ∀ s, f s ≤ g s) : ∀ N, fsum f N ≤ fsum g N
  | 0 => Q'.le_refl' 0
  | N + 1 => Q'.add_le_add (fsum_le_fsum h N) (h N)

private theorem fsum_const_mul (c : Q') (f : Nat → Q') : ∀ N,
    fsum (fun s => c * f s) N ≈ c * fsum f N
  | 0 => Q'.eqv_symm (Q'.mul_zero_eqv c)
  | N + 1 => by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (fsum_const_mul c f N)) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv c (fsum f N) (f N))

private theorem scaled_term_le (a b x : Q')
    (ha : (0 : Q') ≤ a) (hab : a ≤ b) (hb : (0 : Q') ≤ b) :
    (a * x) * (a * x) ≤ (b * b) * (x * x) := by
  have h1 := Q'.mul_le_mul_of_nonneg_right a b a hab ha
  have h2 := Q'.mul_le_mul_of_nonneg_left a b b hab hb
  have hs : a * a ≤ b * b := Q'.le_trans' _ _ _ h1 h2
  have hm := Q'.mul_le_mul_of_nonneg_right
    (a * a) (b * b) (x * x) hs
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg x)
  exact Q'.le_trans' _ ((a * a) * (x * x)) _
    (Q'.le_of_eqv (q_mul4_regroup a x a x)) hm

private theorem projected_cycle_term_uniform (f : Nat → Q')
    (l : Nat) (rest : List Nat) (s : Nat) :
    cycleTransfer (l :: rest) (globalVacuumProject f) s *
        cycleTransfer (l :: rest) (globalVacuumProject f) s ≤
      (eighth * eighth) *
        (globalVacuumProject f s * globalVacuumProject f s) := by
  cases s with
  | zero =>
      have hl : cycleTransfer (l :: rest) (globalVacuumProject f) 0 *
          cycleTransfer (l :: rest) (globalVacuumProject f) 0 ≈ 0 := by
        unfold cycleTransfer globalVacuumProject
        exact Q'.eqv_trans _ _ _
          (q_mul_congr (Q'.mul_zero_eqv _) (Q'.mul_zero_eqv _))
          (Q'.zero_mul_eqv 0)
      have hr : (eighth * eighth) *
          (globalVacuumProject f 0 * globalVacuumProject f 0) ≈ 0 := by
        unfold globalVacuumProject
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (eighth * eighth) _ _
            (Q'.zero_mul_eqv 0))
          (Q'.mul_zero_eqv _)
      exact Q'.le_trans' _ 0 _ (Q'.le_of_eqv hl)
        (Q'.le_of_eqv (Q'.eqv_symm hr))
  | succ s =>
      exact scaled_term_le _ _ _
        (cycleEigen_nonneg (l :: rest) (s + 1))
        (cycleEigen_excited_le_eighth l rest (by omega)) (by decide)

/-- Every nonempty finite bivalent cycle contracts on the globally projected
spin-network quotient by the same squared factor `1/64`, independently of
cycle length, link-elimination order, and channel cutoff. -/
theorem finite_cycle_global_vacuum_contraction (f : Nat → Q')
    (l : Nat) (rest : List Nat) (N : Nat) :
    modeNorm (cycleTransfer (l :: rest) (globalVacuumProject f)) N ≤
      (eighth * eighth) * modeNorm (globalVacuumProject f) N := by
  have hs := fsum_le_fsum
    (projected_cycle_term_uniform f l rest) N
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_of_eqv (fsum_const_mul (eighth * eighth)
      (fun s => globalVacuumProject f s * globalVacuumProject f s) N))

/-! ## Exact two-link bigon audit -/

def irrepCoeff (a : IrrepVec) : Nat → Q'
  | 0 => a.1
  | 1 => a.2.1
  | 2 => a.2.2
  | _ => 0

def bigonLinkPacket : LinkPacket := fun _ => irrepCoeff bigonDoubleLocal
def bigonOrder : List Nat := [0, 1]
def bigonReverseOrder : List Nat := [1, 0]

def bigonGaugePacket : Nat → Q' :=
  cycleGaugeCollapse bigonLinkPacket bigonOrder

def bigonProjectedPacket : Nat → Q' :=
  globalVacuumProject bigonGaugePacket

/-- Gauge collapse keeps precisely the common-label diagonal of
`(chi_0+chi_2) ⊗ (chi_0+chi_2)`. -/
theorem bigon_gauge_packet_exact :
    bigonGaugePacket 0 ≈ 1 ∧
    bigonGaugePacket 1 ≈ 0 ∧
    bigonGaugePacket 2 ≈ 1 := by decide

/-- After the unique global vacuum loop is removed, the bigon is exactly the
quadratic common-label loop. -/
theorem bigon_projected_quotient_exact :
    bigonProjectedPacket 0 ≈ 0 ∧
    bigonProjectedPacket 1 ≈ 0 ∧
    bigonProjectedPacket 2 ≈ 1 := by decide

theorem bigon_projected_norm_exact :
    modeNorm bigonProjectedPacket 3 ≈ 1 := by decide

theorem bigon_elimination_order_compatible (s : Nat) :
    cycleGaugeCollapse bigonLinkPacket bigonOrder s ≈
      cycleGaugeCollapse bigonLinkPacket bigonReverseOrder s := by
  apply cycleGaugeCollapse_order_independent
  exact List.Perm.swap 1 0 []

theorem bigon_transfer_order_compatible (s : Nat) :
    cycleTransfer bigonOrder bigonProjectedPacket s ≈
      cycleTransfer bigonReverseOrder bigonProjectedPacket s := by
  apply cycleTransfer_order_independent
  exact List.Perm.swap 1 0 []

/-- The exact projected bigon satisfies the uniform nonvacuum contraction. -/
theorem bigon_projected_transfer_contraction :
    modeNorm (cycleTransfer bigonOrder bigonProjectedPacket) 3 ≤
      (eighth * eighth) * modeNorm bigonProjectedPacket 3 :=
  finite_cycle_global_vacuum_contraction bigonGaugePacket 0 [1] 3

/-- More sharply, the surviving mode acquires one quadratic eigenvalue from
each of the two links. -/
theorem bigon_projected_transfer_norm_exact :
    modeNorm (cycleTransfer bigonOrder bigonProjectedPacket) 3 ≈
      (quadraticEigen * quadraticEigen) *
        (quadraticEigen * quadraticEigen) := by
  unfold modeNorm cycleTransfer cycleEigen bigonOrder bigonProjectedPacket
    globalVacuumProject bigonGaugePacket cycleGaugeCollapse bigonLinkPacket
    irrepCoeff bigonDoubleLocal eliminateLinks
    fusionCollapse doubleMode vacuumCoord fundamentalCoord quadraticCoord
    quadraticEigen physLinkWeight eigA qpow c4 coupling
  decide

end YMGap.Continuum.SU2GlobalVacuumCycleQuotient

#print axioms YMGap.Continuum.SU2GlobalVacuumCycleQuotient.cycleGaugeCollapse_order_independent
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleQuotient.cycleGaugeCollapse_transfer_intertwiner
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleQuotient.globalVacuumProject_transfer_commutes
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleQuotient.finite_cycle_global_vacuum_contraction
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleQuotient.bigon_projected_quotient_exact
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleQuotient.bigon_elimination_order_compatible
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleQuotient.bigon_projected_transfer_contraction
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleQuotient.bigon_projected_transfer_norm_exact
