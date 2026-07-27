/-
# A multiplicative dimension-weighted mass for finite SU(2) character packets

The dimension-weighted heat tail becomes useful for nonlinear products because
evaluation of a character packet at the group identity is exactly

  ||P||_dim = sum_s (s+1) P_s.

Exact Clebsch--Gordan synthesis therefore makes this mass multiplicative:

  ||P fusion Q||_dim = ||P||_dim ||Q||_dim.

This file proves that statement for the repository's actual `CharacterPacket`
and `fusionPacket`, proves compatibility with directed zero-padding, and builds
an explicit fivefold packet whose mass is the fifth scalar power.  Positivity
is retained coefficientwise throughout.

This is the algebraic bridge required to lift the spacing-dependent heat tail
through the nonlinear five-holonomy carrier.

# Axiom gate

All witnesses are finite `Type`-level packets.  No classical choice,
`native_decide`, `sorry`, or custom axiom.
-/

import YMGap.Continuum.SU2DimensionWeightedHeatTail
import YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt
import YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility
import YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
import YMGap.Continuum.HeatKernelNodeQuad

namespace YMGap.Continuum.SU2FusionWeightedMass

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility
open YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt
open YMGap.Continuum.SU2DimensionWeightedHeatTail

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem finSum_eqv_congr_lt
    (f g : Nat → Q') :
    ∀ n, (∀ i, i < n → f i ≈ g i) →
      finSum f n ≈ finSum g n
  | 0, _ => Q'.eqv_refl 0
  | n + 1, h => by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (finSum_eqv_congr_lt f g n
            (fun i hi =>
              h i (Nat.lt_trans hi (Nat.lt_succ_self n))))) ?_
      exact Q'.add_eqv_congr_left _ _ _
        (h n (Nat.lt_succ_self n))

/-! ## 1. The packet mass and positivity -/

/-- Dimension-weighted coefficient mass.  For nonnegative packets this is the
natural character sup-norm at the identity. -/
def packetWeightedMass {N : Nat} (P : CharacterPacket N) : Q' :=
  finSum
    (fun s => coeffAt P s * representationDimension s)
    (N + 1)

/-- Coefficientwise nonnegativity on the zero-extended packet. -/
def PacketNonnegative {N : Nat} (P : CharacterPacket N) : Prop :=
  ∀ s, (0 : Q') ≤ coeffAt P s

theorem packetWeightedMass_nonneg {N : Nat} {P : CharacterPacket N}
    (hP : PacketNonnegative P) :
    (0 : Q') ≤ packetWeightedMass P :=
  SU2HeatChannelHilbertSchmidtCompletion.finSum_nonneg_local _
    (fun s =>
      Q'.mul_nonneg _ _ (hP s)
        (representationDimension_nonneg s))
    (N + 1)

theorem heatPacket_nonnegative
    {q : Q'} (hq0 : (0 : Q') ≤ q) (N : Nat) :
    PacketNonnegative (heatPacket q N) := by
  intro s
  by_cases hs : s < N + 1
  · rw [coeffAt_of_lt (heatPacket q N) hs]
    exact TruncationTailChannelBound.chanCoeff_nonneg hq0 s
  · have hNs : N < s := by omega
    rw [coeffAt_of_gt (heatPacket q N) hNs]
    decide

theorem padPacket_nonnegative
    {N M : Nat} (hNM : N ≤ M) {P : CharacterPacket N}
    (hP : PacketNonnegative P) :
    PacketNonnegative (padPacket hNM P) := by
  intro s
  rw [coeffAt_padPacket]
  exact hP s

theorem fusionPacket_nonnegative
    {N : Nat} {P Q : CharacterPacket N}
    (hP : PacketNonnegative P) (hQ : PacketNonnegative Q) :
    PacketNonnegative (fusionPacket P Q) := by
  intro s
  by_cases hs : s < 2 * N + 1
  · rw [coeffAt_of_lt (fusionPacket P Q) hs]
    exact fusionProduct_nonneg N hP hQ s
  · have hNs : 2 * N < s := by omega
    rw [coeffAt_of_gt (fusionPacket P Q) hNs]
    decide

/-! ## 2. Evaluation at the identity and multiplicativity -/

/-- The dimension-weighted mass is exactly synthesis evaluated at the group
identity (`U_s(1)=s+1`). -/
theorem eval_synthesis_one_eq_weightedMass
    {N : Nat} (P : CharacterPacket N) :
    eval (synthesis P) 1 ≈ packetWeightedMass P := by
  refine Q'.eqv_trans _ _ _
    (eval_synthesis P 1) ?_
  exact RationalTail.finSum_eqv_congr _ _
    (fun s =>
      Q'.mul_eqv_congr_left (coeffAt P s)
        (Cheb.U s 1) (representationDimension s)
        (HeatKernelNodeQuad.U_at_one s))
    (N + 1)

/-- Directed zero-padding preserves the dimension-weighted mass exactly. -/
theorem packetWeightedMass_pad
    {N M : Nat} (hNM : N ≤ M) (P : CharacterPacket N) :
    packetWeightedMass (padPacket hNM P) ≈ packetWeightedMass P := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (eval_synthesis_one_eq_weightedMass (padPacket hNM P))) ?_
  refine Q'.eqv_trans _ _ _
    (synthesis_padPacket hNM P 1) ?_
  exact eval_synthesis_one_eq_weightedMass P

/-- **Clebsch--Gordan multiplicativity of the weighted mass.** -/
theorem packetWeightedMass_fusion
    {N : Nat} (P Q : CharacterPacket N) :
    packetWeightedMass (fusionPacket P Q)
      ≈ packetWeightedMass P * packetWeightedMass Q := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (eval_synthesis_one_eq_weightedMass (fusionPacket P Q))) ?_
  refine Q'.eqv_trans _ _ _
    (synthesis_fusionPacket_product P Q 1) ?_
  refine Q'.eqv_trans _ _ _
    (eval_pmul (synthesis P) (synthesis Q) 1) ?_
  exact q_mul_congr
    (eval_synthesis_one_eq_weightedMass P)
    (eval_synthesis_one_eq_weightedMass Q)

/-- The heat packet mass is the corresponding weighted coefficient partial
sum. -/
theorem heatPacket_weightedMass_eq_partial
    (q : Q') (N : Nat) :
    packetWeightedMass (heatPacket q N)
      ≈ finSum (weightedChanCoeff q) (N + 1) := by
  apply finSum_eqv_congr_lt
  intro s hs
  rw [coeffAt_of_lt (heatPacket q N) hs]
  exact Q'.mul_comm_eqv
    (TruncationTailChannelBound.chanCoeff q s)
    (representationDimension s)

/-- The explicit spacing-dependent ceiling bounds every finite heat-packet
weighted mass. -/
theorem heatPacket_weightedMass_le_explicitCeiling
    {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < 1)
    (N : Nat) :
    packetWeightedMass (heatPacket q N)
      ≤ weightedOnePlaquetteCeiling q
          (explicitWeightedLabelCutoff q) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (heatPacket_weightedMass_eq_partial q N))
    (weightedAllLabelPartial_le_explicitCeiling hq0 hq1 (N + 1))

/-! ## 3. The same-carrier fivefold packet -/

def fusionPacketTwo {N : Nat} (P : CharacterPacket N) :
    CharacterPacket (2 * N) :=
  fusionPacket P P

def fusionPacketThree {N : Nat} (P : CharacterPacket N) :
    CharacterPacket (2 * (2 * N)) :=
  fusionPacket (fusionPacketTwo P)
    (padPacket (by omega : N ≤ 2 * N) P)

def fusionPacketFour {N : Nat} (P : CharacterPacket N) :
    CharacterPacket (2 * (2 * (2 * N))) :=
  fusionPacket (fusionPacketThree P)
    (padPacket (by omega : N ≤ 2 * (2 * N)) P)

/-- Five successive copies of one packet on the actual Clebsch--Gordan
carrier.  Cutoff growth is explicit: `N -> 2N -> 4N -> 8N -> 16N`. -/
def fusionPacketFive {N : Nat} (P : CharacterPacket N) :
    CharacterPacket (2 * (2 * (2 * (2 * N)))) :=
  fusionPacket (fusionPacketFour P)
    (padPacket (by omega : N ≤ 2 * (2 * (2 * N))) P)

/-- Left-associated fifth scalar product, matching the packet construction. -/
def scalarPowerFive (x : Q') : Q' :=
  (((x * x) * x) * x) * x

theorem fusionPacketTwo_nonnegative
    {N : Nat} {P : CharacterPacket N}
    (hP : PacketNonnegative P) :
    PacketNonnegative (fusionPacketTwo P) :=
  fusionPacket_nonnegative hP hP

theorem fusionPacketThree_nonnegative
    {N : Nat} {P : CharacterPacket N}
    (hP : PacketNonnegative P) :
    PacketNonnegative (fusionPacketThree P) :=
  fusionPacket_nonnegative
    (fusionPacketTwo_nonnegative hP)
    (padPacket_nonnegative (by omega) hP)

theorem fusionPacketFour_nonnegative
    {N : Nat} {P : CharacterPacket N}
    (hP : PacketNonnegative P) :
    PacketNonnegative (fusionPacketFour P) :=
  fusionPacket_nonnegative
    (fusionPacketThree_nonnegative hP)
    (padPacket_nonnegative
      (by omega : N ≤ 2 * (2 * N)) hP)

theorem fusionPacketFive_nonnegative
    {N : Nat} {P : CharacterPacket N}
    (hP : PacketNonnegative P) :
    PacketNonnegative (fusionPacketFive P) :=
  fusionPacket_nonnegative
    (fusionPacketFour_nonnegative hP)
    (padPacket_nonnegative
      (by omega : N ≤ 2 * (2 * (2 * N))) hP)

theorem fusionPacketTwo_weightedMass
    {N : Nat} (P : CharacterPacket N) :
    packetWeightedMass (fusionPacketTwo P)
      ≈ packetWeightedMass P * packetWeightedMass P :=
  packetWeightedMass_fusion P P

theorem fusionPacketThree_weightedMass
    {N : Nat} (P : CharacterPacket N) :
    packetWeightedMass (fusionPacketThree P)
      ≈ (packetWeightedMass P * packetWeightedMass P) *
          packetWeightedMass P := by
  refine Q'.eqv_trans _ _ _
    (packetWeightedMass_fusion
      (fusionPacketTwo P)
      (padPacket (by omega : N ≤ 2 * N) P)) ?_
  exact q_mul_congr
    (fusionPacketTwo_weightedMass P)
    (packetWeightedMass_pad (by omega : N ≤ 2 * N) P)

theorem fusionPacketFour_weightedMass
    {N : Nat} (P : CharacterPacket N) :
    packetWeightedMass (fusionPacketFour P)
      ≈ ((packetWeightedMass P * packetWeightedMass P) *
          packetWeightedMass P) * packetWeightedMass P := by
  refine Q'.eqv_trans _ _ _
    (packetWeightedMass_fusion
      (fusionPacketThree P)
      (padPacket (by omega : N ≤ 2 * (2 * N)) P)) ?_
  exact q_mul_congr
    (fusionPacketThree_weightedMass P)
    (packetWeightedMass_pad
      (by omega : N ≤ 2 * (2 * N)) P)

/-- **The weighted mass of the genuine fivefold carrier is the fifth scalar
power.** -/
theorem fusionPacketFive_weightedMass
    {N : Nat} (P : CharacterPacket N) :
    packetWeightedMass (fusionPacketFive P)
      ≈ scalarPowerFive (packetWeightedMass P) := by
  refine Q'.eqv_trans _ _ _
    (packetWeightedMass_fusion
      (fusionPacketFour P)
      (padPacket (by omega : N ≤ 2 * (2 * (2 * N))) P)) ?_
  exact q_mul_congr
    (fusionPacketFour_weightedMass P)
    (packetWeightedMass_pad
      (by omega : N ≤ 2 * (2 * (2 * N))) P)

end YMGap.Continuum.SU2FusionWeightedMass

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SU2FusionWeightedMass.packetWeightedMass_fusion
#print axioms YMGap.Continuum.SU2FusionWeightedMass.heatPacket_weightedMass_le_explicitCeiling
#print axioms YMGap.Continuum.SU2FusionWeightedMass.fusionPacketFive_weightedMass
