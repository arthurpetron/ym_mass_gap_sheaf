/-
# Nonlinear same-carrier five-fusion tail

This module lifts the dimension-weighted heat tail through the actual
Clebsch--Gordan fivefold carrier.  It deliberately works on one common padded
carrier when comparing two cutoffs; this is the same-carrier comparison that
the independent five-label tensor shortcut cannot provide.

The first layer proves:

* exact synthesis of `fusionPacketFive P` as `(synthesis P)^5`;
* coefficientwise monotonicity of the fivefold packet;
* compatibility of the fivefold packet with every directed padding map;
* identification of its Haar square with the existing canonical nonlinear
  fifth-power Haar square.

The second layer supplies a quantitative weighted-L1-to-Haar-L2 stability
estimate and combines it with the geometric heat tail.

# Axiom gate

Finite `Nat`/`Q'` packet algebra only.  No `Classical.*`, `native_decide`,
`sorry`, custom axiom, or noncomputable witness.
-/

import YMGap.Continuum.SU2FusionWeightedMass
import YMGap.Continuum.FusionPositivity
import YMGap.Continuum.BondMovingMoment
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2NonlinearFiveFusionTail

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionPositivity
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialPacketDescent
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge
open YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility
open YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt
open YMGap.Continuum.SU2DimensionWeightedHeatTail
open YMGap.Continuum.SU2FusionWeightedMass

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem packetEqv_trans_local
    {N : Nat} {P Q R : CharacterPacket N}
    (hPQ : PacketEqv P Q) (hQR : PacketEqv Q R) :
    PacketEqv P R :=
  fun i => Q'.eqv_trans _ _ _ (hPQ i) (hQR i)

/-! ## 1. Exact same-carrier fifth-power synthesis -/

theorem fivePointwiseProduct_congr {p q : Poly}
    (hpq : PolyEqv p q) :
    PolyEqv (fivePointwiseProduct p) (fivePointwiseProduct q) := by
  unfold fivePointwiseProduct
  exact pmul_congr
    (pmul_congr
      (pmul_congr
        (pmul_congr hpq hpq) hpq) hpq) hpq

theorem fusionPacketTwo_synthesis
    {N : Nat} (P : CharacterPacket N) :
    PolyEqv (synthesis (fusionPacketTwo P))
      (pmul (synthesis P) (synthesis P)) :=
  synthesis_fusionPacket_product P P

theorem fusionPacketThree_synthesis
    {N : Nat} (P : CharacterPacket N) :
    PolyEqv (synthesis (fusionPacketThree P))
      (pmul (pmul (synthesis P) (synthesis P))
        (synthesis P)) := by
  refine peqv_trans
    (synthesis_fusionPacket_product
      (fusionPacketTwo P)
      (padPacket (by omega : N ≤ 2 * N) P)) ?_
  exact pmul_congr
    (fusionPacketTwo_synthesis P)
    (synthesis_padPacket (by omega : N ≤ 2 * N) P)

theorem fusionPacketFour_synthesis
    {N : Nat} (P : CharacterPacket N) :
    PolyEqv (synthesis (fusionPacketFour P))
      (pmul
        (pmul (pmul (synthesis P) (synthesis P))
          (synthesis P))
        (synthesis P)) := by
  refine peqv_trans
    (synthesis_fusionPacket_product
      (fusionPacketThree P)
      (padPacket (by omega : N ≤ 2 * (2 * N)) P)) ?_
  exact pmul_congr
    (fusionPacketThree_synthesis P)
    (synthesis_padPacket (by omega : N ≤ 2 * (2 * N)) P)

/-- **The genuine fivefold packet synthesizes to the pointwise fifth
power.** -/
theorem fusionPacketFive_synthesis
    {N : Nat} (P : CharacterPacket N) :
    PolyEqv (synthesis (fusionPacketFive P))
      (fivePointwiseProduct (synthesis P)) := by
  refine peqv_trans
    (synthesis_fusionPacket_product
      (fusionPacketFour P)
      (padPacket
        (by omega : N ≤ 2 * (2 * (2 * N))) P)) ?_
  exact pmul_congr
    (fusionPacketFour_synthesis P)
    (synthesis_padPacket
      (by omega : N ≤ 2 * (2 * (2 * N))) P)

/-! ## 2. Coefficient order and directed compatibility -/

def PacketLe {N : Nat} (P Q : CharacterPacket N) : Prop :=
  ∀ s, coeffAt P s ≤ coeffAt Q s

theorem PacketLe_refl {N : Nat} (P : CharacterPacket N) :
    PacketLe P P :=
  fun _ => Q'.le_refl' _

theorem PacketLe_trans
    {N : Nat} {P Q R : CharacterPacket N}
    (hPQ : PacketLe P Q) (hQR : PacketLe Q R) :
    PacketLe P R :=
  fun s => Q'.le_trans' _ _ _ (hPQ s) (hQR s)

theorem padPacket_le
    {N M : Nat} (hNM : N ≤ M)
    {P Q : CharacterPacket N} (hPQ : PacketLe P Q) :
    PacketLe (padPacket hNM P) (padPacket hNM Q) := by
  intro s
  rw [coeffAt_padPacket, coeffAt_padPacket]
  exact hPQ s

theorem fusionPacket_le
    {N : Nat} {P P' Q Q2 : CharacterPacket N}
    (hP' : PacketNonnegative P')
    (hQ : PacketNonnegative Q)
    (hPP' : PacketLe P P') (hQQ2 : PacketLe Q Q2) :
    PacketLe (fusionPacket P Q) (fusionPacket P' Q2) := by
  intro s
  by_cases hs : s < 2 * N + 1
  · rw [coeffAt_of_lt (fusionPacket P Q) hs,
      coeffAt_of_lt (fusionPacket P' Q2) hs]
    exact fusionProduct_mono N hP' hQ hPP' hQQ2 s
  · have hNs : 2 * N < s := by omega
    rw [coeffAt_of_gt (fusionPacket P Q) hNs,
      coeffAt_of_gt (fusionPacket P' Q2) hNs]
    exact Q'.le_refl' 0

theorem fusionPacketTwo_le
    {N : Nat} {P Q : CharacterPacket N}
    (hP : PacketNonnegative P) (hQ : PacketNonnegative Q)
    (hPQ : PacketLe P Q) :
    PacketLe (fusionPacketTwo P) (fusionPacketTwo Q) :=
  fusionPacket_le hQ hP hPQ hPQ

theorem fusionPacketThree_le
    {N : Nat} {P Q : CharacterPacket N}
    (hP : PacketNonnegative P) (hQ : PacketNonnegative Q)
    (hPQ : PacketLe P Q) :
    PacketLe (fusionPacketThree P) (fusionPacketThree Q) :=
  fusionPacket_le
    (fusionPacketTwo_nonnegative hQ)
    (padPacket_nonnegative (by omega) hP)
    (fusionPacketTwo_le hP hQ hPQ)
    (padPacket_le (by omega) hPQ)

theorem fusionPacketFour_le
    {N : Nat} {P Q : CharacterPacket N}
    (hP : PacketNonnegative P) (hQ : PacketNonnegative Q)
    (hPQ : PacketLe P Q) :
    PacketLe (fusionPacketFour P) (fusionPacketFour Q) :=
  fusionPacket_le
    (fusionPacketThree_nonnegative hQ)
    (padPacket_nonnegative (by omega) hP)
    (fusionPacketThree_le hP hQ hPQ)
    (padPacket_le (by omega) hPQ)

theorem fusionPacketFive_le
    {N : Nat} {P Q : CharacterPacket N}
    (hP : PacketNonnegative P) (hQ : PacketNonnegative Q)
    (hPQ : PacketLe P Q) :
    PacketLe (fusionPacketFive P) (fusionPacketFive Q) :=
  fusionPacket_le
    (fusionPacketFour_nonnegative hQ)
    (padPacket_nonnegative (by omega) hP)
    (fusionPacketFour_le hP hQ hPQ)
    (padPacket_le (by omega) hPQ)

/-- Output cutoff of the explicit fivefold packet. -/
def fiveCarrierCutoff (N : Nat) : Nat :=
  2 * (2 * (2 * (2 * N)))

theorem fiveCarrierCutoff_mono
    {N M : Nat} (hNM : N ≤ M) :
    fiveCarrierCutoff N ≤ fiveCarrierCutoff M := by
  unfold fiveCarrierCutoff
  omega

/-- **The same-carrier fivefold packet commutes with every directed padding
map.**  The proof uses exact synthesis plus character faithfulness, avoiding
any reassociation assumption. -/
theorem fusionPacketFive_pad
    {N M : Nat} (hNM : N ≤ M) (P : CharacterPacket N) :
    PacketEqv
      (fusionPacketFive (padPacket hNM P))
      (padPacket (fiveCarrierCutoff_mono hNM)
        (fusionPacketFive P)) := by
  apply packetEqv_of_synthesis
  refine peqv_trans
    (fusionPacketFive_synthesis (padPacket hNM P)) ?_
  refine peqv_trans
    (fivePointwiseProduct_congr
      (synthesis_padPacket hNM P)) ?_
  refine peqv_symm ?_
  refine peqv_trans
    (synthesis_padPacket
      (fiveCarrierCutoff_mono hNM)
      (fusionPacketFive P)) ?_
  exact fusionPacketFive_synthesis P

/-- A smaller heat cutoff, embedded in a larger one, is coefficientwise below
the larger heat packet. -/
theorem heatPacket_pad_le
    {q : Q'} (hq0 : (0 : Q') ≤ q)
    {N M : Nat} (hNM : N ≤ M) :
    PacketLe (padPacket hNM (heatPacket q N))
      (heatPacket q M) := by
  intro s
  rw [coeffAt_padPacket]
  by_cases hsN : s < N + 1
  · rw [coeffAt_of_lt (heatPacket q N) hsN,
      coeffAt_of_lt (heatPacket q M) (by omega)]
    exact Q'.le_refl' _
  · have hNs : N < s := by omega
    rw [coeffAt_of_gt (heatPacket q N) hNs]
    exact heatPacket_nonnegative hq0 M s

/-! ## 3. Identification with the existing nonlinear Haar square -/

/-- The direct same-carrier fivefold packet and the canonical descended
nonlinear packet synthesize to the same fifth-power class polynomial. -/
theorem nonlinearFiveHaarPacket_eqv_direct_synthesis
    (q : Q') (N : Nat) :
    PolyEqv
      (synthesis (nonlinearFiveHaarPacket q N))
      (synthesis (fusionPacketFive (heatPacket q N))) := by
  refine peqv_trans
    (nonlinearFiveHaarPacket_synthesizes_pointwise q N) ?_
  exact peqv_symm
    (fusionPacketFive_synthesis (heatPacket q N))

/-! ## 4. Quantitative weighted-L1 to Haar-L2 stability -/

/-- Diagonal Haar square of a packet, exposed as a rational finite sum. -/
def packetHaarSq {N : Nat} (P : CharacterPacket N) : Q' :=
  finSum (fun s => coeffAt P s * coeffAt P s) (N + 1)

/-- Dimension-weighted coefficient gap between ordered packets. -/
def packetWeightedGap {N : Nat}
    (P Q : CharacterPacket N) : Q' :=
  finSum
    (fun s =>
      (coeffAt Q s + -(coeffAt P s)) *
        representationDimension s)
    (N + 1)

/-- Unweighted coefficient gap, used only as an intermediate quantity. -/
def packetCoefficientGap {N : Nat}
    (P Q : CharacterPacket N) : Q' :=
  finSum (fun s => coeffAt Q s + -(coeffAt P s)) (N + 1)

/-- Difference of squares over the constructive rational equivalence. -/
private theorem diff_sq (u v : Q') :
    ((u + -v) * (u + v)) ≈ (u * u + -(v * v)) := by
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_mul u (-v) (u + v)) ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr
      (Q'.mul_add_eqv u u v)
      (Q'.mul_add_eqv (-v) u v)) ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr
      (Q'.eqv_refl (u * u + u * v))
      (QPoly.q_add_congr
        (Q'.eqv_trans _ _ _
          (Q'.neg_mul_eqv v u)
          (Q'.neg_eqv_congr _ _
            (Q'.mul_comm_eqv v u)))
        (Q'.neg_mul_eqv v v))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left
      (u * u + u * v)
      (-(u * v) + -(v * v))
      (-(v * v) + -(u * v))
      (Q'.add_comm_eqv (-(u * v)) (-(v * v)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_swap_inner
      (u * u) (u * v) (-(v * v)) (-(u * v))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left
      (u * u + -(v * v))
      (u * v + -(u * v)) 0
      (Q'.add_neg_self_eqv (u * v))) ?_
  exact Q'.eqv_of_eq
    (Q'.add_zero' (u * u + -(v * v)))

theorem packetWeightedGap_nonneg
    {N : Nat} {P Q : CharacterPacket N}
    (hPQ : PacketLe P Q) :
    (0 : Q') ≤ packetWeightedGap P Q :=
  SU2HeatChannelHilbertSchmidtCompletion.finSum_nonneg_local _
    (fun s =>
      Q'.mul_nonneg _ _
        (Q'.sub_nonneg_of_le (hPQ s))
        (representationDimension_nonneg s))
    (N + 1)

theorem packetCoefficientGap_nonneg
    {N : Nat} {P Q : CharacterPacket N}
    (hPQ : PacketLe P Q) :
    (0 : Q') ≤ packetCoefficientGap P Q :=
  SU2HeatChannelHilbertSchmidtCompletion.finSum_nonneg_local _
    (fun s => Q'.sub_nonneg_of_le (hPQ s))
    (N + 1)

/-- Weighted mass decomposes exactly into the smaller mass plus the weighted
coefficient gap. -/
theorem packetWeightedMass_eq_add_gap
    {N : Nat} (P Q : CharacterPacket N) :
    packetWeightedMass Q
      ≈ packetWeightedMass P + packetWeightedGap P Q := by
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr _ _
      (fun s => by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (coeffAt Q s)
            (coeffAt P s + (coeffAt Q s + -(coeffAt P s)))
            (representationDimension s)
            (Q'.add_sub_cancel_eqv
              (coeffAt Q s) (coeffAt P s))) ?_
        exact Q'.add_mul_eqv
          (coeffAt P s)
          (coeffAt Q s + -(coeffAt P s))
          (representationDimension s))
      (N + 1)) ?_
  exact RationalTail.finSum_add
    (fun s => coeffAt P s * representationDimension s)
    (fun s =>
      (coeffAt Q s + -(coeffAt P s)) *
        representationDimension s)
    (N + 1)

/-- The Haar square decomposes as the smaller Haar square plus the exact
difference-of-squares cross sum. -/
theorem packetHaarSq_eq_add_cross
    {N : Nat} (P Q : CharacterPacket N) :
    packetHaarSq Q ≈
      packetHaarSq P +
        finSum
          (fun s =>
            (coeffAt Q s + -(coeffAt P s)) *
              (coeffAt Q s + coeffAt P s))
          (N + 1) := by
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr _ _
      (fun s => by
        refine Q'.eqv_trans _ _ _
          (Q'.add_sub_cancel_eqv
            (coeffAt Q s * coeffAt Q s)
            (coeffAt P s * coeffAt P s)) ?_
        exact Q'.add_eqv_congr_left
          (coeffAt P s * coeffAt P s)
          (coeffAt Q s * coeffAt Q s +
            -(coeffAt P s * coeffAt P s))
          ((coeffAt Q s + -(coeffAt P s)) *
            (coeffAt Q s + coeffAt P s))
          (Q'.eqv_symm
            (diff_sq (coeffAt Q s) (coeffAt P s))))
      (N + 1)) ?_
  exact RationalTail.finSum_add
    (fun s => coeffAt P s * coeffAt P s)
    (fun s =>
      (coeffAt Q s + -(coeffAt P s)) *
        (coeffAt Q s + coeffAt P s))
    (N + 1)

theorem one_le_representationDimension (s : Nat) :
    (1 : Q') ≤ representationDimension s := by
  refine Q'.le_trans' _ (Q'.ofNat 1) _ ?_ ?_
  · exact Q'.le_of_eqv (by decide)
  · exact CReal.ofNat_le_ofNat (by omega)

/-- Every nonnegative coefficient is bounded by the packet's weighted mass. -/
theorem coeffAt_le_packetWeightedMass
    {N : Nat} {P : CharacterPacket N}
    (hP : PacketNonnegative P) (s : Nat) :
    coeffAt P s ≤ packetWeightedMass P := by
  by_cases hs : s < N + 1
  · have hscale :
        coeffAt P s
          ≤ coeffAt P s * representationDimension s := by
      have hmul :
          coeffAt P s * (1 : Q')
            ≤ coeffAt P s * representationDimension s :=
        Q'.mul_le_mul_of_nonneg_left _ _ _
          (one_le_representationDimension s) (hP s)
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
        (Q'.mul_one_eqv (coeffAt P s))) hmul
    have hterm :
        coeffAt P s * representationDimension s
          ≤ packetWeightedMass P :=
      by
        change
          coeffAt P s * representationDimension s
            ≤ finSum
              (fun t =>
                coeffAt P t * representationDimension t)
              (N + 1)
        rw [← MovingCutoff.fsum_eq_finSum]
        exact BondMovingMoment.fsum_term_le_of_nonneg
          (fun t =>
            Q'.mul_nonneg _ _ (hP t)
              (representationDimension_nonneg t))
          s (N + 1) hs
    exact Q'.le_trans' _ _ _ hscale hterm
  · have hNs : N < s := by omega
    rw [coeffAt_of_gt P hNs]
    exact packetWeightedMass_nonneg hP

/-- Dropping the dimension weights can only reduce an ordered coefficient
gap. -/
theorem packetCoefficientGap_le_weightedGap
    {N : Nat} {P Q : CharacterPacket N}
    (hPQ : PacketLe P Q) :
    packetCoefficientGap P Q ≤ packetWeightedGap P Q := by
  exact CharacterTail.finSum_le_termwise _ _
    (fun s => by
      let d := coeffAt Q s + -(coeffAt P s)
      have hd0 : (0 : Q') ≤ d :=
        Q'.sub_nonneg_of_le (hPQ s)
      have hmul :
          d * (1 : Q') ≤ d * representationDimension s :=
        Q'.mul_le_mul_of_nonneg_left _ _ _
          (one_le_representationDimension s) hd0
      exact Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.mul_one_eqv d)) hmul)
    (N + 1)

/-- The exact square cross term is controlled by weighted gap times the sum
of the two weighted masses. -/
theorem packetCross_le_weighted
    {N : Nat} {P Q : CharacterPacket N}
    (hP : PacketNonnegative P) (hQ : PacketNonnegative Q)
    (hPQ : PacketLe P Q) :
    finSum
        (fun s =>
          (coeffAt Q s + -(coeffAt P s)) *
            (coeffAt Q s + coeffAt P s))
        (N + 1)
      ≤ packetWeightedGap P Q *
          (packetWeightedMass Q + packetWeightedMass P) := by
  let B := packetWeightedMass Q + packetWeightedMass P
  have hB0 : (0 : Q') ≤ B :=
    Q'.zero_le_add _ _
      (packetWeightedMass_nonneg hQ)
      (packetWeightedMass_nonneg hP)
  have hterm :
      ∀ s,
        (coeffAt Q s + -(coeffAt P s)) *
            (coeffAt Q s + coeffAt P s)
          ≤ (coeffAt Q s + -(coeffAt P s)) * B := by
    intro s
    have hsum :
        coeffAt Q s + coeffAt P s ≤ B :=
      Q'.add_le_add
        (coeffAt_le_packetWeightedMass hQ s)
        (coeffAt_le_packetWeightedMass hP s)
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hsum
      (Q'.sub_nonneg_of_le (hPQ s))
  have hsum :
      finSum
          (fun s =>
            (coeffAt Q s + -(coeffAt P s)) *
              (coeffAt Q s + coeffAt P s))
          (N + 1)
        ≤ finSum
          (fun s =>
            (coeffAt Q s + -(coeffAt P s)) * B)
          (N + 1) :=
    CharacterTail.finSum_le_termwise _ _ hterm (N + 1)
  have hpull :
      finSum
          (fun s =>
            (coeffAt Q s + -(coeffAt P s)) * B)
          (N + 1)
        ≈ packetCoefficientGap P Q * B :=
    Q'.eqv_symm
      (RationalTail.finSum_mul_const
        (fun s => coeffAt Q s + -(coeffAt P s))
        B (N + 1))
  have hgap :=
    packetCoefficientGap_le_weightedGap hPQ
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpull)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hgap hB0))

/-- **Quantitative nonlinear Haar-square stability at one common carrier.** -/
theorem packetHaarSq_le_add_weightedGap
    {N : Nat} {P Q : CharacterPacket N}
    (hP : PacketNonnegative P) (hQ : PacketNonnegative Q)
    (hPQ : PacketLe P Q) :
    packetHaarSq Q
      ≤ packetHaarSq P +
          packetWeightedGap P Q *
            (packetWeightedMass Q + packetWeightedMass P) := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (packetHaarSq_eq_add_cross P Q)) ?_
  exact Q'.add_le_add_left _ _ _
    (packetCross_le_weighted hP hQ hPQ)

/-- Coefficientwise order of nonnegative packets implies order of their
diagonal Haar squares. -/
theorem packetHaarSq_mono
    {N : Nat} {P Q : CharacterPacket N}
    (hP : PacketNonnegative P)
    (hQ : PacketNonnegative Q)
    (hPQ : PacketLe P Q) :
    packetHaarSq P ≤ packetHaarSq Q := by
  unfold packetHaarSq
  exact CharacterTail.finSum_le_termwise _ _
    (fun s =>
      Q'.mul_le_mul_of_nonneg
        (hPQ s) (hPQ s) (hQ s) (hP s))
    (N + 1)

/-- The rational diagonal square is the actual finite Haar pairing. -/
theorem packetHaarSq_eq_fusionHaar
    {N : Nat} (P : CharacterPacket N) :
    packetHaarSq P ≈ fusionHaar P P :=
  by
    unfold packetHaarSq
    rw [← MovingCutoff.fsum_eq_finSum]
    exact Q'.eqv_symm (fusionHaar_eq_diagonal P P)

/-- The diagonal packet sum is the bare Haar square of the synthesized class
polynomial.  This formulation compares packets with different cutoffs. -/
theorem packetHaarSq_eq_barePairing
    {N : Nat} (P : CharacterPacket N) :
    packetHaarSq P ≈
      bareVacuumHaar
        (pmul (synthesis P) (synthesis P)) := by
  exact Q'.eqv_trans _ _ _
    (packetHaarSq_eq_fusionHaar P)
    (Q'.eqv_symm (barePairing_eq_fusionHaar P P))

theorem synthesis_congr_of_packetEqv_local
    {N : Nat} {P Q : CharacterPacket N}
    (hPQ : PacketEqv P Q) :
    PolyEqv (synthesis P) (synthesis Q) := by
  intro x
  refine Q'.eqv_trans _
    (finSum
      (fun s => coeffAt P s * Cheb.U s x) (N + 1)) _
    (eval_synthesis P x) ?_
  refine Q'.eqv_trans _
    (finSum
      (fun s => coeffAt Q s * Cheb.U s x) (N + 1)) _ ?_ ?_
  · exact RationalTail.finSum_eqv_congr _ _
      (fun s =>
        Q'.mul_eqv_congr_right _ _ _
          (coeffAt_packetEqv hPQ s))
      (N + 1)
  · exact Q'.eqv_symm (eval_synthesis Q x)

/-- Haar-square semantics is invariant under synthesized polynomial
equivalence, even when the packet cutoffs differ. -/
theorem packetHaarSq_congr_synthesis
    {N M : Nat} {P : CharacterPacket N}
    {Q : CharacterPacket M}
    (hPQ : PolyEqv (synthesis P) (synthesis Q)) :
    packetHaarSq P ≈ packetHaarSq Q := by
  refine Q'.eqv_trans _
    (bareVacuumHaar
      (pmul (synthesis P) (synthesis P))) _
    (packetHaarSq_eq_barePairing P) ?_
  refine Q'.eqv_trans _
    (bareVacuumHaar
      (pmul (synthesis Q) (synthesis Q))) _ ?_ ?_
  · exact bareVacuumHaar_congr
      (pmul_congr hPQ hPQ)
  · exact Q'.eqv_symm
      (packetHaarSq_eq_barePairing Q)

/-- Directed padding before genuine fivefold fusion changes neither the
resulting nonlinear Haar square nor its carrier semantics. -/
theorem packetHaarSq_fusionPacketFive_pad
    {N M : Nat} (hNM : N ≤ M)
    (P : CharacterPacket N) :
    packetHaarSq
        (fusionPacketFive (padPacket hNM P))
      ≈ packetHaarSq (fusionPacketFive P) := by
  apply packetHaarSq_congr_synthesis
  refine peqv_trans
    (synthesis_congr_of_packetEqv_local
      (fusionPacketFive_pad hNM P)) ?_
  exact synthesis_padPacket
    (fiveCarrierCutoff_mono hNM)
    (fusionPacketFive P)

/-! ## 5. Scalar fifth-power Lipschitz envelope -/

def scalarPowerFour (x : Q') : Q' :=
  ((x * x) * x) * x

def fourthMixedSum (x y : Q') : Q' :=
  (((scalarPowerFour y +
      (((y * y) * y) * x)) +
      (((y * y) * x) * x)) +
      (((y * x) * x) * x)) +
      scalarPowerFour x

def fiveFourthCopies (W : Q') : Q' :=
  (((scalarPowerFour W + scalarPowerFour W) +
      scalarPowerFour W) +
      scalarPowerFour W) +
      scalarPowerFour W

private def scalarPowerFiveDifferenceL :
    RingNormaliser.PolyExpr :=
  let y := RingNormaliser.PolyExpr.var 1
  .mul (.mul (.mul (.mul y y) y) y) y

private def scalarPowerFiveDifferenceR :
    RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let x4 := .mul (.mul (.mul x x) x) x
  let y4 := .mul (.mul (.mul y y) y) y
  let y3x := .mul (.mul (.mul y y) y) x
  let y2x2 := .mul (.mul (.mul y y) x) x
  let yx3 := .mul (.mul (.mul y x) x) x
  .add (.mul x4 x)
    (.mul (.add y (.neg x))
      (.add (.add (.add (.add y4 y3x) y2x2) yx3) x4))

private theorem scalarPowerFiveDifference_normal :
    RingNormaliser.normalize scalarPowerFiveDifferenceL =
      RingNormaliser.normalize scalarPowerFiveDifferenceR := by
  decide

theorem scalarPowerFive_difference
    (x y : Q') :
  scalarPowerFive y ≈
      scalarPowerFive x +
        (y + -x) * fourthMixedSum x y := by
  simpa [scalarPowerFiveDifferenceL, scalarPowerFiveDifferenceR,
    scalarPowerFive, fourthMixedSum, scalarPowerFour,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      scalarPowerFiveDifferenceL scalarPowerFiveDifferenceR
      scalarPowerFiveDifference_normal
      (fun | 0 => x | _ => y))

theorem scalarPowerFour_nonneg
    {x : Q'} (hx0 : (0 : Q') ≤ x) :
    (0 : Q') ≤ scalarPowerFour x :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ hx0 hx0) hx0) hx0

theorem scalarPowerFive_nonneg
    {x : Q'} (hx0 : (0 : Q') ≤ x) :
    (0 : Q') ≤ scalarPowerFive x :=
  Q'.mul_nonneg _ _
    (scalarPowerFour_nonneg hx0) hx0

private theorem mulFour_le_powerFour
    {a b c d W : Q'}
    (hb0 : (0 : Q') ≤ b) (hc0 : (0 : Q') ≤ c)
    (hd0 : (0 : Q') ≤ d)
    (hW0 : (0 : Q') ≤ W)
    (haW : a ≤ W) (hbW : b ≤ W)
    (hcW : c ≤ W) (hdW : d ≤ W) :
    ((a * b) * c) * d ≤ scalarPowerFour W := by
  have h2 : a * b ≤ W * W :=
    Q'.mul_le_mul_of_nonneg haW hbW hW0 hb0
  have hWW0 : (0 : Q') ≤ W * W :=
    Q'.mul_nonneg _ _ hW0 hW0
  have h3 : (a * b) * c ≤ (W * W) * W :=
    Q'.mul_le_mul_of_nonneg h2 hcW hWW0 hc0
  have hWWW0 : (0 : Q') ≤ (W * W) * W :=
    Q'.mul_nonneg _ _ hWW0 hW0
  exact Q'.mul_le_mul_of_nonneg h3 hdW hWWW0 hd0

theorem fourthMixedSum_le_fiveFourthCopies
    {x y W : Q'}
    (hx0 : (0 : Q') ≤ x) (hy0 : (0 : Q') ≤ y)
    (hW0 : (0 : Q') ≤ W)
    (hxW : x ≤ W) (hyW : y ≤ W) :
    fourthMixedSum x y ≤ fiveFourthCopies W := by
  have hyyyy :
      scalarPowerFour y ≤ scalarPowerFour W :=
    mulFour_le_powerFour hy0 hy0 hy0 hW0
      hyW hyW hyW hyW
  have hyyyx :
      (((y * y) * y) * x) ≤ scalarPowerFour W :=
    mulFour_le_powerFour hy0 hy0 hx0 hW0
      hyW hyW hyW hxW
  have hyyxx :
      (((y * y) * x) * x) ≤ scalarPowerFour W :=
    mulFour_le_powerFour hy0 hx0 hx0 hW0
      hyW hyW hxW hxW
  have hyxxx :
      (((y * x) * x) * x) ≤ scalarPowerFour W :=
    mulFour_le_powerFour hx0 hx0 hx0 hW0
      hyW hxW hxW hxW
  have hxxxx :
      scalarPowerFour x ≤ scalarPowerFour W :=
    mulFour_le_powerFour hx0 hx0 hx0 hW0
      hxW hxW hxW hxW
  exact Q'.add_le_add
    (Q'.add_le_add
      (Q'.add_le_add
        (Q'.add_le_add hyyyy hyyyx)
        hyyxx)
      hyxxx)
    hxxxx

/-- **Fifth-power Lipschitz bound on a positive order interval.** -/
theorem scalarPowerFive_le_add_gap
    {x y W : Q'}
    (hx0 : (0 : Q') ≤ x) (hy0 : (0 : Q') ≤ y)
    (hW0 : (0 : Q') ≤ W)
    (hxy : x ≤ y) (hyW : y ≤ W) :
    scalarPowerFive y
      ≤ scalarPowerFive x +
          (y + -x) * fiveFourthCopies W := by
  have hxW : x ≤ W :=
    Q'.le_trans' _ _ _ hxy hyW
  have hgap0 : (0 : Q') ≤ y + -x :=
    Q'.sub_nonneg_of_le hxy
  have hmix :=
    fourthMixedSum_le_fiveFourthCopies
      hx0 hy0 hW0 hxW hyW
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (scalarPowerFive_difference x y)) ?_
  exact Q'.add_le_add_left _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      hmix hgap0)

theorem scalarPowerFive_mono
    {x y : Q'} (hx0 : (0 : Q') ≤ x)
    (hy0 : (0 : Q') ≤ y) (hxy : x ≤ y) :
    scalarPowerFive x ≤ scalarPowerFive y := by
  have h4 :
      scalarPowerFour x ≤ scalarPowerFour y :=
    mulFour_le_powerFour hx0 hx0 hx0 hy0
      hxy hxy hxy hxy
  exact Q'.mul_le_mul_of_nonneg
    h4 hxy (scalarPowerFour_nonneg hy0) hx0

/-! ## 6. Fivefold packet Lipschitz domination -/

private theorem le_of_add_le_add_left_local
    {a b c : Q'} (h : c + a ≤ c + b) :
    a ≤ b := by
  have hshift :
      (c + a) + -c ≤ (c + b) + -c :=
    Q'.add_le_add_right _ _ (-c) h
  have hleft : ((c + a) + -c) ≈ a := by
    refine Q'.eqv_trans _ ((a + c) + -c) _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.add_comm_eqv c a)) ?_
    refine Q'.eqv_trans _ (a + (c + -c)) _
      (Q'.add_assoc_eqv a c (-c)) ?_
    refine Q'.eqv_trans _ (a + 0) _
      (Q'.add_eqv_congr_left a _ _
        (Q'.add_neg_self_eqv c)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  have hright : ((c + b) + -c) ≈ b := by
    refine Q'.eqv_trans _ ((b + c) + -c) _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.add_comm_eqv c b)) ?_
    refine Q'.eqv_trans _ (b + (c + -c)) _
      (Q'.add_assoc_eqv b c (-c)) ?_
    refine Q'.eqv_trans _ (b + 0) _
      (Q'.add_eqv_congr_left b _ _
        (Q'.add_neg_self_eqv c)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' b)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hleft))
    (Q'.le_trans' _ _ _ hshift
      (Q'.le_of_eqv hright))

private theorem sub_eqv_right_of_eqv_add
    {x y g : Q'} (h : y ≈ x + g) :
    y + -x ≈ g := by
  refine Q'.eqv_trans _ ((x + g) + -x) _
    (Q'.add_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ (x + (g + -x)) _
    (Q'.add_assoc_eqv x g (-x)) ?_
  refine Q'.eqv_trans _ (x + (-x + g)) _
    (Q'.add_eqv_congr_left x _ _
      (Q'.add_comm_eqv g (-x))) ?_
  refine Q'.eqv_trans _ ((x + -x) + g) _
    (Q'.eqv_symm (Q'.add_assoc_eqv x (-x) g)) ?_
  refine Q'.eqv_trans _ (0 + g) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_neg_self_eqv x)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' g)

theorem packetWeightedMass_mono
    {N : Nat} {P Q : CharacterPacket N}
    (hPQ : PacketLe P Q) :
    packetWeightedMass P ≤ packetWeightedMass Q := by
  unfold packetWeightedMass
  exact CharacterTail.finSum_le_termwise _ _
    (fun s =>
      Q'.mul_le_mul_of_nonneg_right _ _ _
        (hPQ s) (representationDimension_nonneg s))
    (N + 1)

/-! ## 7. The exact heat-tail input gap -/

/-- On the larger carrier, the weighted packet gap between a padded heat
truncation and the larger heat packet is exactly the omitted all-label
window. -/
theorem heatPacket_pad_weightedGap_eq_tail
    (q : Q') {N M : Nat} (hNM : N ≤ M) :
    packetWeightedGap
        (padPacket hNM (heatPacket q N))
        (heatPacket q M)
      ≈ weightedDiscardedPartial q (N + 1) (M - N) := by
  let P := padPacket hNM (heatPacket q N)
  let Q := heatPacket q M
  let T := weightedDiscardedPartial q (N + 1) (M - N)
  have hcarrier :
      (N + 1) + (M - N) = M + 1 := by
    omega
  have hPmass :
      packetWeightedMass P
        ≈ finSum (weightedChanCoeff q) (N + 1) := by
    change
      packetWeightedMass (padPacket hNM (heatPacket q N))
        ≈ finSum (weightedChanCoeff q) (N + 1)
    refine Q'.eqv_trans _ _ _
      (packetWeightedMass_pad hNM (heatPacket q N)) ?_
    exact heatPacket_weightedMass_eq_partial q N
  have hQmass :
      packetWeightedMass Q
        ≈ finSum (weightedChanCoeff q) (M + 1) :=
    heatPacket_weightedMass_eq_partial q M
  have hsplit :
      finSum (weightedChanCoeff q) (M + 1)
        ≈ finSum (weightedChanCoeff q) (N + 1) + T := by
    simpa [T, hcarrier] using
      (FiveHolonomyPerronCutoff.finSum_split
        (weightedChanCoeff q) (N + 1) (M - N))
  have htailDecomp :
      packetWeightedMass Q
        ≈ packetWeightedMass P + T := by
    refine Q'.eqv_trans _ _ _ hQmass ?_
    refine Q'.eqv_trans _ _ _ hsplit ?_
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm hPmass)
  have hgapDecomp :
      packetWeightedMass Q
        ≈ packetWeightedMass P +
          packetWeightedGap P Q :=
    packetWeightedMass_eq_add_gap P Q
  have hgap :
      packetWeightedMass Q + -(packetWeightedMass P)
        ≈ packetWeightedGap P Q :=
    sub_eqv_right_of_eqv_add hgapDecomp
  have htail :
      packetWeightedMass Q + -(packetWeightedMass P)
        ≈ T :=
    sub_eqv_right_of_eqv_add htailDecomp
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm hgap) htail

/-- Past the explicit spacing-dependent label cutoff, the exact common-carrier
heat-packet gap is bounded by twice its first omitted weighted coefficient,
uniformly in the larger cutoff. -/
theorem heatPacket_pad_weightedGap_le_twoLead
    {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < 1)
    {N M : Nat} (hNM : N ≤ M)
    (hcut : explicitWeightedLabelCutoff q ≤ N + 1) :
    packetWeightedGap
        (padPacket hNM (heatPacket q N))
        (heatPacket q M)
      ≤ weightedChanCoeff q (N + 1) * Q'.ofNat 2 := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (heatPacket_pad_weightedGap_eq_tail q hNM)) ?_
  exact weightedDiscardedPartial_le_twoLead
    (Q'.le_of_lt hq0)
    (Q'.le_trans' _ _ _
      (Q'.le_of_lt hq1) (Q'.le_refl' 1))
    (N + 1) (by omega)
    (weightedDiscardedRatio_le_half_of_cutoff
      hq0 hq1 hcut)
    (M - N)

theorem fiveFourthCopies_nonneg
    {W : Q'} (hW0 : (0 : Q') ≤ W) :
    (0 : Q') ≤ fiveFourthCopies W := by
  have h4 : (0 : Q') ≤ scalarPowerFour W :=
    scalarPowerFour_nonneg hW0
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _ h4 h4)
        h4)
      h4)
    h4

/-- The dimension-weighted coefficient gap created by the genuine fivefold
Clebsch--Gordan fusion is Lipschitz in the input weighted gap.  Both sides are
computed on their actual common output carrier. -/
theorem fusionPacketFive_weightedGap_le
    {N : Nat} {P Q : CharacterPacket N} {W : Q'}
    (hP : PacketNonnegative P) (hQ : PacketNonnegative Q)
    (hPQ : PacketLe P Q)
    (hW0 : (0 : Q') ≤ W)
    (hQW : packetWeightedMass Q ≤ W) :
    packetWeightedGap (fusionPacketFive P) (fusionPacketFive Q)
      ≤ packetWeightedGap P Q * fiveFourthCopies W := by
  let FP := fusionPacketFive P
  let FQ := fusionPacketFive Q
  have hmassP0 : (0 : Q') ≤ packetWeightedMass P :=
    packetWeightedMass_nonneg hP
  have hmassQ0 : (0 : Q') ≤ packetWeightedMass Q :=
    packetWeightedMass_nonneg hQ
  have hmassPQ :
      packetWeightedMass P ≤ packetWeightedMass Q :=
    packetWeightedMass_mono hPQ
  have hpow :
      scalarPowerFive (packetWeightedMass Q) ≤
        scalarPowerFive (packetWeightedMass P) +
          (packetWeightedMass Q + -(packetWeightedMass P)) *
            fiveFourthCopies W :=
    scalarPowerFive_le_add_gap
      hmassP0 hmassQ0 hW0 hmassPQ hQW
  have hinputDifference :
      packetWeightedMass Q + -(packetWeightedMass P)
        ≈ packetWeightedGap P Q := by
    have hdecomp :=
      packetWeightedMass_eq_add_gap P Q
    have hshift :
        packetWeightedMass Q + -(packetWeightedMass P) ≈
          (packetWeightedMass P + packetWeightedGap P Q) +
            -(packetWeightedMass P) :=
      Q'.add_eqv_congr_right _ _ _
        hdecomp
    refine Q'.eqv_trans _ _ _ hshift ?_
    refine Q'.eqv_trans _
      (packetWeightedMass P +
        (packetWeightedGap P Q + -(packetWeightedMass P))) _ ?_ ?_
    · exact Q'.add_assoc_eqv
        (packetWeightedMass P)
        (packetWeightedGap P Q)
        (-(packetWeightedMass P))
    · refine Q'.eqv_trans _
        (packetWeightedMass P +
          (-(packetWeightedMass P) + packetWeightedGap P Q)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.add_comm_eqv
            (packetWeightedGap P Q)
            (-(packetWeightedMass P)))
      · refine Q'.eqv_trans _
          ((packetWeightedMass P + -(packetWeightedMass P)) +
            packetWeightedGap P Q) _ ?_ ?_
        · exact Q'.eqv_symm
            (Q'.add_assoc_eqv
              (packetWeightedMass P)
              (-(packetWeightedMass P))
              (packetWeightedGap P Q))
        · refine Q'.eqv_trans _
            (0 + packetWeightedGap P Q) _ ?_ ?_
          · exact Q'.add_eqv_congr_right _ _ _
              (Q'.add_neg_self_eqv
                (packetWeightedMass P))
          · exact Q'.eqv_of_eq
              (Q'.zero_add' (packetWeightedGap P Q))
  have hpowGap :
      scalarPowerFive (packetWeightedMass Q) ≤
        scalarPowerFive (packetWeightedMass P) +
          packetWeightedGap P Q * fiveFourthCopies W :=
    Q'.le_trans' _ _ _ hpow
      (Q'.add_le_add_left _ _ _
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_right _ _
            (fiveFourthCopies W) hinputDifference)))
  have hFPmass :
      packetWeightedMass FP ≈
        scalarPowerFive (packetWeightedMass P) :=
    fusionPacketFive_weightedMass P
  have hFQmass :
      packetWeightedMass FQ ≈
        scalarPowerFive (packetWeightedMass Q) :=
    fusionPacketFive_weightedMass Q
  have hForder : PacketLe FP FQ :=
    fusionPacketFive_le hP hQ hPQ
  have hFdecomp :
      packetWeightedMass FQ ≈
        packetWeightedMass FP +
          packetWeightedGap FP FQ :=
    packetWeightedMass_eq_add_gap FP FQ
  have hadd :
      packetWeightedMass FP +
          packetWeightedGap FP FQ
        ≤ packetWeightedMass FP +
          packetWeightedGap P Q * fiveFourthCopies W := by
    refine Q'.le_trans' _ (packetWeightedMass FQ) _
      (Q'.le_of_eqv (Q'.eqv_symm hFdecomp)) ?_
    refine Q'.le_trans' _
      (scalarPowerFive (packetWeightedMass Q)) _
      (Q'.le_of_eqv hFQmass) ?_
    exact Q'.le_trans' _
      (scalarPowerFive (packetWeightedMass P) +
        packetWeightedGap P Q * fiveFourthCopies W) _
      hpowGap
      (Q'.add_le_add_right _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm hFPmass)))
  exact le_of_add_le_add_left_local hadd

def nonlinearFiveAmplifier (W : Q') : Q' :=
  fiveFourthCopies W *
    (scalarPowerFive W + scalarPowerFive W)

theorem nonlinearFiveAmplifier_nonneg
    {W : Q'} (hW0 : (0 : Q') ≤ W) :
    (0 : Q') ≤ nonlinearFiveAmplifier W :=
  Q'.mul_nonneg _ _
    (fiveFourthCopies_nonneg hW0)
    (Q'.zero_le_add _ _
      (scalarPowerFive_nonneg hW0)
      (scalarPowerFive_nonneg hW0))

/-- **Common-carrier nonlinear Hilbert--Schmidt stability.**  The exact
fivefold Clebsch--Gordan output at `Q` is dominated by the output at `P` plus
the input dimension-weighted tail times an explicit fifth-power envelope. -/
theorem fusionPacketFive_haarSq_le
    {N : Nat} {P Q : CharacterPacket N} {W : Q'}
    (hP : PacketNonnegative P) (hQ : PacketNonnegative Q)
    (hPQ : PacketLe P Q)
    (hW0 : (0 : Q') ≤ W)
    (hQW : packetWeightedMass Q ≤ W) :
    packetHaarSq (fusionPacketFive Q)
      ≤ packetHaarSq (fusionPacketFive P) +
          packetWeightedGap P Q * nonlinearFiveAmplifier W := by
  let FP := fusionPacketFive P
  let FQ := fusionPacketFive Q
  have hFP0 : PacketNonnegative FP :=
    fusionPacketFive_nonnegative hP
  have hFQ0 : PacketNonnegative FQ :=
    fusionPacketFive_nonnegative hQ
  have hForder : PacketLe FP FQ :=
    fusionPacketFive_le hP hQ hPQ
  have hbase :=
    packetHaarSq_le_add_weightedGap
      hFP0 hFQ0 hForder
  have hgap :
      packetWeightedGap FP FQ ≤
        packetWeightedGap P Q * fiveFourthCopies W :=
    fusionPacketFive_weightedGap_le
      hP hQ hPQ hW0 hQW
  have hmassP :
      packetWeightedMass FP ≤ scalarPowerFive W := by
    refine Q'.le_trans' _
      (scalarPowerFive (packetWeightedMass P)) _
      (Q'.le_of_eqv (fusionPacketFive_weightedMass P)) ?_
    exact scalarPowerFive_mono
      (packetWeightedMass_nonneg hP) hW0
      (Q'.le_trans' _ _ _
        (packetWeightedMass_mono hPQ) hQW)
  have hmassQ :
      packetWeightedMass FQ ≤ scalarPowerFive W := by
    refine Q'.le_trans' _
      (scalarPowerFive (packetWeightedMass Q)) _
      (Q'.le_of_eqv (fusionPacketFive_weightedMass Q)) ?_
    exact scalarPowerFive_mono
      (packetWeightedMass_nonneg hQ) hW0 hQW
  have hmassSum :
      packetWeightedMass FQ + packetWeightedMass FP
        ≤ scalarPowerFive W + scalarPowerFive W :=
    Q'.add_le_add hmassQ hmassP
  have hgapUpper0 :
      (0 : Q') ≤
        packetWeightedGap P Q * fiveFourthCopies W :=
    Q'.mul_nonneg _ _
      (packetWeightedGap_nonneg hPQ)
      (fiveFourthCopies_nonneg hW0)
  have hmassLower0 :
      (0 : Q') ≤
        packetWeightedMass FQ + packetWeightedMass FP :=
    Q'.zero_le_add _ _
      (packetWeightedMass_nonneg hFQ0)
      (packetWeightedMass_nonneg hFP0)
  have hproduct :
      packetWeightedGap FP FQ *
          (packetWeightedMass FQ + packetWeightedMass FP)
        ≤
      (packetWeightedGap P Q * fiveFourthCopies W) *
          (scalarPowerFive W + scalarPowerFive W) :=
    Q'.mul_le_mul_of_nonneg
      hgap hmassSum hgapUpper0 hmassLower0
  refine Q'.le_trans' _ _ _ hbase ?_
  refine Q'.add_le_add_left _ _ _ ?_
  refine Q'.le_trans' _ _ _ hproduct ?_
  exact Q'.le_of_eqv
    (by
      unfold nonlinearFiveAmplifier
      exact Q'.mul_assoc_eqv
        (packetWeightedGap P Q)
        (fiveFourthCopies W)
        (scalarPowerFive W + scalarPowerFive W))

/-! ## 8. Quantitative nonlinear heat convergence on the physical carrier -/

/-- **Spacing-dependent nonlinear all-label tail bound.**  After the explicit
weighted label cutoff, every larger genuine fivefold heat carrier is bounded
by the smaller carrier plus twice the first omitted dimension-weighted
coefficient, multiplied by one spacing-dependent but cutoff-uniform
fifth-power envelope. -/
theorem heatFusionPacketFive_haarSq_le_twoLead
    {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < 1)
    {N M : Nat} (hNM : N ≤ M)
    (hcut : explicitWeightedLabelCutoff q ≤ N + 1) :
    packetHaarSq (fusionPacketFive (heatPacket q M))
      ≤ packetHaarSq (fusionPacketFive (heatPacket q N)) +
          (weightedChanCoeff q (N + 1) * Q'.ofNat 2) *
            nonlinearFiveAmplifier
              (weightedOnePlaquetteCeiling q
                (explicitWeightedLabelCutoff q)) := by
  let P := padPacket hNM (heatPacket q N)
  let Q := heatPacket q M
  let W :=
    weightedOnePlaquetteCeiling q
      (explicitWeightedLabelCutoff q)
  have hP0 : PacketNonnegative P :=
    padPacket_nonnegative hNM
      (heatPacket_nonnegative (Q'.le_of_lt hq0) N)
  have hQ0 : PacketNonnegative Q :=
    heatPacket_nonnegative (Q'.le_of_lt hq0) M
  have hPQ : PacketLe P Q :=
    heatPacket_pad_le (Q'.le_of_lt hq0) hNM
  have hW0 : (0 : Q') ≤ W := by
    unfold W weightedOnePlaquetteCeiling
    exact Q'.zero_le_add _ _
      (SU2HeatChannelHilbertSchmidtCompletion.finSum_nonneg_local _
        (weightedChanCoeff_nonneg
          (Q'.le_of_lt hq0))
        (explicitWeightedLabelCutoff q))
      (Q'.mul_nonneg _ _
        (weightedChanCoeff_nonneg
          (Q'.le_of_lt hq0)
          (explicitWeightedLabelCutoff q))
        (by decide))
  have hQW : packetWeightedMass Q ≤ W := by
    exact heatPacket_weightedMass_le_explicitCeiling
      hq0 hq1 M
  have hbase :
      packetHaarSq (fusionPacketFive Q)
        ≤ packetHaarSq (fusionPacketFive P) +
            packetWeightedGap P Q *
              nonlinearFiveAmplifier W :=
    fusionPacketFive_haarSq_le
      hP0 hQ0 hPQ hW0 hQW
  have hcarrier :
      packetHaarSq (fusionPacketFive P)
        ≈ packetHaarSq
            (fusionPacketFive (heatPacket q N)) :=
    packetHaarSq_fusionPacketFive_pad
      hNM (heatPacket q N)
  have htail :
      packetWeightedGap P Q
        ≤ weightedChanCoeff q (N + 1) * Q'.ofNat 2 :=
    heatPacket_pad_weightedGap_le_twoLead
      hq0 hq1 hNM hcut
  have hamp0 :
      (0 : Q') ≤ nonlinearFiveAmplifier W :=
    nonlinearFiveAmplifier_nonneg hW0
  have herror :
      packetWeightedGap P Q *
          nonlinearFiveAmplifier W
        ≤
      (weightedChanCoeff q (N + 1) * Q'.ofNat 2) *
          nonlinearFiveAmplifier W :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ htail hamp0
  exact Q'.le_trans' _ _ _ hbase
    (Q'.add_le_add
      (Q'.le_of_eqv hcarrier)
      herror)

/-- The finite genuine fivefold heat Haar squares are directed upward with the
character cutoff. -/
theorem heatFusionPacketFive_haarSq_mono
    {q : Q'} (hq0 : (0 : Q') ≤ q)
    {N M : Nat} (hNM : N ≤ M) :
    packetHaarSq (fusionPacketFive (heatPacket q N))
      ≤ packetHaarSq (fusionPacketFive (heatPacket q M)) := by
  let P := padPacket hNM (heatPacket q N)
  let Q := heatPacket q M
  have hP0 : PacketNonnegative P :=
    padPacket_nonnegative hNM
      (heatPacket_nonnegative hq0 N)
  have hQ0 : PacketNonnegative Q :=
    heatPacket_nonnegative hq0 M
  have hPQ : PacketLe P Q :=
    heatPacket_pad_le hq0 hNM
  have hcarrier :
      packetHaarSq (fusionPacketFive P)
        ≈ packetHaarSq
            (fusionPacketFive (heatPacket q N)) :=
    packetHaarSq_fusionPacketFive_pad
      hNM (heatPacket q N)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hcarrier))
    (packetHaarSq_mono
      (fusionPacketFive_nonnegative hP0)
      (fusionPacketFive_nonnegative hQ0)
      (fusionPacketFive_le hP0 hQ0 hPQ))

end YMGap.Continuum.SU2NonlinearFiveFusionTail

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SU2NonlinearFiveFusionTail.fusionPacketFive_synthesis
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionTail.fusionPacketFive_pad
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionTail.nonlinearFiveHaarPacket_eqv_direct_synthesis
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionTail.packetHaarSq_le_add_weightedGap
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionTail.scalarPowerFive_le_add_gap
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionTail.fusionPacketFive_weightedGap_le
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionTail.fusionPacketFive_haarSq_le
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionTail.heatPacket_pad_weightedGap_eq_tail
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionTail.heatFusionPacketFive_haarSq_le_twoLead
