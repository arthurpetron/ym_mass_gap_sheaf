/-
# A finite trivalent triangle packet network

This is the first connected three-vertex packet network.  Its internal edge
labels are `a` on `0--1`, `b` on `1--2`, and `c` on `2--0`.  Each vertex has
one external packet.  The evaluator sums the common triple `(a,b,c)` only
after all three exact SU(2) intertwiner constraints have been imposed:

    V₀(a,c) V₁(a,b) V₂(b,c).

Thus no internal edge is eliminated independently.  The coefficient packet
retains `a`; the scalar Gram additionally contracts it with its physical
Wilson weight.  A concrete all-fundamental instance is non-vacuous and gives
the sharp fence `1/512` for three independent edge contractions but `0` for
the simultaneous triangle, because every vertex would require the forbidden
odd coupling `N_{11}^1`.

Honest scope: this module implements one concrete finite trivalent graph and
its directed-system/completed-transfer coherence.  It is not yet a recursive
arbitrary-graph evaluator or a thermodynamic/continuum construction.
-/

import YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient

namespace YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit
open YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS
open YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer
open YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility
open YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem q_mul_zero_of_left {a b : Q'} (ha : a ≈ 0) :
    a * b ≈ 0 :=
  Q'.eqv_trans _ (0 * b) _
    (q_mul_congr ha (Q'.eqv_refl _)) (Q'.zero_mul_eqv _)

private theorem q_mul_zero_of_right {a b : Q'} (hb : b ≈ 0) :
    a * b ≈ 0 :=
  Q'.eqv_trans _ (a * 0) _
    (q_mul_congr (Q'.eqv_refl _) hb) (Q'.mul_zero_eqv _)

private theorem fsum_eqv_congr (f g : Nat → Q')
    (h : ∀ i, f i ≈ g i) (n : Nat) : fsum f n ≈ fsum g n :=
  YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr f g h n

private theorem fsum_zero_extension {f : Nat → Q'} {n m : Nat}
    (hnm : n ≤ m) (hz : ∀ i, n ≤ i → f i ≈ 0) :
    fsum f m ≈ fsum f n := by
  induction hnm with
  | refl => exact Q'.eqv_refl _
  | @step m hnm ih =>
      rw [fsum_succ]
      exact Q'.eqv_trans _ (fsum f n + 0) _
        (Q'.add_eqv_congr' ih (hz m hnm)) (q_add_zero_eqv _)

private theorem fusionInd_swap (a b c : Nat) :
    fusionInd a b c = fusionInd b a c := by
  unfold fusionInd
  rw [YMGap.Continuum.FusionCoreStepRoundD.fusionOK_symm_ab a b c]

private theorem vertexFiber_swap {K : Nat}
    (P Q R : CharacterPacket K) (a b : Nat) :
    vertexFiber P Q R a b ≈ vertexFiber Q P R b a := by
  unfold vertexFiber
  exact q_mul_congr (Q'.mul_comm_eqv _ _)
    (fsum_eqv_congr _ _ (fun c => by
      rw [fusionInd_swap a b c]
      exact Q'.eqv_refl _) (K + 1))

/-! ## Concrete syntax and simultaneous evaluator -/

/-- Nine packet decorations on a trivalent triangle: two internal half-edge
packets and one external packet at each of three vertices. -/
structure TrianglePacketNetwork (K : Nat) where
  edge01At0 : CharacterPacket K
  edge20At0 : CharacterPacket K
  external0 : CharacterPacket K
  edge01At1 : CharacterPacket K
  edge12At1 : CharacterPacket K
  external1 : CharacterPacket K
  edge12At2 : CharacterPacket K
  edge20At2 : CharacterPacket K
  external2 : CharacterPacket K

/-- Componentwise packet equality of two concrete decorations of the same
triangle. -/
structure TrianglePacketNetworkEqv {K : Nat}
    (T U : TrianglePacketNetwork K) : Prop where
  edge01At0 : PacketEqv T.edge01At0 U.edge01At0
  edge20At0 : PacketEqv T.edge20At0 U.edge20At0
  external0 : PacketEqv T.external0 U.external0
  edge01At1 : PacketEqv T.edge01At1 U.edge01At1
  edge12At1 : PacketEqv T.edge12At1 U.edge12At1
  external1 : PacketEqv T.external1 U.external1
  edge12At2 : PacketEqv T.edge12At2 U.edge12At2
  edge20At2 : PacketEqv T.edge20At2 U.edge20At2
  external2 : PacketEqv T.external2 U.external2

private theorem vertexFiber_congr {K : Nat}
    {P P' Q Qalt R R' : CharacterPacket K}
    (hP : PacketEqv P P') (hQ : PacketEqv Q Qalt)
    (hR : PacketEqv R R') (a b : Nat) :
    vertexFiber P Q R a b ≈ vertexFiber P' Qalt R' a b := by
  unfold vertexFiber
  exact q_mul_congr
    (q_mul_congr (coeffAt_packetEqv hP a) (coeffAt_packetEqv hQ b))
    (fsum_eqv_congr _ _ (fun c =>
      Q'.mul_eqv_congr_left (fusionInd a b c) _ _
        (coeffAt_packetEqv hR c)) (K + 1))

/-- The joint `(a,b,c)` summand.  All three vertex constraints occur in one
term, so an edge label cannot be summed before its two neighboring vertices
have both seen it. -/
def triangleIntegrand {K : Nat} (T : TrianglePacketNetwork K)
    (a b c : Nat) : Q' :=
  (vertexFiber T.edge01At0 T.edge20At0 T.external0 a c *
    vertexFiber T.edge01At1 T.edge12At1 T.external1 a b) *
      vertexFiber T.edge12At2 T.edge20At2 T.external2 b c

def triangleIntegrandCyclic {K : Nat} (T : TrianglePacketNetwork K)
    (a b c : Nat) : Q' :=
  (vertexFiberCyclic T.edge01At0 T.edge20At0 T.external0 a c *
    vertexFiberCyclic T.edge01At1 T.edge12At1 T.external1 a b) *
      vertexFiberCyclic T.edge12At2 T.edge20At2 T.external2 b c

/-- Reverse the cyclic order of the two internal half-edges at every vertex,
while retaining the same geometric edge labels. -/
def triangleIntegrandOrientationReverse {K : Nat}
    (T : TrianglePacketNetwork K) (a b c : Nat) : Q' :=
  (vertexFiber T.edge20At0 T.edge01At0 T.external0 c a *
    vertexFiber T.edge12At1 T.edge01At1 T.external1 b a) *
      vertexFiber T.edge20At2 T.edge12At2 T.external2 c b

private theorem triangleIntegrand_congr {K : Nat}
    {T U : TrianglePacketNetwork K} (h : TrianglePacketNetworkEqv T U)
    (a b c : Nat) : triangleIntegrand T a b c ≈
      triangleIntegrand U a b c := by
  unfold triangleIntegrand
  exact q_mul_congr
    (q_mul_congr
      (vertexFiber_congr h.edge01At0 h.edge20At0 h.external0 a c)
      (vertexFiber_congr h.edge01At1 h.edge12At1 h.external1 a b))
    (vertexFiber_congr h.edge12At2 h.edge20At2 h.external2 b c)

def triangleInner {K : Nat} (T : TrianglePacketNetwork K)
    (a b : Nat) : Q' :=
  fsum (fun c => packetEigen c * triangleIntegrand T a b c) (K + 1)

/-- First-edge marginal of the simultaneous three-label quotient. -/
def triangleCoeff {K : Nat} (T : TrianglePacketNetwork K) (a : Nat) : Q' :=
  fsum (fun b => packetEigen b * triangleInner T a b) (K + 1)

def triangleCoeffCyclic {K : Nat}
    (T : TrianglePacketNetwork K) (a : Nat) : Q' :=
  fsum (fun b => packetEigen b *
    fsum (fun c => packetEigen c * triangleIntegrandCyclic T a b c)
      (K + 1)) (K + 1)

def triangleCoeffOrientationReverse {K : Nat}
    (T : TrianglePacketNetwork K) (a : Nat) : Q' :=
  fsum (fun b => packetEigen b *
    fsum (fun c => packetEigen c *
      triangleIntegrandOrientationReverse T a b c) (K + 1)) (K + 1)

def triangleJointPacket {K : Nat}
    (T : TrianglePacketNetwork K) : CharacterPacket K where
  coeff i := triangleCoeff T i.val

def triangleJointPacketCyclic {K : Nat}
    (T : TrianglePacketNetwork K) : CharacterPacket K where
  coeff i := triangleCoeffCyclic T i.val

def triangleJointPacketOrientationReverse {K : Nat}
    (T : TrianglePacketNetwork K) : CharacterPacket K where
  coeff i := triangleCoeffOrientationReverse T i.val

/-- The simultaneous evaluator is compositional with respect to equality of
every packet decoration. -/
theorem triangleJointPacket_congr {K : Nat}
    {T U : TrianglePacketNetwork K} (h : TrianglePacketNetworkEqv T U) :
    PacketEqv (triangleJointPacket T) (triangleJointPacket U) := by
  intro i
  unfold triangleJointPacket triangleCoeff triangleInner
  exact fsum_eqv_congr _ _ (fun b =>
    Q'.mul_eqv_congr_left (packetEigen b) _ _
      (fsum_eqv_congr _ _ (fun c =>
        Q'.mul_eqv_congr_left (packetEigen c) _ _
          (triangleIntegrand_congr h i.val b c)) (K + 1))) (K + 1)

theorem triangleJointPacket_association {K : Nat}
    (T : TrianglePacketNetwork K) :
    PacketEqv (triangleJointPacket T) (triangleJointPacketCyclic T) := by
  intro i
  unfold triangleJointPacket triangleJointPacketCyclic triangleCoeff
    triangleCoeffCyclic triangleInner triangleIntegrand
    triangleIntegrandCyclic
  exact fsum_eqv_congr _ _ (fun b =>
    Q'.mul_eqv_congr_left (packetEigen b) _ _
      (fsum_eqv_congr _ _ (fun c =>
        Q'.mul_eqv_congr_left (packetEigen c) _ _
          (q_mul_congr
            (q_mul_congr
              (vertexFiber_association T.edge01At0 T.edge20At0
                T.external0 i.val c)
              (vertexFiber_association T.edge01At1 T.edge12At1
                T.external1 i.val b))
            (vertexFiber_association T.edge12At2 T.edge20At2
              T.external2 b c))) (K + 1))) (K + 1)

theorem triangleJointPacket_orientation {K : Nat}
    (T : TrianglePacketNetwork K) :
    PacketEqv (triangleJointPacket T)
      (triangleJointPacketOrientationReverse T) := by
  intro i
  unfold triangleJointPacket triangleJointPacketOrientationReverse
    triangleCoeff triangleCoeffOrientationReverse triangleInner
    triangleIntegrand triangleIntegrandOrientationReverse
  exact fsum_eqv_congr _ _ (fun b =>
    Q'.mul_eqv_congr_left (packetEigen b) _ _
      (fsum_eqv_congr _ _ (fun c =>
        Q'.mul_eqv_congr_left (packetEigen c) _ _
          (q_mul_congr
            (q_mul_congr
              (vertexFiber_swap T.edge01At0 T.edge20At0 T.external0
                i.val c)
              (vertexFiber_swap T.edge01At1 T.edge12At1 T.external1
                i.val b))
            (vertexFiber_swap T.edge12At2 T.edge20At2 T.external2 b c)))
        (K + 1))) (K + 1)

/-- Full simultaneous triangle contraction after applying the physical weight
on the retained `0--1` edge. -/
def triangleJointGram {K : Nat} (T : TrianglePacketNetwork K) : Q' :=
  fsum (fun a => packetEigen a * triangleCoeff T a) (K + 1)

/-- Exact common-triple form of the evaluator.  This identity makes explicit
that the three shared labels are contracted in one joint finite sum. -/
theorem triangleJointGram_common_triple {K : Nat}
    (T : TrianglePacketNetwork K) :
    triangleJointGram T ≈
      fsum (fun a => fsum (fun b => fsum (fun c =>
        (((packetEigen a * packetEigen b) * packetEigen c) *
          triangleIntegrand T a b c)) (K + 1)) (K + 1)) (K + 1) := by
  unfold triangleJointGram triangleCoeff triangleInner
  exact fsum_eqv_congr _ _ (fun a => by
    refine Q'.eqv_trans _
      (fsum (fun b => packetEigen a *
        (packetEigen b * fsum (fun c =>
          packetEigen c * triangleIntegrand T a b c) (K + 1)))
        (K + 1)) _ ?_ ?_
    · exact YMGap.Continuum.CubeRatioBounds.fsum_const_mul
        (packetEigen a)
        (fun b => packetEigen b * fsum (fun c =>
          packetEigen c * triangleIntegrand T a b c) (K + 1)) (K + 1)
    · exact fsum_eqv_congr _ _ (fun b => by
        refine Q'.eqv_trans _
          ((packetEigen a * packetEigen b) *
            fsum (fun c => packetEigen c * triangleIntegrand T a b c)
              (K + 1)) _
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
        refine Q'.eqv_trans _
          (fsum (fun c => (packetEigen a * packetEigen b) *
            (packetEigen c * triangleIntegrand T a b c)) (K + 1)) _
          (YMGap.Continuum.CubeRatioBounds.fsum_const_mul
            (packetEigen a * packetEigen b)
            (fun c => packetEigen c * triangleIntegrand T a b c) (K + 1)) ?_
        exact fsum_eqv_congr _ _ (fun c =>
          Q'.eqv_symm (Q'.mul_assoc_eqv
            (packetEigen a * packetEigen b) (packetEigen c)
            (triangleIntegrand T a b c))) (K + 1)) (K + 1)) (K + 1)

/-! ## Directed-system padding -/

def padTrianglePacketNetwork {K L : Nat} (hKL : K ≤ L)
    (T : TrianglePacketNetwork K) : TrianglePacketNetwork L where
  edge01At0 := padPacket hKL T.edge01At0
  edge20At0 := padPacket hKL T.edge20At0
  external0 := padPacket hKL T.external0
  edge01At1 := padPacket hKL T.edge01At1
  edge12At1 := padPacket hKL T.edge12At1
  external1 := padPacket hKL T.external1
  edge12At2 := padPacket hKL T.edge12At2
  edge20At2 := padPacket hKL T.edge20At2
  external2 := padPacket hKL T.external2

private theorem vertexFiber_pad {K L : Nat} (hKL : K ≤ L)
    (P Q R : CharacterPacket K) (a b : Nat) :
    vertexFiber (padPacket hKL P) (padPacket hKL Q) (padPacket hKL R) a b ≈
      vertexFiber P Q R a b := by
  unfold vertexFiber
  simp only [coeffAt_padPacket]
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _
    (fsum (fun c => fusionInd a b c * coeffAt R c) (K + 1)) _
    (fsum_zero_extension (by omega) ?_) (Q'.eqv_refl _)
  intro c hc
  rw [coeffAt_of_gt R (by omega)]
  exact Q'.mul_zero_eqv _

private theorem vertexFiber_zero_first_above {K : Nat}
    (P Q R : CharacterPacket K) {a : Nat} (ha : K < a) (b : Nat) :
    vertexFiber P Q R a b ≈ 0 := by
  unfold vertexFiber
  rw [coeffAt_of_gt P ha]
  exact Q'.eqv_trans _ (0 * _) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _))
    (Q'.zero_mul_eqv _)

private theorem vertexFiber_zero_second_above {K : Nat}
    (P Q R : CharacterPacket K) (a : Nat) {b : Nat} (hb : K < b) :
    vertexFiber P Q R a b ≈ 0 := by
  unfold vertexFiber
  rw [coeffAt_of_gt Q hb]
  exact Q'.eqv_trans _ (0 * _) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _))
    (Q'.zero_mul_eqv _)

private theorem triangleIntegrand_pad {K L : Nat} (hKL : K ≤ L)
    (T : TrianglePacketNetwork K) (a b c : Nat) :
    triangleIntegrand (padTrianglePacketNetwork hKL T) a b c ≈
      triangleIntegrand T a b c := by
  unfold triangleIntegrand padTrianglePacketNetwork
  exact q_mul_congr
    (q_mul_congr
      (vertexFiber_pad hKL T.edge01At0 T.edge20At0 T.external0 a c)
      (vertexFiber_pad hKL T.edge01At1 T.edge12At1 T.external1 a b))
    (vertexFiber_pad hKL T.edge12At2 T.edge20At2 T.external2 b c)

private theorem triangleIntegrand_zero_a {K : Nat}
    (T : TrianglePacketNetwork K) {a : Nat} (ha : K < a) (b c : Nat) :
    triangleIntegrand T a b c ≈ 0 := by
  unfold triangleIntegrand
  exact q_mul_zero_of_left (q_mul_zero_of_left
    (vertexFiber_zero_first_above T.edge01At0 T.edge20At0
      T.external0 ha c))

private theorem triangleIntegrand_zero_b {K : Nat}
    (T : TrianglePacketNetwork K) (a : Nat) {b : Nat} (hb : K < b)
    (c : Nat) : triangleIntegrand T a b c ≈ 0 := by
  unfold triangleIntegrand
  exact q_mul_zero_of_left (q_mul_zero_of_right
    (vertexFiber_zero_second_above T.edge01At1 T.edge12At1
      T.external1 a hb))

private theorem triangleIntegrand_zero_c {K : Nat}
    (T : TrianglePacketNetwork K) (a b : Nat) {c : Nat} (hc : K < c) :
    triangleIntegrand T a b c ≈ 0 := by
  unfold triangleIntegrand
  exact q_mul_zero_of_left (q_mul_zero_of_left
    (vertexFiber_zero_second_above T.edge01At0 T.edge20At0
      T.external0 a hc))

private theorem triangleInner_pad {K L : Nat} (hKL : K ≤ L)
    (T : TrianglePacketNetwork K) (a b : Nat) :
    triangleInner (padTrianglePacketNetwork hKL T) a b ≈
      triangleInner T a b := by
  unfold triangleInner
  refine Q'.eqv_trans _
    (fsum (fun c => packetEigen c * triangleIntegrand T a b c) (L + 1)) _
    (fsum_eqv_congr _ _ (fun c =>
      Q'.mul_eqv_congr_left (packetEigen c) _ _
        (triangleIntegrand_pad hKL T a b c)) (L + 1)) ?_
  exact fsum_zero_extension (by omega) (fun c hc =>
    q_mul_zero_of_right (triangleIntegrand_zero_c T a b (by omega)))

private theorem triangleInner_zero_a {K : Nat}
    (T : TrianglePacketNetwork K) {a : Nat} (ha : K < a) (b : Nat) :
    triangleInner T a b ≈ 0 := by
  unfold triangleInner
  apply YMGap.Continuum.FusionQuotientCollapse.fsum_zero_below
  intro c hc
  exact q_mul_zero_of_right (triangleIntegrand_zero_a T ha b c)

private theorem triangleInner_zero_b {K : Nat}
    (T : TrianglePacketNetwork K) (a : Nat) {b : Nat} (hb : K < b) :
    triangleInner T a b ≈ 0 := by
  unfold triangleInner
  apply YMGap.Continuum.FusionQuotientCollapse.fsum_zero_below
  intro c hc
  exact q_mul_zero_of_right (triangleIntegrand_zero_b T a hb c)

private theorem triangleCoeff_pad {K L : Nat} (hKL : K ≤ L)
    (T : TrianglePacketNetwork K) (a : Nat) :
    triangleCoeff (padTrianglePacketNetwork hKL T) a ≈
      triangleCoeff T a := by
  unfold triangleCoeff
  refine Q'.eqv_trans _
    (fsum (fun b => packetEigen b * triangleInner T a b) (L + 1)) _
    (fsum_eqv_congr _ _ (fun b =>
      Q'.mul_eqv_congr_left (packetEigen b) _ _
        (triangleInner_pad hKL T a b)) (L + 1)) ?_
  exact fsum_zero_extension (by omega) (fun b hb =>
    q_mul_zero_of_right (triangleInner_zero_b T a (by omega)))

private theorem triangleCoeff_zero_above {K : Nat}
    (T : TrianglePacketNetwork K) {a : Nat} (ha : K < a) :
    triangleCoeff T a ≈ 0 := by
  unfold triangleCoeff
  apply YMGap.Continuum.FusionQuotientCollapse.fsum_zero_below
  intro b hb
  exact q_mul_zero_of_right (triangleInner_zero_a T ha b)

/-- Padding all nine decorations at once commutes with the simultaneous graph
evaluator and introduces no false label channel. -/
theorem triangleJointPacket_pad {K L : Nat} (hKL : K ≤ L)
    (T : TrianglePacketNetwork K) :
    PacketEqv (triangleJointPacket (padTrianglePacketNetwork hKL T))
      (padPacket hKL (triangleJointPacket T)) := by
  intro i
  change triangleCoeff (padTrianglePacketNetwork hKL T) i.val ≈
    coeffAt (triangleJointPacket T) i.val
  refine Q'.eqv_trans _ (triangleCoeff T i.val) _
    (triangleCoeff_pad hKL T i.val) ?_
  by_cases hi : i.val < K + 1
  · rw [coeffAt_of_lt _ hi]
    exact Q'.eqv_refl _
  · rw [coeffAt_of_gt _ (by omega)]
    exact triangleCoeff_zero_above T (by omega)

/-! ## Exact anti-factorization fence -/

def fundamentalTriangleNetwork : TrianglePacketNetwork 1 where
  edge01At0 := trivalentFundamentalLeg
  edge20At0 := trivalentFundamentalLeg
  external0 := trivalentFundamentalLeg
  edge01At1 := trivalentFundamentalLeg
  edge12At1 := trivalentFundamentalLeg
  external1 := trivalentFundamentalLeg
  edge12At2 := trivalentFundamentalLeg
  edge20At2 := trivalentFundamentalLeg
  external2 := trivalentFundamentalLeg

/-- The forbidden evaluator that contracts the three internal edges
separately and never presents a common label triple to the vertices. -/
def triangleIndependentEdgeFactorization {K : Nat}
    (T : TrianglePacketNetwork K) : Q' :=
  (packetWilsonGram T.edge01At0 T.edge01At1 *
    packetWilsonGram T.edge12At1 T.edge12At2) *
      packetWilsonGram T.edge20At2 T.edge20At0

def fundamentalTriangleIndependentEdgeGram : Q' :=
  triangleIndependentEdgeFactorization fundamentalTriangleNetwork

def fundamentalTriangleSimultaneousGram : Q' :=
  triangleJointGram fundamentalTriangleNetwork

theorem fundamental_triangle_independent_exact :
    fundamentalTriangleIndependentEdgeGram ≈
      Q'.mkPos 1 512 (by decide) := by decide

theorem fundamental_triangle_simultaneous_zero :
    fundamentalTriangleSimultaneousGram ≈ 0 := by decide

/-- Three separately contracted edges lose the simultaneous odd-parity
constraint at the vertices. -/
theorem fundamental_triangle_independent_disagrees :
    ¬ (fundamentalTriangleIndependentEdgeGram ≈
      fundamentalTriangleSimultaneousGram) := by decide

/-! ## Completion and physical transfer descent -/

def completedTriangleJointState {K : Nat} (T : TrianglePacketNetwork K) :
    GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS (stagePacket (triangleJointPacket T))

def completedTriangleCyclicState {K : Nat} (T : TrianglePacketNetwork K) :
    GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS (stagePacket (triangleJointPacketCyclic T))

def completedTriangleOrientationReverseState {K : Nat}
    (T : TrianglePacketNetwork K) : GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS
    (stagePacket (triangleJointPacketOrientationReverse T))

private theorem embedV_eq_of_packetEqv {K : Nat}
    {P Q : CharacterPacket K} (h : PacketEqv P Q) :
    embedV packetColimitGNS (stagePacket P) =
      embedV packetColimitGNS (stagePacket Q) := by
  apply Quotient.sound
  exact embed_null_of_rad packetColimitGNS
    (rad_of_veq packetColimitGNS (fun s => coeffAt_packetEqv h s))

private theorem embedV_stage_pad_eq {K L : Nat} (hKL : K ≤ L)
    (P : CharacterPacket K) :
    embedV packetColimitGNS (stagePacket (padPacket hKL P)) =
      embedV packetColimitGNS (stagePacket P) := by
  apply Quotient.sound
  exact embed_null_of_rad packetColimitGNS
    (rad_of_veq packetColimitGNS (fun s => by
      change coeffAt (padPacket hKL P) s ≈ coeffAt P s
      rw [coeffAt_padPacket]
      exact Q'.eqv_refl _))

theorem completedTriangle_association {K : Nat}
    (T : TrianglePacketNetwork K) :
    completedTriangleJointState T = completedTriangleCyclicState T :=
  embedV_eq_of_packetEqv (triangleJointPacket_association T)

theorem completedTriangle_congr {K : Nat}
    {T U : TrianglePacketNetwork K} (h : TrianglePacketNetworkEqv T U) :
    completedTriangleJointState T = completedTriangleJointState U :=
  embedV_eq_of_packetEqv (triangleJointPacket_congr h)

theorem completedTriangle_orientation {K : Nat}
    (T : TrianglePacketNetwork K) :
    completedTriangleJointState T =
      completedTriangleOrientationReverseState T :=
  embedV_eq_of_packetEqv (triangleJointPacket_orientation T)

theorem completedTriangle_pad {K L : Nat} (hKL : K ≤ L)
    (T : TrianglePacketNetwork K) :
    completedTriangleJointState (padTrianglePacketNetwork hKL T) =
      completedTriangleJointState T := by
  refine Eq.trans (embedV_eq_of_packetEqv (triangleJointPacket_pad hKL T)) ?_
  exact embedV_stage_pad_eq hKL (triangleJointPacket T)

theorem completedTriangle_transfer_exact {K : Nat}
    (T : TrianglePacketNetwork K) :
    completedPacketTransfer (completedTriangleJointState T) =
      embedV packetColimitGNS
        (stagePacket (packetTransfer (triangleJointPacket T))) :=
  completedPacketTransfer_embed _

theorem completedTriangle_transfer_association_descends {K : Nat}
    (T : TrianglePacketNetwork K) :
    completedPacketTransfer (completedTriangleJointState T) =
      completedPacketTransfer (completedTriangleCyclicState T) :=
  congrArg completedPacketTransfer (completedTriangle_association T)

theorem completedTriangle_transfer_congr_descends {K : Nat}
    {T U : TrianglePacketNetwork K} (h : TrianglePacketNetworkEqv T U) :
    completedPacketTransfer (completedTriangleJointState T) =
      completedPacketTransfer (completedTriangleJointState U) :=
  congrArg completedPacketTransfer (completedTriangle_congr h)

theorem completedTriangle_transfer_orientation_descends {K : Nat}
    (T : TrianglePacketNetwork K) :
    completedPacketTransfer (completedTriangleJointState T) =
      completedPacketTransfer (completedTriangleOrientationReverseState T) :=
  congrArg completedPacketTransfer (completedTriangle_orientation T)

theorem completedTriangle_transfer_pad_descends {K L : Nat}
    (hKL : K ≤ L) (T : TrianglePacketNetwork K) :
    completedPacketTransfer
        (completedTriangleJointState (padTrianglePacketNetwork hKL T)) =
      completedPacketTransfer (completedTriangleJointState T) :=
  congrArg completedPacketTransfer (completedTriangle_pad hKL T)

end YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork

#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.triangleJointPacket_association
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.triangleJointPacket_orientation
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.triangleJointPacket_congr
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.triangleJointGram_common_triple
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.triangleJointPacket_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.fundamental_triangle_independent_exact
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.fundamental_triangle_simultaneous_zero
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.fundamental_triangle_independent_disagrees
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.completedTriangle_association
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.completedTriangle_congr
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.completedTriangle_orientation
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.completedTriangle_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.completedTriangle_transfer_exact
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.completedTriangle_transfer_association_descends
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.completedTriangle_transfer_congr_descends
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.completedTriangle_transfer_orientation_descends
#print axioms YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork.completedTriangle_transfer_pad_descends
