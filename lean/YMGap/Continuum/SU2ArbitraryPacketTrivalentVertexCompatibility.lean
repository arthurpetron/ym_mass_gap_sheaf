/-
# Arbitrary-cutoff trivalent SU(2) packet vertices

Three independently truncated plaquette packets are first embedded at one
canonical common cutoff.  Their two binary Clebsch--Gordan association trees
are retained as a single trivalent vertex carrier.  Exact character synthesis,
followed by constructive Haar extraction against every basis character, proves
that the two trees agree coefficientwise.  Thus associativity is derived in
the packet quotient rather than postulated as a representation-ring law.

The carrier is coherent under three unrelated cutoff enlargements.  It also
has an exact cross-tree interacting Gram and a simultaneous completed transfer
action.  These statements concern all three incident packets at once; they are
not a product of three independent one-link claims.

Honest scope: this is one arbitrary-packet trivalent shared-link vertex.  It
does not yet identify vertices across a general lattice, impose all cycle
relations simultaneously, or construct the thermodynamic/continuum limit.
-/

import YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility

namespace YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialHaarDescent
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit
open YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS
open YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer
open YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge
open YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility

local infix:50 " ≈ " => Q'.eqv

private theorem packetEqv_refl {N : Nat} (P : CharacterPacket N) :
    PacketEqv P P := fun _ => Q'.eqv_refl _

private theorem packetEqv_trans {N : Nat} {P Q R : CharacterPacket N}
    (hPQ : PacketEqv P Q) (hQR : PacketEqv Q R) : PacketEqv P R :=
  fun i => Q'.eqv_trans _ _ _ (hPQ i) (hQR i)

private theorem finSum_zero_extension {f : Nat → Q'} {n m : Nat}
    (hnm : n ≤ m) (hz : ∀ i, n ≤ i → f i ≈ 0) :
    finSum f m ≈ finSum f n := by
  induction hnm with
  | refl => exact Q'.eqv_refl _
  | @step m hnm ih =>
      exact Q'.eqv_trans _ (finSum f n + 0) _
        (q_add_congr ih (hz m hnm)) (q_add_zero_eqv _)

/-! ## Synthesis reflects coefficient equality -/

/-- Haar pairing with a pure character extracts the corresponding packet
coefficient.  This is the constructive coefficient-separation mechanism used
below; no choice of roots or interpolation nodes occurs. -/
theorem fusionHaar_basis_right {N : Nat} (P : CharacterPacket N)
    (i : Fin (N + 1)) :
    fusionHaar P (basisPacket i) ≈ P.coeff i := by
  refine Q'.eqv_trans _
    (fsum (fun s => coeffAt P s * coeffAt (basisPacket i) s) (N + 1)) _
    (fusionHaar_eq_diagonal P (basisPacket i)) ?_
  have hzero : ∀ s, s ≠ i.val →
      coeffAt P s * coeffAt (basisPacket i) s ≈ 0 := by
    intro s hsi
    rw [coeffAt_basis i s, if_neg hsi]
    exact Q'.mul_zero_eqv _
  refine Q'.eqv_trans _
    (coeffAt P i.val * coeffAt (basisPacket i) i.val) _
    (YMGap.Continuum.FusionQuotientCollapse.fsum_collapse
      hzero (N + 1) i.isLt) ?_
  rw [coeffAt_basis i i.val, if_pos rfl]
  exact Q'.eqv_trans _ (coeffAt P i.val) _
    (Q'.mul_one_eqv _) (Q'.eqv_of_eq (coeffAt_of_lt P i.isLt))

/-- Bare polynomial Haar pairing is exactly the packet fusion pairing. -/
theorem barePairing_eq_fusionHaar {N : Nat} (P Q : CharacterPacket N) :
    bareVacuumHaar (pmul (synthesis P) (synthesis Q)) ≈
      fusionHaar P Q := by
  refine Q'.eqv_trans _
    (bareVacuumHaar (synthesis (fusionPacket P Q))) _ ?_ ?_
  · exact bareVacuumHaar_congr
      (peqv_symm (synthesis_fusionPacket_product P Q))
  · refine Q'.eqv_trans _ (vacuumHaar (fusionPacket P Q)) _
      (bareVacuumHaar_synthesis_packet (fusionPacket P Q)) ?_
    exact vacuumHaar_fusionPacket P Q

/-- **Faithfulness of exact character synthesis.**  Semantic equality of two
finite synthesized class polynomials forces coefficientwise packet equality.
Every coordinate is recovered by the derived Haar pairing above. -/
theorem packetEqv_of_synthesis {N : Nat} {P Q : CharacterPacket N}
    (h : PolyEqv (synthesis P) (synthesis Q)) : PacketEqv P Q := by
  intro i
  have hpair :
      bareVacuumHaar (pmul (synthesis P) (synthesis (basisPacket i))) ≈
        bareVacuumHaar (pmul (synthesis Q) (synthesis (basisPacket i))) :=
    bareVacuumHaar_congr (pmul_congr h (peqv_refl _))
  refine Q'.eqv_trans _ (fusionHaar P (basisPacket i)) _
    (Q'.eqv_symm (fusionHaar_basis_right P i)) ?_
  refine Q'.eqv_trans _
    (bareVacuumHaar (pmul (synthesis P) (synthesis (basisPacket i)))) _
    (Q'.eqv_symm (barePairing_eq_fusionHaar P (basisPacket i))) ?_
  refine Q'.eqv_trans _
    (bareVacuumHaar (pmul (synthesis Q) (synthesis (basisPacket i)))) _ hpair ?_
  refine Q'.eqv_trans _ (fusionHaar Q (basisPacket i)) _
    (barePairing_eq_fusionHaar Q (basisPacket i)) ?_
  exact fusionHaar_basis_right Q i

/-- Zero-padding changes neither the synthesized character polynomial nor any
of its semantic values. -/
theorem synthesis_padPacket {N M : Nat} (hNM : N ≤ M)
    (P : CharacterPacket N) :
    PolyEqv (synthesis (padPacket hNM P)) (synthesis P) := by
  intro x
  refine Q'.eqv_trans _
    (finSum (fun s => coeffAt (padPacket hNM P) s * Cheb.U s x) (M + 1)) _
    (eval_synthesis (padPacket hNM P) x) ?_
  refine Q'.eqv_trans _
    (finSum (fun s => coeffAt P s * Cheb.U s x) (M + 1)) _ ?_ ?_
  · exact RationalTail.finSum_eqv_congr _ _ (fun s => by
      rw [coeffAt_padPacket]
      exact Q'.eqv_refl _) (M + 1)
  · refine Q'.eqv_trans _
      (finSum (fun s => coeffAt P s * Cheb.U s x) (N + 1)) _
      (finSum_zero_extension (by omega) ?_) ?_
    · intro s hs
      rw [coeffAt_of_gt P (by omega)]
      exact Q'.zero_mul_eqv _
    · exact Q'.eqv_symm (eval_synthesis P x)

/-! ## The trivalent carrier and its association/orientation quotient -/

/-- Output cutoff of the two binary trees.  It is deliberately written in
the shape produced by two applications of `fusionPacket`. -/
def trivalentOutputCutoff (K : Nat) : Nat := 2 * (2 * K)

/-- Both association trees of a single three-leg vertex. -/
abbrev TrivalentVertexPacket (K : Nat) :=
  CharacterPacket (trivalentOutputCutoff K) ×
    CharacterPacket (trivalentOutputCutoff K)

def TrivalentVertexEqv {K : Nat}
    (X Y : TrivalentVertexPacket K) : Prop :=
  PacketEqv X.1 Y.1 ∧ PacketEqv X.2 Y.2

private theorem vertexEqv_trans {K : Nat}
    {X Y Z : TrivalentVertexPacket K}
    (hXY : TrivalentVertexEqv X Y) (hYZ : TrivalentVertexEqv Y Z) :
    TrivalentVertexEqv X Z :=
  ⟨packetEqv_trans hXY.1 hYZ.1, packetEqv_trans hXY.2 hYZ.2⟩

private theorem base_to_double (K : Nat) : K ≤ 2 * K := by omega

def leftAssociatedPacket {K : Nat}
    (P Q R : CharacterPacket K) : CharacterPacket (trivalentOutputCutoff K) :=
  fusionPacket (fusionPacket P Q) (padPacket (base_to_double K) R)

def rightAssociatedPacket {K : Nat}
    (P Q R : CharacterPacket K) : CharacterPacket (trivalentOutputCutoff K) :=
  fusionPacket (padPacket (base_to_double K) P) (fusionPacket Q R)

def trivalentVertexPacket {K : Nat}
    (P Q R : CharacterPacket K) : TrivalentVertexPacket K :=
  (leftAssociatedPacket P Q R, rightAssociatedPacket P Q R)

/-- Exact synthesis of the left association tree. -/
theorem leftAssociated_synthesis {K : Nat}
    (P Q R : CharacterPacket K) :
    PolyEqv (synthesis (leftAssociatedPacket P Q R))
      (pmul (pmul (synthesis P) (synthesis Q)) (synthesis R)) := by
  refine peqv_trans (synthesis_fusionPacket_product _ _) ?_
  exact pmul_congr (synthesis_fusionPacket_product P Q)
    (synthesis_padPacket (base_to_double K) R)

/-- Exact synthesis of the right association tree. -/
theorem rightAssociated_synthesis {K : Nat}
    (P Q R : CharacterPacket K) :
    PolyEqv (synthesis (rightAssociatedPacket P Q R))
      (pmul (synthesis P) (pmul (synthesis Q) (synthesis R))) := by
  refine peqv_trans (synthesis_fusionPacket_product _ _) ?_
  exact pmul_congr (synthesis_padPacket (base_to_double K) P)
    (synthesis_fusionPacket_product Q R)

/-- **General trivalent association quotient.**  For arbitrary coefficient
packets, not merely fundamental modes, the two Clebsch--Gordan trees agree in
every output channel. -/
theorem trivalent_association_closure {K : Nat}
    (P Q R : CharacterPacket K) :
    PacketEqv (leftAssociatedPacket P Q R)
      (rightAssociatedPacket P Q R) := by
  apply packetEqv_of_synthesis
  exact peqv_trans (leftAssociated_synthesis P Q R)
    (peqv_trans (pmul_assoc (synthesis P) (synthesis Q) (synthesis R))
      (peqv_symm (rightAssociated_synthesis P Q R)))

/-- Closed normalization guard: three fundamental legs fuse to
`2 chi_1 + chi_3`.  The multiplicity two certifies that this carrier is a
genuine interacting trivalent fusion, not three independent one-link states. -/
def trivalentFundamentalLeg : CharacterPacket 1 :=
  basisPacket ⟨1, by omega⟩

theorem trivalentFundamental_multiplicity :
    coeffAt
        (leftAssociatedPacket trivalentFundamentalLeg
          trivalentFundamentalLeg trivalentFundamentalLeg) 0 ≈ 0 ∧
    coeffAt
        (leftAssociatedPacket trivalentFundamentalLeg
          trivalentFundamentalLeg trivalentFundamentalLeg) 1 ≈ 2 ∧
    coeffAt
        (leftAssociatedPacket trivalentFundamentalLeg
          trivalentFundamentalLeg trivalentFundamentalLeg) 2 ≈ 0 ∧
    coeffAt
        (leftAssociatedPacket trivalentFundamentalLeg
          trivalentFundamentalLeg trivalentFundamentalLeg) 3 ≈ 1 := by
  decide

/-- Reversing all three incident orientations preserves both association
trees simultaneously in the packet quotient. -/
theorem trivalent_orientation_reversal {K : Nat}
    (P Q R : CharacterPacket K) :
    TrivalentVertexEqv (trivalentVertexPacket P Q R)
      (trivalentVertexPacket R Q P) := by
  constructor <;> apply packetEqv_of_synthesis
  · exact peqv_trans (leftAssociated_synthesis P Q R)
      (peqv_trans
        (pmul_comm (pmul (synthesis P) (synthesis Q)) (synthesis R))
        (peqv_trans
          (pmul_congr (peqv_refl _) (pmul_comm (synthesis P) (synthesis Q)))
          (peqv_trans
            (peqv_symm
              (pmul_assoc (synthesis R) (synthesis Q) (synthesis P)))
            (peqv_symm (leftAssociated_synthesis R Q P)))))
  · exact peqv_trans (rightAssociated_synthesis P Q R)
      (peqv_trans
        (peqv_symm (pmul_assoc (synthesis P) (synthesis Q) (synthesis R)))
        (peqv_trans
          (pmul_comm (pmul (synthesis P) (synthesis Q)) (synthesis R))
          (peqv_trans
            (pmul_congr (peqv_refl _) (pmul_comm (synthesis P) (synthesis Q)))
            (peqv_symm (rightAssociated_synthesis R Q P)))))

/-! ## Simultaneous cutoff coherence for all three legs -/

private theorem padPacket_congr {N M : Nat} (hNM : N ≤ M)
    {P Q : CharacterPacket N} (hPQ : PacketEqv P Q) :
    PacketEqv (padPacket hNM P) (padPacket hNM Q) := by
  intro i
  change coeffAt P i.val ≈ coeffAt Q i.val
  exact coeffAt_packetEqv hPQ i.val

/-- The whole two-tree vertex respects coefficient equality in all three
incident legs simultaneously. -/
theorem trivalentVertexPacket_congr {K : Nat}
    {P P' Q Q' R R' : CharacterPacket K}
    (hP : PacketEqv P P') (hQ : PacketEqv Q Q')
    (hR : PacketEqv R R') :
    TrivalentVertexEqv (trivalentVertexPacket P Q R)
      (trivalentVertexPacket P' Q' R') := by
  exact ⟨
    fusionPacket_congr (fusionPacket_congr hP hQ)
      (padPacket_congr (base_to_double K) hR),
    fusionPacket_congr (padPacket_congr (base_to_double K) hP)
      (fusionPacket_congr hQ hR)⟩

/-- Padding all three common-cutoff legs commutes with both association trees
in one directed-system square. -/
theorem trivalentVertexPacket_pad {K L : Nat} (hKL : K ≤ L)
    (P Q R : CharacterPacket K) :
    TrivalentVertexEqv
      (trivalentVertexPacket (padPacket hKL P) (padPacket hKL Q)
        (padPacket hKL R))
      (padPacket
          (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 hKL))
          (trivalentVertexPacket P Q R).1,
        padPacket
          (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 hKL))
          (trivalentVertexPacket P Q R).2) := by
  let h2 : 2 * K ≤ 2 * L := Nat.mul_le_mul_left 2 hKL
  have hRpath : PacketEqv
      (padPacket (base_to_double L) (padPacket hKL R))
      (padPacket h2 (padPacket (base_to_double K) R)) := by
    intro i
    change coeffAt (padPacket hKL R) i.val ≈
      coeffAt (padPacket (base_to_double K) R) i.val
    rw [coeffAt_padPacket, coeffAt_padPacket]
    exact Q'.eqv_refl _
  have hPpath : PacketEqv
      (padPacket (base_to_double L) (padPacket hKL P))
      (padPacket h2 (padPacket (base_to_double K) P)) := by
    intro i
    change coeffAt (padPacket hKL P) i.val ≈
      coeffAt (padPacket (base_to_double K) P) i.val
    rw [coeffAt_padPacket, coeffAt_padPacket]
    exact Q'.eqv_refl _
  constructor
  · exact packetEqv_trans
      (fusionPacket_congr (fusionPacket_pad hKL P Q) hRpath)
      (fusionPacket_pad h2 (fusionPacket P Q)
        (padPacket (base_to_double K) R))
  · exact packetEqv_trans
      (fusionPacket_congr hPpath (fusionPacket_pad hKL Q R))
      (fusionPacket_pad h2 (padPacket (base_to_double K) P)
        (fusionPacket Q R))

/-- Canonical common cutoff of three independently truncated legs. -/
def trivalentCutoff (N M L : Nat) : Nat := Nat.max N (Nat.max M L)

def padTrivalentFirst {N M L : Nat} (P : CharacterPacket N) :
    CharacterPacket (trivalentCutoff N M L) :=
  padPacket (Nat.le_max_left N (Nat.max M L)) P

def padTrivalentSecond {N M L : Nat} (Q : CharacterPacket M) :
    CharacterPacket (trivalentCutoff N M L) :=
  padPacket (Nat.le_trans (Nat.le_max_left M L)
    (Nat.le_max_right N (Nat.max M L))) Q

def padTrivalentThird {N M L : Nat} (R : CharacterPacket L) :
    CharacterPacket (trivalentCutoff N M L) :=
  padPacket (Nat.le_trans (Nat.le_max_right M L)
    (Nat.le_max_right N (Nat.max M L))) R

/-- The arbitrary-cutoff trivalent carrier retains both association trees. -/
def arbitraryTrivalentVertexPacket {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) : TrivalentVertexPacket (trivalentCutoff N M L) :=
  trivalentVertexPacket (padTrivalentFirst (M := M) (L := L) P)
    (padTrivalentSecond (N := N) (L := L) Q)
    (padTrivalentThird (N := N) (M := M) R)

private theorem trivalentCutoff_mono
    {N N' M M' L L' : Nat}
    (hN : N ≤ N') (hM : M ≤ M') (hL : L ≤ L') :
    trivalentCutoff N M L ≤ trivalentCutoff N' M' L' := by
  apply (Nat.max_le).2
  exact ⟨Nat.le_trans hN (Nat.le_max_left _ _),
    (Nat.max_le).2
      ⟨Nat.le_trans hM
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)),
        Nat.le_trans hL
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))⟩⟩

/-- **Independent-cutoff coherence for a trivalent vertex.**  The three
input cutoffs may increase by unrelated amounts.  Both association trees then
agree with the corresponding padding of the original two-tree carrier. -/
theorem arbitraryTrivalentVertexPacket_pad_independent
    {N N' M M' L L' : Nat}
    (hN : N ≤ N') (hM : M ≤ M') (hL : L ≤ L')
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    TrivalentVertexEqv
      (arbitraryTrivalentVertexPacket (padPacket hN P)
        (padPacket hM Q) (padPacket hL R))
      (padPacket
          (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2
            (trivalentCutoff_mono hN hM hL)))
          (arbitraryTrivalentVertexPacket P Q R).1,
        padPacket
          (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2
            (trivalentCutoff_mono hN hM hL)))
          (arbitraryTrivalentVertexPacket P Q R).2) := by
  let K := trivalentCutoff N M L
  let K' := trivalentCutoff N' M' L'
  have hKK : K ≤ K' := trivalentCutoff_mono hN hM hL
  let A : CharacterPacket K := padTrivalentFirst (M := M) (L := L) P
  let B : CharacterPacket K := padTrivalentSecond (N := N) (L := L) Q
  let C : CharacterPacket K := padTrivalentThird (N := N) (M := M) R
  let A' : CharacterPacket K' :=
    padTrivalentFirst (M := M') (L := L') (padPacket hN P)
  let B' : CharacterPacket K' :=
    padTrivalentSecond (N := N') (L := L') (padPacket hM Q)
  let C' : CharacterPacket K' :=
    padTrivalentThird (N := N') (M := M') (padPacket hL R)
  have hA : PacketEqv A' (padPacket hKK A) := by
    intro i
    change coeffAt (padPacket hN P) i.val ≈ coeffAt A i.val
    simp only [A, padTrivalentFirst, coeffAt_padPacket]
    exact Q'.eqv_refl _
  have hB : PacketEqv B' (padPacket hKK B) := by
    intro i
    change coeffAt (padPacket hM Q) i.val ≈ coeffAt B i.val
    simp only [B, padTrivalentSecond, coeffAt_padPacket]
    exact Q'.eqv_refl _
  have hC : PacketEqv C' (padPacket hKK C) := by
    intro i
    change coeffAt (padPacket hL R) i.val ≈ coeffAt C i.val
    simp only [C, padTrivalentThird, coeffAt_padPacket]
    exact Q'.eqv_refl _
  change TrivalentVertexEqv (trivalentVertexPacket A' B' C')
    (padPacket
        (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 hKK))
        (trivalentVertexPacket A B C).1,
      padPacket
        (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 hKK))
        (trivalentVertexPacket A B C).2)
  exact vertexEqv_trans (trivalentVertexPacket_congr hA hB hC)
    (trivalentVertexPacket_pad hKK A B C)

/-- The arbitrary-cutoff carrier closes under association. -/
theorem arbitraryTrivalent_association_closure {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    PacketEqv (arbitraryTrivalentVertexPacket P Q R).1
      (arbitraryTrivalentVertexPacket P Q R).2 :=
  trivalent_association_closure _ _ _

/-- Both tree syntheses of the unequal-cutoff vertex are the corresponding
ordinary triple products of the three canonically padded input packets. -/
theorem arbitraryTrivalent_synthesis_vertex {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    PolyEqv (synthesis (arbitraryTrivalentVertexPacket P Q R).1)
      (pmul
        (pmul (synthesis (padTrivalentFirst (M := M) (L := L) P))
          (synthesis (padTrivalentSecond (N := N) (L := L) Q)))
        (synthesis (padTrivalentThird (N := N) (M := M) R))) ∧
    PolyEqv (synthesis (arbitraryTrivalentVertexPacket P Q R).2)
      (pmul
        (synthesis (padTrivalentFirst (M := M) (L := L) P))
        (pmul (synthesis (padTrivalentSecond (N := N) (L := L) Q))
          (synthesis (padTrivalentThird (N := N) (M := M) R)))) :=
  ⟨leftAssociated_synthesis _ _ _, rightAssociated_synthesis _ _ _⟩

/-- Orientation reversal for unequal original cutoffs, represented at the
same canonical three-leg cutoff so no transport equality is hidden in a type
cast. -/
def arbitraryTrivalentOrientationReverse {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) : TrivalentVertexPacket (trivalentCutoff N M L) :=
  trivalentVertexPacket (padTrivalentThird (N := N) (M := M) R)
    (padTrivalentSecond (N := N) (L := L) Q)
    (padTrivalentFirst (M := M) (L := L) P)

theorem arbitraryTrivalent_orientation_reversal {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    TrivalentVertexEqv (arbitraryTrivalentVertexPacket P Q R)
      (arbitraryTrivalentOrientationReverse P Q R) :=
  trivalent_orientation_reversal _ _ _

/-! ## Cross-tree Gram and completed transfer -/

/-- Interacting Gram between the two association trees of the same vertex. -/
def arbitraryTrivalentCrossGram {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) : Q' :=
  packetWilsonGram (arbitraryTrivalentVertexPacket P Q R).1
    (arbitraryTrivalentVertexPacket P Q R).2

/-- Association closure identifies the cross-tree Gram with the exact norm of
the left tree. -/
theorem arbitraryTrivalentCrossGram_eq_left {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    arbitraryTrivalentCrossGram P Q R ≈
      packetWilsonGram (arbitraryTrivalentVertexPacket P Q R).1
        (arbitraryTrivalentVertexPacket P Q R).1 := by
  unfold arbitraryTrivalentCrossGram
  exact packetWilsonGram_congr (packetEqv_refl _)
    (packetEqv_symm (arbitraryTrivalent_association_closure P Q R))

def arbitraryTrivalentStage {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) : StagedPacket × StagedPacket :=
  (stagePacket (arbitraryTrivalentVertexPacket P Q R).1,
    stagePacket (arbitraryTrivalentVertexPacket P Q R).2)

private theorem stagedGram_stagePacket {K : Nat}
    (A B : CharacterPacket K) :
    stagedGram (stagePacket A) (stagePacket B) ≈ packetWilsonGram A B := by
  refine Q'.eqv_trans _
    (packetWilsonGram (padPacket (Nat.le_refl K) A)
      (padPacket (Nat.le_refl K) B)) _
    (stagedGram_pad_to (stagePacket A) (stagePacket B)
      (Nat.le_refl K) (Nat.le_refl K)) ?_
  exact packetWilsonGram_congr (padPacket_refl A) (padPacket_refl B)

/-- The dense colimit form between the two trees is exactly the interacting
trivalent cross Gram. -/
theorem arbitraryTrivalentStage_cross_gram {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    packetColimitGNS.B (arbitraryTrivalentStage P Q R).1
      (arbitraryTrivalentStage P Q R).2 ≈
        arbitraryTrivalentCrossGram P Q R := by
  exact stagedGram_stagePacket (arbitraryTrivalentVertexPacket P Q R).1
    (arbitraryTrivalentVertexPacket P Q R).2

def completedArbitraryTrivalentState {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    GNSCompletionSpace packetColimitGNS ×
      GNSCompletionSpace packetColimitGNS :=
  (embedV packetColimitGNS (arbitraryTrivalentStage P Q R).1,
    embedV packetColimitGNS (arbitraryTrivalentStage P Q R).2)

private theorem embedV_eq_of_veq (D : GNSData) {a b : D.V}
    (h : D.veq a b) : embedV D a = embedV D b := by
  apply Quotient.sound
  exact embed_null_of_rad D (rad_of_veq D h)

/-- The two association components become literally equal in the constructive
GNS completion. -/
theorem completedArbitraryTrivalent_association {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    (completedArbitraryTrivalentState P Q R).1 =
      (completedArbitraryTrivalentState P Q R).2 := by
  apply embedV_eq_of_veq packetColimitGNS
  intro s
  exact coeffAt_packetEqv
    (arbitraryTrivalent_association_closure P Q R) s

/-- Independent enlargement of all three leg cutoffs leaves the completed
two-tree vertex literally unchanged. -/
theorem completedArbitraryTrivalentState_pad_independent
    {N N' M M' L L' : Nat}
    (hN : N ≤ N') (hM : M ≤ M') (hL : L ≤ L')
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    completedArbitraryTrivalentState (padPacket hN P)
        (padPacket hM Q) (padPacket hL R) =
      completedArbitraryTrivalentState P Q R := by
  have hv := arbitraryTrivalentVertexPacket_pad_independent
    hN hM hL P Q R
  apply Prod.ext
  · apply embedV_eq_of_veq packetColimitGNS
    intro s
    refine Q'.eqv_trans _
      (coeffAt
        (padPacket
          (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2
            (trivalentCutoff_mono hN hM hL)))
          (arbitraryTrivalentVertexPacket P Q R).1) s) _ ?_ ?_
    · exact coeffAt_packetEqv hv.1 s
    · rw [coeffAt_padPacket]
      exact Q'.eqv_refl _
  · apply embedV_eq_of_veq packetColimitGNS
    intro s
    refine Q'.eqv_trans _
      (coeffAt
        (padPacket
          (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2
            (trivalentCutoff_mono hN hM hL)))
          (arbitraryTrivalentVertexPacket P Q R).2) s) _ ?_ ?_
    · exact coeffAt_packetEqv hv.2 s
    · rw [coeffAt_padPacket]
      exact Q'.eqv_refl _

def completedTrivalentTransfer
    (x : GNSCompletionSpace packetColimitGNS ×
      GNSCompletionSpace packetColimitGNS) :
    GNSCompletionSpace packetColimitGNS ×
      GNSCompletionSpace packetColimitGNS :=
  (completedPacketTransfer x.1, completedPacketTransfer x.2)

/-- One simultaneous physical transfer acts on both association trees of the
completed trivalent vertex. -/
theorem completedArbitraryTrivalentState_transfer {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    completedTrivalentTransfer (completedArbitraryTrivalentState P Q R) =
      (embedV packetColimitGNS
          (stagePacket (packetTransfer
            (arbitraryTrivalentVertexPacket P Q R).1)),
        embedV packetColimitGNS
          (stagePacket (packetTransfer
            (arbitraryTrivalentVertexPacket P Q R).2))) := by
  apply Prod.ext
  · exact completedPacketTransfer_embed (arbitraryTrivalentStage P Q R).1
  · exact completedPacketTransfer_embed (arbitraryTrivalentStage P Q R).2

private theorem packetTransfer_congr {K : Nat}
    {P Q : CharacterPacket K} (h : PacketEqv P Q) :
    PacketEqv (packetTransfer P) (packetTransfer Q) := by
  intro i
  exact Q'.mul_eqv_congr_left (packetEigen i.val) _ _ (h i)

/-- Association and orientation quotient relations both survive the physical
transfer, so the completed action descends through the trivalent quotient. -/
theorem arbitraryTrivalent_transfer_quotient {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    PacketEqv
      (packetTransfer (arbitraryTrivalentVertexPacket P Q R).1)
      (packetTransfer (arbitraryTrivalentVertexPacket P Q R).2) :=
  packetTransfer_congr (arbitraryTrivalent_association_closure P Q R)

/-- Full orientation reversal also commutes with transfer on both association
components simultaneously. -/
theorem arbitraryTrivalent_transfer_orientation {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    TrivalentVertexEqv
      (packetTransfer (arbitraryTrivalentVertexPacket P Q R).1,
        packetTransfer (arbitraryTrivalentVertexPacket P Q R).2)
      (packetTransfer (arbitraryTrivalentOrientationReverse P Q R).1,
        packetTransfer (arbitraryTrivalentOrientationReverse P Q R).2) :=
  ⟨packetTransfer_congr (arbitraryTrivalent_orientation_reversal P Q R).1,
    packetTransfer_congr (arbitraryTrivalent_orientation_reversal P Q R).2⟩

/-- Bundled trivalent certificate: unrelated cutoff growth, association
closure, cross-tree Gram identification, and transfer descent all hold for the
same three-leg carrier. -/
theorem trivalent_vertex_quotient_compatible
    {N N' M M' L L' : Nat}
    (hN : N ≤ N') (hM : M ≤ M') (hL : L ≤ L')
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    TrivalentVertexEqv
      (arbitraryTrivalentVertexPacket (padPacket hN P)
        (padPacket hM Q) (padPacket hL R))
      (padPacket
          (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2
            (trivalentCutoff_mono hN hM hL)))
          (arbitraryTrivalentVertexPacket P Q R).1,
        padPacket
          (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2
            (trivalentCutoff_mono hN hM hL)))
          (arbitraryTrivalentVertexPacket P Q R).2) ∧
    PacketEqv (arbitraryTrivalentVertexPacket P Q R).1
      (arbitraryTrivalentVertexPacket P Q R).2 ∧
    arbitraryTrivalentCrossGram P Q R ≈
      packetWilsonGram (arbitraryTrivalentVertexPacket P Q R).1
        (arbitraryTrivalentVertexPacket P Q R).1 ∧
    PacketEqv
      (packetTransfer (arbitraryTrivalentVertexPacket P Q R).1)
      (packetTransfer (arbitraryTrivalentVertexPacket P Q R).2) := by
  exact ⟨arbitraryTrivalentVertexPacket_pad_independent hN hM hL P Q R,
    arbitraryTrivalent_association_closure P Q R,
    arbitraryTrivalentCrossGram_eq_left P Q R,
    arbitraryTrivalent_transfer_quotient P Q R⟩

end YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility

#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.fusionHaar_basis_right
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.barePairing_eq_fusionHaar
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.packetEqv_of_synthesis
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.synthesis_padPacket
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.leftAssociated_synthesis
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.rightAssociated_synthesis
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.trivalent_association_closure
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.trivalentFundamental_multiplicity
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.trivalent_orientation_reversal
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.trivalentVertexPacket_congr
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.trivalentVertexPacket_pad
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.arbitraryTrivalentVertexPacket_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.arbitraryTrivalent_association_closure
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.arbitraryTrivalent_synthesis_vertex
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.arbitraryTrivalent_orientation_reversal
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.arbitraryTrivalentCrossGram_eq_left
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.arbitraryTrivalentStage_cross_gram
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.completedArbitraryTrivalent_association
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.completedArbitraryTrivalentState_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.completedArbitraryTrivalentState_transfer
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.arbitraryTrivalent_transfer_quotient
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.arbitraryTrivalent_transfer_orientation
#print axioms YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility.trivalent_vertex_quotient_compatible
