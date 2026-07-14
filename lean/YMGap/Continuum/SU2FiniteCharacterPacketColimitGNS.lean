/-
# GNS module on the finite-character packet colimit

This file equips the staged finite-support carrier with exact addition,
negation and rational scaling across unequal cutoffs.  The interacting Wilson
Gram is evaluated after padding both arguments to their common cutoff.  The
result is a constructive `GNSData`: all module laws hold modulo the staged
coefficient equivalence, the form is bilinear and symmetric, and positivity is
the already-derived finite-packet Wilson positivity.

Thus the algebraic colimit is now accepted by the general GNS quotient and
completion machinery.  This does not assert that its metric completion has
already been identified with the full four-dimensional field algebra.
-/

import YMGap.Continuum.SU2FiniteCharacterPacketColimit

namespace YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit

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

/-! ## Staged linear operations -/

def zeroPacket (N : Nat) : CharacterPacket N where
  coeff _ := 0

def stagedZero : StagedPacket := ⟨0, zeroPacket 0⟩

def stagedAdd (A B : StagedPacket) : StagedPacket :=
  let K := Nat.max A.cutoff B.cutoff
  { cutoff := K
    packet :=
      { coeff := fun i => coeffAt A.packet i.val + coeffAt B.packet i.val } }

def stagedNeg (A : StagedPacket) : StagedPacket :=
  { cutoff := A.cutoff
    packet := { coeff := fun i => -(A.packet.coeff i) } }

def stagedSmul (q : Q') (A : StagedPacket) : StagedPacket :=
  { cutoff := A.cutoff
    packet := { coeff := fun i => q * A.packet.coeff i } }

theorem coeffAt_stagedZero (s : Nat) :
    coeffAt stagedZero.packet s ≈ 0 := by
  by_cases hs : s < 1
  · have hs0 : s = 0 := by omega
    subst hs0
    exact Q'.eqv_refl 0
  · unfold coeffAt stagedZero zeroPacket
    rw [dif_neg hs]
    exact Q'.eqv_refl 0

theorem coeffAt_stagedAdd (A B : StagedPacket) (s : Nat) :
    coeffAt (stagedAdd A B).packet s ≈
      coeffAt A.packet s + coeffAt B.packet s := by
  by_cases hsK : s < Nat.max A.cutoff B.cutoff + 1
  · rw [coeffAt_of_lt (stagedAdd A B).packet hsK]
    exact Q'.eqv_refl _
  · have hsA : ¬ s < A.cutoff + 1 := by
      intro hs
      exact hsK (Nat.lt_of_lt_of_le hs
        (Nat.add_le_add_right (Nat.le_max_left _ _) 1))
    have hsB : ¬ s < B.cutoff + 1 := by
      intro hs
      exact hsK (Nat.lt_of_lt_of_le hs
        (Nat.add_le_add_right (Nat.le_max_right _ _) 1))
    unfold coeffAt stagedAdd
    rw [dif_neg hsK, dif_neg hsA, dif_neg hsB]
    exact Q'.eqv_symm (q_zero_add_eqv 0)

theorem coeffAt_stagedNeg (A : StagedPacket) (s : Nat) :
    coeffAt (stagedNeg A).packet s ≈ -(coeffAt A.packet s) := by
  by_cases hs : s < A.cutoff + 1
  · rw [coeffAt_of_lt (stagedNeg A).packet hs,
      coeffAt_of_lt A.packet hs]
    exact Q'.eqv_refl _
  · unfold coeffAt stagedNeg
    rw [dif_neg hs, dif_neg hs]
    decide

theorem coeffAt_stagedSmul (q : Q') (A : StagedPacket) (s : Nat) :
    coeffAt (stagedSmul q A).packet s ≈ q * coeffAt A.packet s := by
  by_cases hs : s < A.cutoff + 1
  · rw [coeffAt_of_lt (stagedSmul q A).packet hs,
      coeffAt_of_lt A.packet hs]
    exact Q'.eqv_refl _
  · unfold coeffAt stagedSmul
    rw [dif_neg hs, dif_neg hs]
    exact Q'.eqv_symm (Q'.mul_zero_eqv q)

theorem stagedAdd_congr {A A' B B' : StagedPacket}
    (hA : StagedEqv A A') (hB : StagedEqv B B') :
    StagedEqv (stagedAdd A B) (stagedAdd A' B') := by
  intro s
  exact Q'.eqv_trans _ (coeffAt A.packet s + coeffAt B.packet s) _
    (coeffAt_stagedAdd A B s)
    (Q'.eqv_trans _
      (coeffAt A'.packet s + coeffAt B'.packet s) _
      (Q'.add_eqv_congr' (hA s) (hB s))
      (Q'.eqv_symm (coeffAt_stagedAdd A' B' s)))

theorem stagedNeg_congr {A A' : StagedPacket} (hA : StagedEqv A A') :
    StagedEqv (stagedNeg A) (stagedNeg A') := by
  intro s
  exact Q'.eqv_trans _ (-(coeffAt A.packet s)) _
    (coeffAt_stagedNeg A s)
    (Q'.eqv_trans _ (-(coeffAt A'.packet s)) _
      (Q'.neg_eqv_congr _ _ (hA s))
      (Q'.eqv_symm (coeffAt_stagedNeg A' s)))

theorem stagedSmul_congr (q : Q') {A A' : StagedPacket}
    (hA : StagedEqv A A') : StagedEqv (stagedSmul q A) (stagedSmul q A') := by
  intro s
  exact Q'.eqv_trans _ (q * coeffAt A.packet s) _
    (coeffAt_stagedSmul q A s)
    (Q'.eqv_trans _ (q * coeffAt A'.packet s) _
      (Q'.mul_eqv_congr_left q _ _ (hA s))
      (Q'.eqv_symm (coeffAt_stagedSmul q A' s)))

theorem stagedAdd_assoc (A B C : StagedPacket) :
    StagedEqv (stagedAdd (stagedAdd A B) C)
      (stagedAdd A (stagedAdd B C)) := by
  intro s
  refine Q'.eqv_trans _
    (coeffAt (stagedAdd A B).packet s + coeffAt C.packet s) _
    (coeffAt_stagedAdd (stagedAdd A B) C s) ?_
  refine Q'.eqv_trans _
    ((coeffAt A.packet s + coeffAt B.packet s) + coeffAt C.packet s) _
    (Q'.add_eqv_congr_right _ _ _ (coeffAt_stagedAdd A B s)) ?_
  refine Q'.eqv_trans _
    (coeffAt A.packet s +
      (coeffAt B.packet s + coeffAt C.packet s)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (coeffAt A.packet s + coeffAt (stagedAdd B C).packet s) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (coeffAt_stagedAdd B C s))) ?_
  exact Q'.eqv_symm (coeffAt_stagedAdd A (stagedAdd B C) s)

theorem stagedAdd_comm (A B : StagedPacket) :
    StagedEqv (stagedAdd A B) (stagedAdd B A) := by
  intro s
  exact Q'.eqv_trans _ (coeffAt A.packet s + coeffAt B.packet s) _
    (coeffAt_stagedAdd A B s)
    (Q'.eqv_trans _ (coeffAt B.packet s + coeffAt A.packet s) _
      (Q'.add_comm_eqv _ _)
      (Q'.eqv_symm (coeffAt_stagedAdd B A s)))

theorem stagedZero_add (A : StagedPacket) :
    StagedEqv (stagedAdd stagedZero A) A := by
  intro s
  exact Q'.eqv_trans _ (coeffAt stagedZero.packet s + coeffAt A.packet s) _
    (coeffAt_stagedAdd stagedZero A s)
    (Q'.eqv_trans _ (0 + coeffAt A.packet s) _
      (Q'.add_eqv_congr_right _ _ _ (coeffAt_stagedZero s))
      (q_zero_add_eqv _))

theorem stagedNeg_add (A : StagedPacket) :
    StagedEqv (stagedAdd (stagedNeg A) A) stagedZero := by
  intro s
  refine Q'.eqv_trans _
    (coeffAt (stagedNeg A).packet s + coeffAt A.packet s) _
    (coeffAt_stagedAdd (stagedNeg A) A s) ?_
  refine Q'.eqv_trans _
    (-(coeffAt A.packet s) + coeffAt A.packet s) _
    (Q'.add_eqv_congr_right _ _ _ (coeffAt_stagedNeg A s)) ?_
  refine Q'.eqv_trans _ 0 _
    (Q'.eqv_trans _
      (coeffAt A.packet s + -(coeffAt A.packet s)) _
      (Q'.add_comm_eqv _ _) (q_add_neg_self _)) ?_
  exact Q'.eqv_symm (coeffAt_stagedZero s)

/-! ## Fixed-cutoff form linearity -/

theorem coeffAt_packetAdd {N : Nat} (P Q : CharacterPacket N) (s : Nat) :
    coeffAt (packetAdd P Q) s ≈ coeffAt P s + coeffAt Q s := by
  by_cases hs : s < N + 1
  · rw [coeffAt_of_lt (packetAdd P Q) hs, coeffAt_of_lt P hs,
      coeffAt_of_lt Q hs]
    exact Q'.eqv_refl _
  · unfold coeffAt
    rw [dif_neg hs, dif_neg hs, dif_neg hs]
    exact Q'.eqv_symm (q_zero_add_eqv 0)

theorem coeffAt_packetScale {N : Nat} (q : Q')
    (P : CharacterPacket N) (s : Nat) :
    coeffAt (SU2CharacterVacuumHaar.packetScale q P) s ≈
      q * coeffAt P s := by
  by_cases hs : s < N + 1
  · rw [coeffAt_of_lt (SU2CharacterVacuumHaar.packetScale q P) hs,
      coeffAt_of_lt P hs]
    exact Q'.eqv_refl _
  · unfold coeffAt
    rw [dif_neg hs, dif_neg hs]
    exact Q'.eqv_symm (Q'.mul_zero_eqv q)

theorem packetWilsonGram_add_left {N : Nat}
    (P Q R : CharacterPacket N) :
    packetWilsonGram (packetAdd P Q) R ≈
      packetWilsonGram P R + packetWilsonGram Q R := by
  let f := fun s => packetEigen s * (coeffAt P s * coeffAt R s)
  let g := fun s => packetEigen s * (coeffAt Q s * coeffAt R s)
  refine Q'.eqv_trans _
    (fsum (fun s => packetEigen s *
      (coeffAt (packetAdd P Q) s * coeffAt R s)) (N + 1)) _
    (packetWilsonGram_diagonal (packetAdd P Q) R) ?_
  refine Q'.eqv_trans _ (fsum (fun s => f s + g s) (N + 1)) _ ?_ ?_
  · exact YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      Q'.eqv_trans _
        (packetEigen s *
          ((coeffAt P s + coeffAt Q s) * coeffAt R s)) _
        (Q'.mul_eqv_congr_left (packetEigen s) _ _
          (Q'.mul_eqv_congr_right _ _ _ (coeffAt_packetAdd P Q s)))
        (by
          change packetEigen s *
              ((coeffAt P s + coeffAt Q s) * coeffAt R s) ≈
            packetEigen s * (coeffAt P s * coeffAt R s) +
              packetEigen s * (coeffAt Q s * coeffAt R s)
          ring_qeqv)) (N + 1)
  · refine Q'.eqv_trans _ (fsum f (N + 1) + fsum g (N + 1)) _
      (YMGap.Continuum.CubeRatioBounds.fsum_add f g (N + 1)) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm (packetWilsonGram_diagonal P R))
      (Q'.eqv_symm (packetWilsonGram_diagonal Q R))

theorem packetWilsonGram_scale_left {N : Nat} (q : Q')
    (P R : CharacterPacket N) :
    packetWilsonGram (SU2CharacterVacuumHaar.packetScale q P) R ≈
      q * packetWilsonGram P R := by
  let f := fun s => packetEigen s * (coeffAt P s * coeffAt R s)
  refine Q'.eqv_trans _
    (fsum (fun s => packetEigen s *
      (coeffAt (SU2CharacterVacuumHaar.packetScale q P) s *
        coeffAt R s)) (N + 1)) _
    (packetWilsonGram_diagonal
      (SU2CharacterVacuumHaar.packetScale q P) R) ?_
  refine Q'.eqv_trans _ (fsum (fun s => q * f s) (N + 1)) _ ?_ ?_
  · exact YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      Q'.eqv_trans _
        (packetEigen s * ((q * coeffAt P s) * coeffAt R s)) _
        (Q'.mul_eqv_congr_left (packetEigen s) _ _
          (Q'.mul_eqv_congr_right _ _ _ (coeffAt_packetScale q P s)))
        (by
          change packetEigen s * ((q * coeffAt P s) * coeffAt R s) ≈
            q * (packetEigen s * (coeffAt P s * coeffAt R s))
          ring_qeqv)) (N + 1)
  · refine Q'.eqv_trans _ (q * fsum f (N + 1)) _
      (Q'.eqv_symm
        (YMGap.Continuum.CubeRatioBounds.fsum_const_mul q f (N + 1))) ?_
    exact Q'.mul_eqv_congr_left q _ _
      (Q'.eqv_symm (packetWilsonGram_diagonal P R))

/-! ## The common-cutoff interacting form -/

def stagedGram (A B : StagedPacket) : Q' :=
  packetWilsonGram
    (padPacket (Nat.le_max_left A.cutoff B.cutoff) A.packet)
    (padPacket (Nat.le_max_right A.cutoff B.cutoff) B.packet)

/-- The common-cutoff form may be evaluated at any larger shared cutoff. -/
theorem stagedGram_pad_to (A B : StagedPacket) {K : Nat}
    (hA : A.cutoff ≤ K) (hB : B.cutoff ≤ K) :
    stagedGram A B ≈
      packetWilsonGram (padPacket hA A.packet) (padPacket hB B.packet) := by
  let J := Nat.max A.cutoff B.cutoff
  have hAJ : A.cutoff ≤ J := Nat.le_max_left _ _
  have hBJ : B.cutoff ≤ J := Nat.le_max_right _ _
  have hJK : J ≤ K := (Nat.max_le).2 ⟨hA, hB⟩
  let PA := padPacket hAJ A.packet
  let PB := padPacket hBJ B.packet
  refine Q'.eqv_trans _
    (packetWilsonGram (padPacket hJK PA) (padPacket hJK PB)) _ ?_ ?_
  · exact Q'.eqv_symm (packetWilsonGram_pad hJK PA PB)
  · exact packetWilsonGram_congr
      (by simpa only [PA, J, hAJ] using padPacket_trans hAJ hJK A.packet)
      (by simpa only [PB, J, hBJ] using padPacket_trans hBJ hJK B.packet)

theorem stagedGram_congr_left {A A' : StagedPacket} (B : StagedPacket)
    (hAA : StagedEqv A A') : stagedGram A B ≈ stagedGram A' B := by
  let K := Nat.max A.cutoff (Nat.max A'.cutoff B.cutoff)
  have hA : A.cutoff ≤ K := Nat.le_max_left _ _
  have hA' : A'.cutoff ≤ K :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hB : B.cutoff ≤ K :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hpad : PacketEqv (padPacket hA A.packet) (padPacket hA' A'.packet) := by
    intro i
    change coeffAt A.packet i.val ≈ coeffAt A'.packet i.val
    exact hAA i.val
  exact Q'.eqv_trans _
    (packetWilsonGram (padPacket hA A.packet) (padPacket hB B.packet)) _
    (stagedGram_pad_to A B hA hB)
    (Q'.eqv_trans _
      (packetWilsonGram (padPacket hA' A'.packet) (padPacket hB B.packet)) _
      (packetWilsonGram_congr hpad (fun _ => Q'.eqv_refl _))
      (Q'.eqv_symm (stagedGram_pad_to A' B hA' hB)))

theorem pad_stagedAdd {A B : StagedPacket} {K : Nat}
    (hA : A.cutoff ≤ K) (hB : B.cutoff ≤ K) :
    PacketEqv
      (padPacket ((Nat.max_le).2 ⟨hA, hB⟩) (stagedAdd A B).packet)
      (packetAdd (padPacket hA A.packet) (padPacket hB B.packet)) := by
  intro i
  change coeffAt (stagedAdd A B).packet i.val ≈
    coeffAt A.packet i.val + coeffAt B.packet i.val
  exact coeffAt_stagedAdd A B i.val

theorem pad_stagedSmul (q : Q') {A : StagedPacket} {K : Nat}
    (hA : A.cutoff ≤ K) :
    PacketEqv (padPacket hA (stagedSmul q A).packet)
      (SU2CharacterVacuumHaar.packetScale q (padPacket hA A.packet)) := by
  intro i
  change coeffAt (stagedSmul q A).packet i.val ≈ q * coeffAt A.packet i.val
  exact coeffAt_stagedSmul q A i.val

theorem stagedGram_add_left (A B C : StagedPacket) :
    stagedGram (stagedAdd A B) C ≈ stagedGram A C + stagedGram B C := by
  let K := Nat.max (Nat.max A.cutoff B.cutoff) C.cutoff
  have hAB : Nat.max A.cutoff B.cutoff ≤ K := Nat.le_max_left _ _
  have hC : C.cutoff ≤ K := Nat.le_max_right _ _
  have hA : A.cutoff ≤ K := Nat.le_trans (Nat.le_max_left _ _) hAB
  have hB : B.cutoff ≤ K := Nat.le_trans (Nat.le_max_right _ _) hAB
  refine Q'.eqv_trans _
    (packetWilsonGram
      (padPacket hAB (stagedAdd A B).packet) (padPacket hC C.packet)) _
    (stagedGram_pad_to (stagedAdd A B) C hAB hC) ?_
  refine Q'.eqv_trans _
    (packetWilsonGram
      (packetAdd (padPacket hA A.packet) (padPacket hB B.packet))
      (padPacket hC C.packet)) _
    (packetWilsonGram_congr (pad_stagedAdd hA hB)
      (fun _ => Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _
    (packetWilsonGram (padPacket hA A.packet) (padPacket hC C.packet) +
      packetWilsonGram (padPacket hB B.packet) (padPacket hC C.packet)) _
    (packetWilsonGram_add_left _ _ _) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_symm (stagedGram_pad_to A C hA hC))
    (Q'.eqv_symm (stagedGram_pad_to B C hB hC))

theorem stagedGram_smul_left (q : Q') (A B : StagedPacket) :
    stagedGram (stagedSmul q A) B ≈ q * stagedGram A B := by
  let K := Nat.max A.cutoff B.cutoff
  have hA : A.cutoff ≤ K := Nat.le_max_left _ _
  have hB : B.cutoff ≤ K := Nat.le_max_right _ _
  refine Q'.eqv_trans _
    (packetWilsonGram
      (padPacket hA (stagedSmul q A).packet) (padPacket hB B.packet)) _
    (stagedGram_pad_to (stagedSmul q A) B hA hB) ?_
  refine Q'.eqv_trans _
    (packetWilsonGram
      (SU2CharacterVacuumHaar.packetScale q (padPacket hA A.packet))
      (padPacket hB B.packet)) _
    (packetWilsonGram_congr (pad_stagedSmul q hA)
      (fun _ => Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _
    (q * packetWilsonGram (padPacket hA A.packet) (padPacket hB B.packet)) _
    (packetWilsonGram_scale_left q _ _) ?_
  exact Q'.mul_eqv_congr_left q _ _
    (Q'.eqv_symm (stagedGram_pad_to A B hA hB))

theorem stagedGram_symm (A B : StagedPacket) :
    stagedGram A B ≈ stagedGram B A := by
  let K := Nat.max A.cutoff B.cutoff
  have hA : A.cutoff ≤ K := Nat.le_max_left _ _
  have hB : B.cutoff ≤ K := Nat.le_max_right _ _
  exact Q'.eqv_trans _
    (packetWilsonGram (padPacket hA A.packet) (padPacket hB B.packet)) _
    (stagedGram_pad_to A B hA hB)
    (Q'.eqv_trans _
      (packetWilsonGram (padPacket hB B.packet) (padPacket hA A.packet)) _
      (packetWilsonGram_symmetric _ _)
      (Q'.eqv_symm (stagedGram_pad_to B A hB hA)))

theorem stagedGram_self_nonneg (A : StagedPacket) :
    (0 : Q') ≤ stagedGram A A := by
  unfold stagedGram
  exact packetWilsonGram_nonneg _

/-- The finitely-supported character colimit as an exact interacting GNS
module datum. -/
def packetColimitGNS : GNSData where
  V := StagedPacket
  veq := StagedEqv
  veq_refl := stagedEqv_refl
  veq_symm := stagedEqv_symm
  veq_trans := stagedEqv_trans
  zero := stagedZero
  add := stagedAdd
  neg := stagedNeg
  smul := stagedSmul
  add_congr := stagedAdd_congr
  neg_congr := stagedNeg_congr
  smul_congr := stagedSmul_congr
  add_assoc := stagedAdd_assoc
  add_comm := stagedAdd_comm
  zero_add := stagedZero_add
  neg_add := stagedNeg_add
  B := stagedGram
  B_congr_left := stagedGram_congr_left
  B_add_left := stagedGram_add_left
  B_smul_left := stagedGram_smul_left
  B_symm := stagedGram_symm
  self_nonneg := stagedGram_self_nonneg

end YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS

#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS.packetWilsonGram_add_left
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS.stagedGram_pad_to
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS.stagedGram_congr_left
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS.stagedGram_add_left
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS.packetColimitGNS
