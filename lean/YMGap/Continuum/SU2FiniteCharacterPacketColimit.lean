/-
# Constructive colimit of finite SU(2) character packets

The cutoff-coherent packet maps are assembled here into an actual quotient
type of finitely supported character sequences.  Representatives may live at
different cutoffs; equality means coefficientwise `Q'.eqv` after zero
extension.  The physical Wilson transfer descends to this colimit, each finite
stage embeds injectively, and padding becomes literal equality in the colimit.

The interacting norm square is also representative-independent as an element
of `QR`, the genuine quotient of `Q'` by rational equivalence.  Finally, the
vacuum-free predicate descends and is transfer-invariant, while every staged
representative retains the exact `1/64` contraction.

This is the algebraic finitely-supported one-link colimit.  Its metric
completion and its extension to overlapping four-dimensional networks remain
separate tasks.
-/

import YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem

namespace YMGap.Continuum.SU2FiniteCharacterPacketColimit

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem

local infix:50 " ≈ " => Q'.eqv

/-- A finite packet together with the cutoff at which it is represented. -/
structure StagedPacket : Type where
  cutoff : Nat
  packet : CharacterPacket cutoff

/-- Equality of staged packets is equality of their full zero-extended
coefficient sequences. -/
def StagedEqv (A B : StagedPacket) : Prop :=
  ∀ s, coeffAt A.packet s ≈ coeffAt B.packet s

theorem stagedEqv_refl (A : StagedPacket) : StagedEqv A A :=
  fun _ => Q'.eqv_refl _

theorem stagedEqv_symm {A B : StagedPacket}
    (hAB : StagedEqv A B) : StagedEqv B A :=
  fun s => Q'.eqv_symm (hAB s)

theorem stagedEqv_trans {A B C : StagedPacket}
    (hAB : StagedEqv A B) (hBC : StagedEqv B C) : StagedEqv A C :=
  fun s => Q'.eqv_trans _ _ _ (hAB s) (hBC s)

def stagedPacketSetoid : Setoid StagedPacket where
  r := StagedEqv
  iseqv := ⟨stagedEqv_refl, stagedEqv_symm, stagedEqv_trans⟩

/-- The algebraic directed colimit of all finite character packets. -/
def PacketColimit : Type := Quotient stagedPacketSetoid

def stagePacket {N : Nat} (P : CharacterPacket N) : StagedPacket :=
  ⟨N, P⟩

/-- Canonical inclusion of any finite cutoff into the colimit. -/
def includePacket {N : Nat} (P : CharacterPacket N) : PacketColimit :=
  Quotient.mk stagedPacketSetoid (stagePacket P)

/-- Padding is identified with the original representative in the colimit. -/
theorem includePacket_pad {N M : Nat} (hNM : N ≤ M)
    (P : CharacterPacket N) :
    includePacket (padPacket hNM P) = includePacket P := by
  apply Quotient.sound
  intro s
  exact Q'.eqv_of_eq (coeffAt_padPacket hNM P s)

/-- Each finite stage embeds injectively modulo its coefficient equivalence. -/
theorem includePacket_injective {N : Nat} {P Q : CharacterPacket N}
    (hinc : includePacket P = includePacket Q) : PacketEqv P Q := by
  have hstage : StagedEqv (stagePacket P) (stagePacket Q) :=
    Quotient.exact hinc
  intro i
  have h := hstage i.val
  change coeffAt P i.val ≈ coeffAt Q i.val at h
  rw [coeffAt_of_lt P i.isLt, coeffAt_of_lt Q i.isLt] at h
  exact h

/-! ## Transfer on the colimit -/

def stagedTransfer (A : StagedPacket) : StagedPacket :=
  ⟨A.cutoff, packetTransfer A.packet⟩

theorem stagedTransfer_congr {A B : StagedPacket}
    (hAB : StagedEqv A B) :
    StagedEqv (stagedTransfer A) (stagedTransfer B) := by
  intro s
  exact Q'.eqv_trans _ (packetEigen s * coeffAt A.packet s) _
    (coeffAt_packetTransfer A.packet s)
    (Q'.eqv_trans _ (packetEigen s * coeffAt B.packet s) _
      (Q'.mul_eqv_congr_left (packetEigen s) _ _ (hAB s))
      (Q'.eqv_symm (coeffAt_packetTransfer B.packet s)))

/-- The exact physical same-state transfer on the finitely-supported colimit. -/
def colimitTransfer : PacketColimit → PacketColimit :=
  Quotient.lift
    (fun A => Quotient.mk stagedPacketSetoid (stagedTransfer A))
    (fun _A _B hAB => Quotient.sound (stagedTransfer_congr hAB))

theorem colimitTransfer_include {N : Nat} (P : CharacterPacket N) :
    colimitTransfer (includePacket P) = includePacket (packetTransfer P) := rfl

/-! ## Representative-independent interacting norm -/

def stagedNormSq (A : StagedPacket) : Q' :=
  packetWilsonGram A.packet A.packet

/-- Norm square is independent of cutoff and representative.  Both packets
are padded to the common maximum cutoff, where coefficient equivalence can be
used by the fixed-cutoff Gram congruence. -/
theorem stagedNormSq_congr {A B : StagedPacket}
    (hAB : StagedEqv A B) : stagedNormSq A ≈ stagedNormSq B := by
  let K := Nat.max A.cutoff B.cutoff
  have hAK : A.cutoff ≤ K := Nat.le_max_left _ _
  have hBK : B.cutoff ≤ K := Nat.le_max_right _ _
  have hpad : PacketEqv (padPacket hAK A.packet) (padPacket hBK B.packet) := by
    intro i
    change coeffAt A.packet i.val ≈ coeffAt B.packet i.val
    exact hAB i.val
  exact Q'.eqv_trans _
    (packetWilsonGram (padPacket hAK A.packet) (padPacket hAK A.packet)) _
    (Q'.eqv_symm (packetWilsonGram_pad hAK A.packet A.packet))
    (Q'.eqv_trans _
      (packetWilsonGram (padPacket hBK B.packet) (padPacket hBK B.packet)) _
      (packetWilsonGram_congr hpad hpad)
      (packetWilsonGram_pad hBK B.packet B.packet))

def stagedNormSqQR (A : StagedPacket) : QR :=
  Quotient.mk qSetoid (stagedNormSq A)

/-- The interacting norm square as a genuine function on the colimit. -/
def colimitNormSq : PacketColimit → QR :=
  Quotient.lift stagedNormSqQR (fun _A _B hAB =>
    Quotient.sound (stagedNormSq_congr hAB))

theorem colimitNormSq_include {N : Nat} (P : CharacterPacket N) :
    colimitNormSq (includePacket P) =
      Quotient.mk qSetoid (packetWilsonGram P P) := rfl

/-! ## Vacuum-free subsystem and its contraction -/

def StagedVacuumFree (A : StagedPacket) : Prop :=
  coeffAt A.packet 0 ≈ 0

theorem stagedVacuumFree_iff {A B : StagedPacket}
    (hAB : StagedEqv A B) : StagedVacuumFree A ↔ StagedVacuumFree B := by
  constructor
  · intro hA
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hAB 0)) hA
  · intro hB
    exact Q'.eqv_trans _ _ _ (hAB 0) hB

/-- Vacuum-freeness is a well-defined predicate on the colimit. -/
def ColimitVacuumFree : PacketColimit → Prop :=
  Quotient.lift StagedVacuumFree (fun _A _B hAB =>
    propext (stagedVacuumFree_iff hAB))

theorem colimitVacuumFree_include {N : Nat} (P : CharacterPacket N) :
    ColimitVacuumFree (includePacket P) ↔ coeffAt P 0 ≈ 0 :=
  Iff.rfl

theorem stagedTransfer_vacuumFree (A : StagedPacket)
    (hA : StagedVacuumFree A) : StagedVacuumFree (stagedTransfer A) := by
  refine Q'.eqv_trans _ (packetEigen 0 * coeffAt A.packet 0) _
    (coeffAt_packetTransfer A.packet 0) ?_
  rw [packetEigen_zero]
  exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) hA

theorem colimitTransfer_vacuumFree (x : PacketColimit)
    (hx : ColimitVacuumFree x) :
    ColimitVacuumFree (colimitTransfer x) := by
  refine Quotient.inductionOn x ?_ hx
  intro A hA
  exact stagedTransfer_vacuumFree A hA

/-- Exact representative-level contraction on the colimit's vacuum-free
carrier.  Its constants are independent of the chosen stage, whose norm class
is certified representative-independent above. -/
theorem staged_vacuumfree_uniform_contraction (A : StagedPacket)
    (hA : StagedVacuumFree A) :
    stagedNormSq (stagedTransfer A) ≤
      (SU2PeterWeylWilsonBlock.eighth *
          SU2PeterWeylWilsonBlock.eighth) * stagedNormSq A :=
  vacuumfree_packet_uniform_contraction A.packet hA

end YMGap.Continuum.SU2FiniteCharacterPacketColimit

#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimit.includePacket_pad
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimit.includePacket_injective
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimit.colimitTransfer
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimit.stagedNormSq_congr
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimit.colimitNormSq
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimit.colimitTransfer_vacuumFree
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimit.staged_vacuumfree_uniform_contraction
