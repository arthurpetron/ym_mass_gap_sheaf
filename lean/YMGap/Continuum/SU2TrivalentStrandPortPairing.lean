/-
# Exact port pairing at an SU(2) trivalent strand resolution

The three counts in `TrivalentStrandResolution`

    a = ca + ab,    b = bc + ab,    c = bc + ca

do more than certify admissibility.  They canonically match every individual
strand copy on one leg with exactly one copy on another leg.  This module
makes those copies into bounded `Type`-level ports and defines the matching
as a fixed-point-free involution.

The allocation is explicit.  On leg `a`, the first `ca` copies pair with the
last `ca` copies of leg `c`, and the remaining `ab` copies pair with the last
`ab` copies of leg `b`; the first `bc` copies of `b` and `c` pair directly.
No finite choice or search is involved.

This local matching is the exact combinatorial input needed to assemble the
resolved slab-link networks into a global stranded incidence graph.  It does
not yet identify equal physical-face copies between different lattice links
or extract a global component.

Constructive contract: natural arithmetic and decidable comparisons only.
No `Classical.*`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.SU2TrivalentStrandPeeling

namespace YMGap.Continuum.SU2TrivalentStrandPortPairing

set_option autoImplicit false

open YMGap.Continuum.SU2TrivalentStrandPeeling

/-! ## 1. Bounded strand-copy ports -/

/-- The three legs of a trivalent vertex. -/
inductive TrivalentLeg : Type
  | a
  | b
  | c
  deriving DecidableEq

/-- The twice-spin label carried by a selected leg. -/
def legSize (a b c : Nat) : TrivalentLeg -> Nat
  | .a => a
  | .b => b
  | .c => c

/-- One distinguishable strand copy on a trivalent leg.  The sum-of-finite-
sets presentation keeps the leg visible in the constructor and its label
bound visible in the `Fin` index. -/
inductive TrivalentStrandPort (a b c : Nat) : Type
  | onA (slot : Fin a)
  | onB (slot : Fin b)
  | onC (slot : Fin c)
  deriving DecidableEq

/-- The leg on which a strand port lies. -/
def TrivalentStrandPort.leg {a b c : Nat} :
    TrivalentStrandPort a b c -> TrivalentLeg
  | .onA _ => .a
  | .onB _ => .b
  | .onC _ => .c

/-- The zero-based copy number on the selected leg. -/
def TrivalentStrandPort.slot {a b c : Nat} :
    TrivalentStrandPort a b c -> Nat
  | .onA slot => slot.val
  | .onB slot => slot.val
  | .onC slot => slot.val

/-- The copy number is bounded by the label of its leg. -/
theorem TrivalentStrandPort.slot_lt_legSize
    {a b c : Nat} (port : TrivalentStrandPort a b c) :
    port.slot < legSize a b c port.leg := by
  cases port <;> exact Fin.isLt _

/-! ## 2. The canonical local mate -/

/-- Match every bounded strand copy to its unique partner on a different
leg, using the three explicit strand bundles. -/
def strandMate
    {a b c : Nat} (resolution : TrivalentStrandResolution a b c)
    (port : TrivalentStrandPort a b c) :
    TrivalentStrandPort a b c :=
  match port with
  | .onA slot =>
      if hca : slot.val < resolution.ca then
        .onC ⟨resolution.bc + slot.val, by
          have hc := resolution.c_balance
          omega⟩
      else
        .onB ⟨resolution.bc + (slot.val - resolution.ca), by
          have ha := resolution.a_balance
          have hb := resolution.b_balance
          omega⟩
  | .onB slot =>
      if hbc : slot.val < resolution.bc then
        .onC ⟨slot.val, by
          have hc := resolution.c_balance
          omega⟩
      else
        .onA ⟨resolution.ca + (slot.val - resolution.bc), by
          have ha := resolution.a_balance
          have hb := resolution.b_balance
          omega⟩
  | .onC slot =>
      if hbc : slot.val < resolution.bc then
        .onB ⟨slot.val, by
          have hb := resolution.b_balance
          omega⟩
      else
        .onA ⟨slot.val - resolution.bc, by
          have ha := resolution.a_balance
          have hc := resolution.c_balance
          omega⟩

/-- The mate always lies on a different trivalent leg. -/
theorem strandMate_leg_ne
    {a b c : Nat} (resolution : TrivalentStrandResolution a b c)
    (port : TrivalentStrandPort a b c) :
    (strandMate resolution port).leg ≠ port.leg := by
  cases port with
  | onA slot =>
      by_cases hca : slot.val < resolution.ca <;>
        simp [strandMate, hca, TrivalentStrandPort.leg]
  | onB slot =>
      by_cases hbc : slot.val < resolution.bc <;>
        simp [strandMate, hbc, TrivalentStrandPort.leg]
  | onC slot =>
      by_cases hbc : slot.val < resolution.bc <;>
        simp [strandMate, hbc, TrivalentStrandPort.leg]

/-- The explicit mate is involutive: every strand copy occurs in exactly one
local pair. -/
theorem strandMate_involutive
    {a b c : Nat} (resolution : TrivalentStrandResolution a b c)
    (port : TrivalentStrandPort a b c) :
    strandMate resolution (strandMate resolution port) = port := by
  cases port with
  | onA slot =>
      by_cases hca : slot.val < resolution.ca
      · have hnot : ¬ resolution.bc + slot.val < resolution.bc := by
          omega
        simp only [strandMate]
        rw [dif_pos hca]
        simp only
        rw [dif_neg hnot]
        congr 1
        apply Fin.ext
        dsimp
        omega
      · have ha := resolution.a_balance
        have hnot :
            ¬ resolution.bc + (slot.val - resolution.ca) <
              resolution.bc := by
          omega
        simp only [strandMate]
        rw [dif_neg hca]
        simp only
        rw [dif_neg hnot]
        congr 1
        apply Fin.ext
        dsimp
        omega
  | onB slot =>
      by_cases hbc : slot.val < resolution.bc
      · simp only [strandMate]
        rw [dif_pos hbc]
        simp only
        rw [dif_pos hbc]
      · have hb := resolution.b_balance
        have hnot :
            ¬ resolution.ca + (slot.val - resolution.bc) <
              resolution.ca := by
          omega
        simp only [strandMate]
        rw [dif_neg hbc]
        simp only
        rw [dif_neg hnot]
        congr 1
        apply Fin.ext
        dsimp
        omega
  | onC slot =>
      by_cases hbc : slot.val < resolution.bc
      · simp only [strandMate]
        rw [dif_pos hbc]
        simp only
        rw [dif_pos hbc]
      · have hc := resolution.c_balance
        have hca : slot.val - resolution.bc < resolution.ca := by
          omega
        simp only [strandMate]
        rw [dif_neg hbc]
        simp only
        rw [dif_pos hca]
        congr 1
        apply Fin.ext
        dsimp
        omega

/-- Consequently no local strand copy is paired with itself. -/
theorem strandMate_ne_self
    {a b c : Nat} (resolution : TrivalentStrandResolution a b c)
    (port : TrivalentStrandPort a b c) :
    strandMate resolution port ≠ port := by
  intro heq
  have hleg := congrArg TrivalentStrandPort.leg heq
  exact strandMate_leg_ne resolution port hleg

/-! ## 3. Canonical pairing of every admissible triple -/

/-- The computable canonical resolution turns every admissible trivalent
triple into its exact fixed-point-free port involution. -/
def canonicalTrivalentPortMate
    (a b c : Nat) (hadmissible :
      YMGap.Continuum.BondMovingStep.fusionOK a b c = true) :
    TrivalentStrandPort a b c -> TrivalentStrandPort a b c :=
  strandMate (canonicalTrivalentStrandResolution a b c hadmissible)

theorem canonicalTrivalentPortMate_involutive
    (a b c : Nat) (hadmissible :
      YMGap.Continuum.BondMovingStep.fusionOK a b c = true)
    (port : TrivalentStrandPort a b c) :
    canonicalTrivalentPortMate a b c hadmissible
        (canonicalTrivalentPortMate a b c hadmissible port) =
      port :=
  strandMate_involutive
    (canonicalTrivalentStrandResolution a b c hadmissible) port

theorem canonicalTrivalentPortMate_ne_self
    (a b c : Nat) (hadmissible :
      YMGap.Continuum.BondMovingStep.fusionOK a b c = true)
    (port : TrivalentStrandPort a b c) :
    canonicalTrivalentPortMate a b c hadmissible port ≠ port :=
  strandMate_ne_self
    (canonicalTrivalentStrandResolution a b c hadmissible) port

#print axioms TrivalentStrandPort
#print axioms TrivalentStrandPort.leg
#print axioms TrivalentStrandPort.slot
#print axioms TrivalentStrandPort.slot_lt_legSize
#print axioms strandMate
#print axioms strandMate_leg_ne
#print axioms strandMate_involutive
#print axioms strandMate_ne_self
#print axioms canonicalTrivalentPortMate
#print axioms canonicalTrivalentPortMate_involutive
#print axioms canonicalTrivalentPortMate_ne_self

end YMGap.Continuum.SU2TrivalentStrandPortPairing
