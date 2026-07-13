/-
Signed one-crossing absorption for the harmonic compensated Abel defect.

Unlike the older envelope theorem, this file never assumes all terminal
carrier gaps are nonnegative.  A negative initial block is kept with its true
sign and discarded only after proving its product with the positive drift
increment is nonpositive; the symmetric chord envelope is used solely on the
later nonnegative block.
-/

import YMGap.Continuum.HarmonicWeightedAbelReserve

namespace YMGap.Continuum.HarmonicSignedChordAbsorption

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicWeightedAbelReserve
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv
private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

def signedChordCell (k L s p : Nat) : Q' :=
  if s ≤ p then compensatedChordCell k L p else (0 : Q')

def signedChordSum (k L s : Nat) : Q' :=
  fsum (signedChordCell k L s) L

theorem driftSqFactor_increment_nonneg (k p : Nat) :
    (0 : Q') ≤ driftSqFactor k (p + 1) + -(driftSqFactor k p) := by
  have he := driftSqFactor_increment_geom_eqv k p
  have hG : (0 : Q') ≤ driftSqFactor k p := by
    unfold driftSqFactor
    exact Q'.mul_nonneg _ _
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
  have hu := unit_nonneg (driftDen k) (driftDen_pos k)
  have hs := HeatKernelRGStep.geomSum_nonneg
    (Q'.le_of_lt (driftRatio_pos k)) (4 * p + 6)
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ hG (Q'.mul_nonneg _ _ hu hs))
    (Q'.ge_of_eqv he)

private theorem nonpos_of_not_nonneg {a : Q'}
    (h : ¬ ((0 : Q') ≤ a)) : a ≤ (0 : Q') := by
  have hlt : a < (0 : Q') := by
    have hh : ¬ ((0 : Q').num * (a.den : Int) ≤
        a.num * (((0 : Q').den) : Int)) := h
    exact Int.not_le.mp hh
  exact Q'.le_of_lt hlt

/-- Finite constructive first-crossing search for rational carriers. -/
theorem exists_first_nonnegative (C : Nat → Q') : ∀ L,
    (0 : Q') ≤ C L →
      ∃ s, s ≤ L ∧ (0 : Q') ≤ C s ∧
        ∀ p, p < s → C p ≤ (0 : Q')
  | 0, hL => ⟨0, by omega, hL, by omega⟩
  | L + 1, hL => by
      by_cases h0 : (0 : Q') ≤ C 0
      · exact ⟨0, by omega, h0, by omega⟩
      · let C' := fun p => C (p + 1)
        have hlast : (0 : Q') ≤ C' L := by
          simpa [C'] using hL
        obtain ⟨s, hsL, hs0, hsfirst⟩ :=
          exists_first_nonnegative C' L hlast
        refine ⟨s + 1, by omega, ?_, ?_⟩
        · simpa [C'] using hs0
        · intro p hp
          by_cases hp0 : p = 0
          · subst p
            exact nonpos_of_not_nonneg h0
          · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
            simpa [C'] using hsfirst q (by omega)

/-- Every finite harmonic carrier has an exact first nonnegative terminal
gap, because its endpoint gap is identically zero. -/
theorem exists_harmonic_terminal_carrier_crossing (k L : Nat) :
    ∃ s, s ≤ L ∧
      (0 : Q') ≤ trapezoidNodeCumulative k L +
        -(trapezoidNodeCumulative k s) ∧
      ∀ p, p < s →
        trapezoidNodeCumulative k L +
          -(trapezoidNodeCumulative k p) ≤ (0 : Q') := by
  let C := fun p => trapezoidNodeCumulative k L +
    -(trapezoidNodeCumulative k p)
  have hend : (0 : Q') ≤ C L := by
    unfold C
    exact Q'.ge_of_eqv
      (Q'.add_neg_self_eqv (trapezoidNodeCumulative k L))
  exact exists_first_nonnegative C L hend

/-- Once a terminal carrier gap has become nonnegative, it stays
nonnegative.  The proof shifts the already-checked one-crossing carrier
engine to the crossing index `s`; no sign assumption on the increment at
`s + 1` is needed. -/
theorem terminal_carrier_gap_nonneg_from_split
    (k L s : Nat) (hsL : s ≤ L)
    (hboundary : (0 : Q') ≤ trapezoidNodeCumulative k L +
      -(trapezoidNodeCumulative k s))
    {p : Nat} (hsp : s ≤ p) (hpL : p ≤ L) :
    (0 : Q') ≤ trapezoidNodeCumulative k L +
      -(trapezoidNodeCumulative k p) := by
  let T := trapezoidNodeCumulative k
  let q := trapezoidNodeCoeff k
  let Ts := fun n => T (s + n)
  let qs := fun n => q (s + n)
  let Ls := L - s
  have hstep : ∀ i, Ts (i + 1) ≈ Ts i + qs (i + 1) := by
    intro i
    unfold Ts qs T q
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (trapezoidNodeCumulative_succ_eq k (s + i))
  have hglobal : ∀ i j, 1 ≤ i → i ≤ j →
      (0 : Q') ≤ q i → (0 : Q') ≤ q j := by
    intro i j hi1 hij hqi
    obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
    obtain ⟨d, rfl⟩ : ∃ d, j = a + 1 + d :=
      ⟨j - (a + 1), by omega⟩
    exact trapezoidNodeCoeff_sign_forward k a d hqi
  have hsign : ∀ i j, 1 ≤ i → i ≤ j →
      (0 : Q') ≤ qs i → (0 : Q') ≤ qs j := by
    intro i j hi1 hij hqi
    unfold qs q at hqi ⊢
    exact hglobal (s + i) (s + j) (by omega) (by omega) hqi
  have hstart : T s ≤ T L := Q'.le_of_sub_nonneg hboundary
  have hsLs : s + Ls = L := by
    unfold Ls
    omega
  have htotal : Ts 0 ≤ Ts Ls := by
    simpa [Ts, hsLs] using hstart
  let ps := p - s
  have hps : s + ps = p := by
    unfold ps
    omega
  have hpLs : ps ≤ Ls := by
    unfold ps Ls
    omega
  have hdom := terminal_dominates_of_sign_monotone Ts qs Ls
    hstep hsign htotal ps hpLs
  apply Q'.sub_nonneg_of_le
  simpa [Ts, hps, hsLs] using hdom

/-- Signed one-crossing absorption.  The initial carrier-gap block may be
strictly negative (and in particular `T_L<T_0` is allowed).  Only the later
block is required nonnegative and receives the symmetric chord envelope. -/
theorem compensatedAbelDefect_twice_le_signedChord
    (k L s : Nat)
    (hneg : ∀ p, p < L → p < s →
      trapezoidNodeCumulative k L +
        -(trapezoidNodeCumulative k p) ≤ (0 : Q'))
    (hpos : ∀ p, p < L → s ≤ p →
      (0 : Q') ≤ trapezoidNodeCumulative k L +
        -(trapezoidNodeCumulative k p)) :
    compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L +
        compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L ≤
      signedChordSum k L s := by
  let f := fun p =>
    (abelPrefix (trapezoidNodeCoeff k) L +
      -(abelPrefix (trapezoidNodeCoeff k) p)) *
        (driftSqFactor k (p + 1) + -(driftSqFactor k p))
  have hsplit := CubeRatioBounds.fsum_add f f L
  have hsum : fsum (fun p => f p + f p) L ≤ signedChordSum k L s := by
    unfold signedChordSum
    apply CubeRatioBounds.fsum_mono_lt
    intro p hp
    let C := trapezoidNodeCumulative k L +
      -(trapezoidNodeCumulative k p)
    let d := driftSqFactor k (p + 1) + -(driftSqFactor k p)
    have hC : abelPrefix (trapezoidNodeCoeff k) L +
        -(abelPrefix (trapezoidNodeCoeff k) p) ≈ C :=
      Q'.add_eqv_congr'
        (abelPrefix_trapezoidNodeCoeff k L)
        (Q'.neg_eqv_congr _ _ (abelPrefix_trapezoidNodeCoeff k p))
    have hL : f p + f p ≈ C * (d + d) := by
      unfold f d
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ _ hC)
          (Q'.mul_eqv_congr_right _ _ _ hC)) ?_
      ring_qeqv
    unfold signedChordCell
    by_cases hps : s ≤ p
    · rw [if_pos hps]
      have hm := Q'.mul_le_mul_of_nonneg_left _ _ C
        (driftSqFactor_increment_twice_le_chord k p) (hpos p hp hps)
      unfold compensatedChordCell
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) hm
    · rw [if_neg hps]
      have hd0 := driftSqFactor_increment_nonneg k p
      have hdd0 : (0 : Q') ≤ d + d := Q'.zero_le_add _ _ hd0 hd0
      have hrev : (d + d) * C ≤ (0 : Q') :=
        Q'.mul_nonpos_of_nonneg_nonpos hdd0 (hneg p hp (by omega))
      have hcomm : C * (d + d) ≈ (d + d) * C := by
        ring_qeqv
      have hm : C * (d + d) ≤ (0 : Q') :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm) hrev
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) hm
  unfold compensatedAbelDefect
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hsplit)) hsum

/-- Harmonic one-crossing consumer.  It is enough to locate a single carrier
crossing: gaps before `s` are nonpositive and the gap at `s` is
nonnegative.  The proved one-crossing law for harmonic node coefficients
then supplies every later nonnegative gap required by the signed chord
absorption theorem.  In particular the theorem permits a negative initial
gap `T L - T 0`. -/
theorem compensatedAbelDefect_twice_le_signedChord_of_crossing
    (k L s : Nat) (hsL : s ≤ L)
    (hneg : ∀ p, p < L → p < s →
      trapezoidNodeCumulative k L +
        -(trapezoidNodeCumulative k p) ≤ (0 : Q'))
    (hboundary : (0 : Q') ≤ trapezoidNodeCumulative k L +
      -(trapezoidNodeCumulative k s)) :
    compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L +
        compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L ≤
      signedChordSum k L s := by
  apply compensatedAbelDefect_twice_le_signedChord k L s hneg
  intro p hpL hsp
  exact terminal_carrier_gap_nonneg_from_split k L s hsL hboundary hsp
    (by omega)

/-- Fully constructive existential signed envelope.  The crossing index is
obtained by exact rational comparison, so no total-carrier positivity premise
survives. -/
theorem exists_signedChord_envelope (k L : Nat) :
    ∃ s, s ≤ L ∧
      compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L +
          compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L ≤
        signedChordSum k L s := by
  obtain ⟨s, hsL, hs0, hsfirst⟩ :=
    exists_harmonic_terminal_carrier_crossing k L
  refine ⟨s, hsL, ?_⟩
  apply compensatedAbelDefect_twice_le_signedChord_of_crossing k L s hsL
    (fun p _ hp => hsfirst p hp) hs0

#print axioms driftSqFactor_increment_nonneg
#print axioms exists_first_nonnegative
#print axioms exists_harmonic_terminal_carrier_crossing
#print axioms terminal_carrier_gap_nonneg_from_split
#print axioms compensatedAbelDefect_twice_le_signedChord
#print axioms compensatedAbelDefect_twice_le_signedChord_of_crossing
#print axioms exists_signedChord_envelope

end YMGap.Continuum.HarmonicSignedChordAbsorption
