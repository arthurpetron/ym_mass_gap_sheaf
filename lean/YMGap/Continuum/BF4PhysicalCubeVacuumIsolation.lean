/-
# Quantitative isolation of the constructed stationary cube vacuum

The actual strict reflected form bound gives the explicit positive deficit
margin delta=1-q on the ENTIRE vacuum complement. A fixed vector there must
be zero. Hence any two fixed vectors with the same pairing against the
constructed stationary vacuum coincide. In particular its own vacuum
pairing uniquely specifies that stationary vector, whose norm is already
proved positive; unit normalization is neither assumed nor invented.

Scope: SU(2) BF4 conditional dynamics, w=1/400, extent one, the original
completed reflected carrier. This is not identification with signed-Haar
YM or geometric time, and is not continuum or all-group Clay closure.
-/

import YMGap.Continuum.BF4PhysicalCubeCompletedReflectedGap
import YMGap.Continuum.BF4PhysicalCubeMixedTestBound

namespace YMGap.Continuum.BF4PhysicalCubeVacuumIsolation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeCompletedTransfer
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalCubeSectorVacuum
open YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm
open YMGap.Continuum.BF4PhysicalCubeCenteringPairing
open YMGap.Continuum.BF4PhysicalCubeDissipation
open YMGap.Continuum.BF4PhysicalCubeCompletedReflectedGap
open YMGap.Continuum.BF4PhysicalCubeMixedTestBound

local notation "B" => cubeReflectedInner
local notation "T" => cubeTransfer
local notation "Omega" => reflectedSectorVacuum
local notation "zeroV" => cubeReflectedEmbed []
local infix:50 " ≈ " => Q'.eqv

/-- Explicit positive margin below the stationary eigenvalue one. It is
dimensionless; it is NOT a continuum physical mass. -/
def vacuumMargin : Q' := 1 - reflectedGapRate

theorem vacuumMargin_pos : (0 : Q') < vacuumMargin :=
  YMGap.Continuum.ClusteringImpliesGap.sub_pos_of_lt reflectedGapRate_lt_one

private theorem one_sub_mul (r a : Q') : (1 - r) * a ≈ a + -(r * a) :=
  Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-r) a)
    (Q'.add_eqv_congr' (Q'.one_mul_eqv a) (Q'.neg_mul_eqv r a))

private theorem deficit_lower (r : Q') (norm form : RC)
    (h : RCle form (RCmul (Rq r) norm)) :
    RCle (RCmul (Rq (1 - r)) norm) (RCsub norm form) := by
  revert h
  refine Quotient.inductionOn₂ norm form ?_
  intro N F h epsilon hepsilon
  obtain ⟨index, hN⟩ := h epsilon hepsilon
  refine ⟨index, fun n hn => ?_⟩
  have hf := hN n hn
  change F.approx n ≤ r * N.approx n + epsilon at hf
  have hneg := Q'.neg_le_neg_add hf
  have hsum := Q'.add_le_add_left (N.approx n) _ _ hneg
  change (1 - r) * N.approx n ≤ (N.approx n + -F.approx n) + epsilon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (one_sub_mul r (N.approx n)))
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (Q'.add_assoc_eqv _ _ _)))

/-- Every centered vector pays a positive fixed fraction of its ORIGINAL
reflected squared norm in the same operator's one-step deficit. -/
theorem margin_times_norm_le_dissipation (x : CubeSectorVacuumComplement) :
    RCle (RCmul (Rq vacuumMargin) (B x.val x.val)) (dissipation x.val) :=
  deficit_lower reflectedGapRate (B x.val x.val) (B (T x.val) x.val)
    (completed_reflected_form_bound x)

private theorem zero_mul (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv (A.approx n)))

/-- There is no nonzero stationary vector in the completed vacuum
complement. Cancellation uses the explicit rational margin, not a norm
that might vanish. -/
theorem fixed_complement_eq_zero (x : CubeSectorVacuumComplement)
    (hfixed : T x.val = x.val) : x.val = zeroV := by
  have h := margin_times_norm_le_dissipation x
  unfold dissipation at h
  rw [hfixed, sub_self] at h
  have hn : RCle (B x.val x.val) RCzero := by
    apply cancel_q vacuumMargin vacuumMargin_pos
    rw [RCmul_comm (B x.val x.val) (Rq vacuumMargin), zero_mul]
    exact h
  have hzero := RCle_antisymm hn (inner_nonnegative x.val)
  apply eq_zero_of_response_zero x.val
  rw [hfixed, hzero]

/-- Subtraction commutes with the SAME completed operator, proved by
self-adjointness and testing its original bilinear form. -/
theorem transfer_sub (x y : CubeReflectedCompletion) :
    T (cubeReflectedSub x y) = cubeReflectedSub (T x) (T y) := by
  apply cubeReflected_ext_dense
  intro test
  rw [cubeTransfer_selfAdjoint, cubeReflectedInner_sub_left, cubeReflectedInner_sub_left,
    ← cubeTransfer_selfAdjoint x _, ← cubeTransfer_selfAdjoint y _]

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem eq_of_sub_zero (a b : RC) (h : RCsub a b = RCzero) : a = b := by
  have hid : a = RCadd b (RCsub a b) := by
    refine Quotient.inductionOn₂ a b ?_
    intro repA repB
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      Q'.add_sub_cancel_eqv (repA.approx n) (repB.approx n)))
  rw [h, add_zero] at hid
  exact hid

/-- Fixed vectors are uniquely determined by their pairing against the
actual stationary sector vacuum. No choice of a real scalar is required. -/
theorem fixed_vectors_eq_of_vacuum_pairing (x y : CubeReflectedCompletion)
    (hx : T x = x) (hy : T y = y) (hpairing : B Omega x = B Omega y) : x = y := by
  have hcenter : B Omega (cubeReflectedSub x y) = RCzero := by
    rw [cubeReflectedInner_symm, cubeReflectedInner_sub_left,
      cubeReflectedInner_symm x Omega, cubeReflectedInner_symm y Omega, hpairing, sub_self]
  have hfixed : T (cubeReflectedSub x y) = cubeReflectedSub x y := by
    rw [transfer_sub, hx, hy]
  have hz := fixed_complement_eq_zero ⟨cubeReflectedSub x y, hcenter⟩ hfixed
  apply cubeReflected_ext_dense
  intro test
  have hp := congrArg (fun z => B z (cubeReflectedEmbed test)) hz
  dsimp only at hp
  rw [cubeReflectedInner_sub_left, cubeReflectedInner_zero_left] at hp
  exact eq_of_sub_zero _ _ hp

/-- The constructed nonzero vacuum is the UNIQUE stationary vector with
its own vacuum pairing. Its already proved norm floor is not replaced by
an unjustified unit-normalization assertion. -/
theorem stationary_vacuum_unique (x : CubeReflectedCompletion)
    (hfixed : T x = x) (hpairing : B Omega x = B Omega Omega) : x = Omega :=
  fixed_vectors_eq_of_vacuum_pairing x Omega hfixed reflectedSectorVacuum_fixed hpairing

end YMGap.Continuum.BF4PhysicalCubeVacuumIsolation

#print axioms YMGap.Continuum.BF4PhysicalCubeVacuumIsolation.vacuumMargin
#print axioms YMGap.Continuum.BF4PhysicalCubeVacuumIsolation.vacuumMargin_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeVacuumIsolation.margin_times_norm_le_dissipation
#print axioms YMGap.Continuum.BF4PhysicalCubeVacuumIsolation.fixed_complement_eq_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeVacuumIsolation.transfer_sub
#print axioms YMGap.Continuum.BF4PhysicalCubeVacuumIsolation.fixed_vectors_eq_of_vacuum_pairing
#print axioms YMGap.Continuum.BF4PhysicalCubeVacuumIsolation.stationary_vacuum_unique
