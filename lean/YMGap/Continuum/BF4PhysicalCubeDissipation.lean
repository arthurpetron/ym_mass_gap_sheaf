/-
# Quantitative dissipation of the actual completed cube transfer

For every vector of the existing reflected completion, its displacement
T x - x has squared norm at most twice <x,x> - <T x,x>. Consequently a
pairing detecting displacement gives a quantitative lower bound on the
same operator's Rayleigh deficit. No spectral theorem or gap input is used.

All assertions concern the fixed anchor w=1/400, extent one. They neither
identify conditional steps with geometric time nor assert a uniform gap.
-/

import YMGap.Continuum.BF4PhysicalCubeCenteredDensity

namespace YMGap.Continuum.BF4PhysicalCubeDissipation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ScaledGNSCompletionEstimates
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeCompletedTransfer
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalCubeCenteringPairing
open YMGap.Continuum.BF4PhysicalCubeSectorVacuum
open YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "B" => cubeReflectedInner
local notation "T" => cubeTransfer
local infix:50 " ≈ " => Q'.eqv

abbrev Rq (q : Q') : RC := Quotient.mk CReal.crealSetoid (CReal.ofQ' q)

theorem rq_nonnegative {q : Q'} (hq : (0 : Q') ≤ q) : RCnonneg (Rq q) :=
  CReal.leEv_of_le (CReal.ofQ'_le_ofQ' hq)

theorem rq_eqv {a b : Q'} (h : a ≈ b) : Rq a = Rq b :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => h))

theorem rq_mul (a b : Q') : RCmul (Rq a) (Rq b) = Rq (a * b) := rfl

theorem cancel_q (q : Q') (hq : (0 : Q') < q) (a b : RC)
    (h : RCle (RCmul a (Rq q)) (RCmul b (Rq q))) : RCle a b := by
  refine Quotient.inductionOn₂ a b ?_ h
  intro A B hab
  exact RCBilinearDifference.cancel_positive_factor q hq (fun _ => Q'.le_refl' _) hab

theorem sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.add_neg_self_eqv _))

theorem sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : -(0 : Q') ≈ 0))
      (Q'.eqv_of_eq (Q'.add_zero' _))))

theorem twice_mul (a : RC) : RCadd a a = RCmul a (Rq 2) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _ (YMGap.Continuum.OSReconstructionProgress.q_two_mul _)
      (Q'.mul_comm_eqv _ _)))

theorem inner_nonnegative (x : CubeReflectedCompletion) : RCnonneg (B x x) :=
  scaledInner_nonnegative D anchorNormalization x

theorem inner_cauchySchwarz (x y : CubeReflectedCompletion) :
    RCle (RCmul (B x y) (B x y)) (RCmul (B x x) (B y y)) :=
  scaledInner_cauchySchwarz D anchorNormalization x y

def displacement (x : CubeReflectedCompletion) : CubeReflectedCompletion :=
  cubeReflectedSub (T x) x

def dissipation (x : CubeReflectedCompletion) : RC := RCsub (B x x) (B (T x) x)

theorem displacement_pairing (x y : CubeReflectedCompletion) :
    B (displacement x) y = RCsub (B (T x) y) (B x y) :=
  cubeReflectedInner_sub_left (T x) x y

theorem displacement_selfAdjoint (x y : CubeReflectedCompletion) :
    B (displacement x) y = B x (displacement y) := by
  rw [displacement_pairing, cubeReflectedInner_symm x (displacement y),
    displacement_pairing, cubeTransfer_selfAdjoint, cubeReflectedInner_symm (T y) x,
    cubeReflectedInner_symm y x]

/-- A displacement is exactly centered at the constructed stationary vacuum. -/
def centeredDisplacement (x : CubeReflectedCompletion) : CubeSectorVacuumComplement :=
  ⟨displacement x, by
    rw [cubeReflectedInner_symm, displacement_pairing, cubeTransfer_selfAdjoint,
      reflectedSectorVacuum_fixed, sub_self]⟩

private theorem difference_regroup (a b c : RC) :
    RCsub (RCsub c b) (RCsub b a) = RCadd (RCsub a b) (RCsub c b) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro repA repB repC
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change (repC.approx n + -repB.approx n) + -(repB.approx n + -repA.approx n) ≈
    (repA.approx n + -repB.approx n) + (repC.approx n + -repB.approx n)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv _)))) ?_
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den]
  simp only [Int.add_mul]
  ac_rfl

/-- This estimate uses only the ACTUAL full-space contraction, with no
finite-support hypothesis and no presumed strict spectral rate. -/
theorem displacement_norm_le_twice_dissipation (x : CubeReflectedCompletion) :
    RCle (B (displacement x) (displacement x))
      (RCadd (dissipation x) (dissipation x)) := by
  have hid := RCBilinearDifference.difference_diagonal cubeReflectedSub B
    cubeReflectedInner_sub_left cubeReflectedInner_symm (T x) x
  rw [cubeReflectedInner_symm x (T x), difference_regroup] at hid
  change B (displacement x) (displacement x) = _ at hid
  rw [hid]
  exact RCadd_le_add (RCle_refl _)
    (RCadd_le_add (cubeTransfer_contraction x) (RCle_refl _))

/-- A bounded test controls the displacement pairing by this same Rayleigh
deficit. All vectors are in the original completed reflected carrier. -/
theorem displacement_test_bound (x test : CubeReflectedCompletion) (ceiling : Q')
    (hceiling : (0 : Q') ≤ ceiling) (htest : RCle (B test test) (Rq ceiling)) :
    RCle (RCmul (B (displacement x) test) (B (displacement x) test))
      (RCmul (RCadd (dissipation x) (dissipation x)) (Rq ceiling)) :=
  RCle_trans (inner_cauchySchwarz (displacement x) test)
    (RCle_trans (mul_mono_left (inner_nonnegative (displacement x)) htest)
      (mul_mono_right (rq_nonnegative hceiling) (displacement_norm_le_twice_dissipation x)))

theorem positive_test_square {floor : Q'} (hfloor : (0 : Q') ≤ floor) {pairing : RC}
    (hpairing : RCle (Rq floor) pairing) : RCle (Rq (floor * floor)) (RCmul pairing pairing) := by
  have hp := RCle_trans (rq_nonnegative hfloor) hpairing
  exact RCle_trans (mul_mono_left (rq_nonnegative hfloor) hpairing) (mul_mono_right hp hpairing)

theorem mul_assoc (a b c : RC) : RCmul (RCmul a b) c = RCmul a (RCmul b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_assoc_eqv _ _ _))

/-- Explicit rational lower bound, without a square root or real inverse. -/
theorem dissipation_floor_of_test (x test : CubeReflectedCompletion)
    (floor ceiling : Q') (hfloor : (0 : Q') ≤ floor) (hceiling : (0 : Q') < ceiling)
    (htest : RCle (B test test) (Rq ceiling)) (hpairing : RCle (Rq floor) (B (displacement x) test)) :
    RCle (Rq (Q'.divPos (floor * floor) (2 * ceiling) (Q'.mul_pos (by decide) hceiling)))
      (dissipation x) := by
  apply cancel_q (2 * ceiling) (Q'.mul_pos (by decide) hceiling)
  have hexact := rq_eqv (Q'.divPos_mul_eqv (floor * floor) (2 * ceiling)
    (Q'.mul_pos (by decide) hceiling))
  rw [rq_mul, hexact]
  have h := RCle_trans (positive_test_square hfloor hpairing)
    (displacement_test_bound x test ceiling (Q'.le_of_lt hceiling) htest)
  rw [twice_mul, mul_assoc] at h
  exact h

theorem norm_floor_of_test (x test : CubeReflectedCompletion)
    (floor ceiling : Q') (hfloor : (0 : Q') ≤ floor) (hceiling : (0 : Q') < ceiling)
    (htest : RCle (B test test) (Rq ceiling)) (hpairing : RCle (Rq floor) (B x test)) :
    RCle (Rq (Q'.divPos (floor * floor) ceiling hceiling)) (B x x) := by
  apply cancel_q ceiling hceiling
  rw [rq_mul, rq_eqv (Q'.divPos_mul_eqv _ _ _)]
  exact RCle_trans (positive_test_square hfloor hpairing)
    (RCle_trans (inner_cauchySchwarz x test) (mul_mono_left (inner_nonnegative x) htest))

theorem strict_form_of_deficit (x : CubeReflectedCompletion) (floor : Q')
    (hfloor : RCle (Rq floor) (dissipation x)) :
    RCle (RCadd (B (T x) x) (Rq floor)) (B x x) := by
  have h := RCadd_le_add (RCle_refl (B (T x) x)) hfloor
  have heq (a b : RC) : RCadd b (RCsub a b) = a := by
    refine Quotient.inductionOn₂ a b ?_
    intro repA repB
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_symm (Q'.add_sub_cancel_eqv _ _)))
  change RCle _ (RCadd (B (T x) x) (RCsub (B x x) (B (T x) x))) at h
  rw [heq] at h
  exact h

theorem sub_le_of_nonnegative (a b : RC) (hb : RCnonneg b) : RCle (RCsub a b) a := by
  refine Quotient.inductionOn₂ a b ?_ hb
  intro repA repB hB epsilon hepsilon
  obtain ⟨N, hN⟩ := hB epsilon hepsilon
  refine ⟨N, fun n hn => ?_⟩
  have hneg := Q'.neg_le_neg_add (hN n hn)
  change -repB.approx n ≤ (0 : Q') + epsilon at hneg
  rw [Q'.zero_add'] at hneg
  exact Q'.add_le_add_left _ _ _ hneg

theorem dissipation_le_norm (x : CubeReflectedCompletion) : RCle (dissipation x) (B x x) :=
  sub_le_of_nonnegative _ _ (cubeTransfer_positive x)

theorem displacement_norm_ceiling (x : CubeReflectedCompletion) (ceiling : Q')
    (hx : RCle (B x x) (Rq ceiling)) :
    RCle (B (displacement x) (displacement x)) (Rq (ceiling + ceiling)) :=
  RCle_trans (displacement_norm_le_twice_dissipation x)
    (RCadd_le_add (RCle_trans (dissipation_le_norm x) hx) (RCle_trans (dissipation_le_norm x) hx))

end YMGap.Continuum.BF4PhysicalCubeDissipation

#print axioms YMGap.Continuum.BF4PhysicalCubeDissipation.displacement
#print axioms YMGap.Continuum.BF4PhysicalCubeDissipation.dissipation
#print axioms YMGap.Continuum.BF4PhysicalCubeDissipation.displacement_pairing
#print axioms YMGap.Continuum.BF4PhysicalCubeDissipation.displacement_selfAdjoint
#print axioms YMGap.Continuum.BF4PhysicalCubeDissipation.centeredDisplacement
#print axioms YMGap.Continuum.BF4PhysicalCubeDissipation.displacement_norm_le_twice_dissipation
#print axioms YMGap.Continuum.BF4PhysicalCubeDissipation.displacement_test_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeDissipation.positive_test_square
#print axioms YMGap.Continuum.BF4PhysicalCubeDissipation.dissipation_floor_of_test
#print axioms YMGap.Continuum.BF4PhysicalCubeDissipation.norm_floor_of_test
#print axioms YMGap.Continuum.BF4PhysicalCubeDissipation.strict_form_of_deficit
#print axioms YMGap.Continuum.BF4PhysicalCubeDissipation.dissipation_le_norm
#print axioms YMGap.Continuum.BF4PhysicalCubeDissipation.displacement_norm_ceiling
