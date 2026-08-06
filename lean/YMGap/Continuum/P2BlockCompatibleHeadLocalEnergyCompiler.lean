/-
Track 11.7-fusion / R3m -- local-to-global compiler for the physical head
energy.

For a path with adjacent edge energies `E_i` and distance-two energies `J_i`,
the pointwise stencil

  3 E_0       <= J_0,
  3 E_(i+1)   <= J_i + J_(i+1),
  3 E_(M+1)   <= J_M

sums exactly to `3 * sum E <= 2 * sum J`: every distance-two edge is paid
once from each endpoint.  This file proves that finite-path compiler without
any coefficient-specific computation.  The physical heat string will supply
the local stencils in the successor module.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleHeadPhysicalEnergy
import YMGap.Continuum.CubeRatioBounds
import YMGap.Continuum.R1EvenCentreBound

namespace YMGap.Continuum.P2BlockCompatibleHeadLocalEnergyCompiler

set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.R1EvenCentreBound

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private def q2 : Q' := Q'.ofNat 2
private def q3 : Q' := Q'.ofNat 3

/-- Type-level local stencil data for a path with `M+2` adjacent edges and
`M+1` distance-two edges. -/
structure TwoStepLocalEnergyData (edge jump : Nat -> Q') (M : Nat) : Type where
  first : q3 * edge 0 <= jump 0
  middle : forall i, i < M ->
    q3 * edge (i + 1) <= jump i + jump (i + 1)
  last : q3 * edge (M + 1) <= jump M

private theorem edge_sum_decompose (edge : Nat -> Q') (M : Nat) :
    q3 * fsum edge (M + 2) ≈
      q3 * edge 0 +
        (q3 * fsum (fun i => edge (i + 1)) M +
          q3 * edge (M + 1)) := by
  have hhead := fsum_shift_cons edge (M + 1)
  have htail :
      fsum (fun i => edge (i + 1)) (M + 1) =
        fsum (fun i => edge (i + 1)) M + edge (M + 1) := rfl
  rw [htail] at hhead
  refine Q'.eqv_trans _
    (q3 * (edge 0 +
      (fsum (fun i => edge (i + 1)) M + edge (M + 1)))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left q3 _ _ hhead
  · ring_qeqv

private theorem middle_sum_bound {edge jump : Nat -> Q'} {M : Nat}
    (h : forall i, i < M ->
      q3 * edge (i + 1) <= jump i + jump (i + 1)) :
    q3 * fsum (fun i => edge (i + 1)) M <=
      fsum (fun i => jump i + jump (i + 1)) M := by
  have hsum := fsum_mono_lt M h
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (fsum_const_mul q3 (fun i => edge (i + 1)) M)) hsum

private theorem jump_budget_eqv (jump : Nat -> Q') (M : Nat) :
    jump 0 +
        (fsum (fun i => jump i + jump (i + 1)) M + jump M) ≈
      q2 * fsum jump (M + 1) := by
  have hadd := fsum_add jump (fun i => jump (i + 1)) M
  have hshift := fsum_shift_cons jump M
  have hsucc : fsum jump (M + 1) = fsum jump M + jump M := rfl
  refine Q'.eqv_trans _
    (jump 0 +
      ((fsum jump M + fsum (fun i => jump (i + 1)) M) + jump M)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (jump 0) _ _
      (Q'.add_eqv_congr_right _ _ (jump M) hadd)
  refine Q'.eqv_trans _
    ((jump 0 + fsum (fun i => jump (i + 1)) M) +
      (fsum jump M + jump M)) _ ?_ ?_
  · ring_qeqv
  refine Q'.eqv_trans _
    (fsum jump (M + 1) + fsum jump (M + 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_symm hshift)
      (Q'.eqv_of_eq hsucc.symm)
  · unfold q2
    exact Q'.eqv_symm (CubeRatioBounds.ofNat_two_mul_eqv _)

/-- **Local-to-global two-step energy compiler.**  No peak location, sign
search, or cutoff enumeration occurs here. -/
theorem twoStepEnergy_of_localData {edge jump : Nat -> Q'} {M : Nat}
    (D : TwoStepLocalEnergyData edge jump M) :
    q3 * fsum edge (M + 2) <= q2 * fsum jump (M + 1) := by
  have hmiddle := middle_sum_bound D.middle
  have hsum :
      q3 * edge 0 +
          (q3 * fsum (fun i => edge (i + 1)) M +
            q3 * edge (M + 1)) <=
        jump 0 +
          (fsum (fun i => jump i + jump (i + 1)) M + jump M) :=
    Q'.add_le_add D.first (Q'.add_le_add hmiddle D.last)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (edge_sum_decompose edge M))
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (jump_budget_eqv jump M)))

#print axioms twoStepEnergy_of_localData

end YMGap.Continuum.P2BlockCompatibleHeadLocalEnergyCompiler
