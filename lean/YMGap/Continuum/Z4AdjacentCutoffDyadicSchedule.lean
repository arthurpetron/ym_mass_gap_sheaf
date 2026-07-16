/-
# A dyadic schedule for the interacting adjacent-cutoff increment

The exact adjacent-cutoff majorant still contains three cutoff-dependent
entropy factors: the number of physical face labellings, the representation
dimension of the first omitted face, and a cubic fusion-multiplicity envelope
at every distinct link.  This file pays all three factors from disjoint blocks
of the quadratic SU(2) Casimir exponent.

For a box with `P` plaquettes, the deliberately loose but explicit schedule

`K(stage,n) = 100 * (P + 1) + stage`

leaves at least `stage` uncancelled powers of one half.  Consequently the
*actual interacting* adjacent partition increment is at most
`(1/2)^stage`.  No measured constant or assumed summability certificate enters
the proof.
-/

import YMGap.Continuum.CasimirMoment
import YMGap.Continuum.Z4AdjacentCutoffIncrementBound
import YMGap.Continuum.Z4GrowingCutoffVolumeTail

namespace YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CasimirMoment
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4AdjacentCutoffIncrementBound
open YMGap.Continuum.Z4ExplicitSupportMultiplicityBound
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedCutoffNaiveTailFence
open YMGap.Continuum.Z4GrowingCutoffVolumeTail
open YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Encode the complete natural prefactor by one dyadic exponent -/

def adjacentCutoffNatPrefactor (K P : Nat) : Nat :=
  (K + 2) ^ P *
    ((K + 2) *
      localMultiplicityNatBound (linkAuxiliaryCutoff (K + 1)) ^ (P * 4))

def adjacentEntropyExponent (K P : Nat) : Nat :=
  (K + 2) * (P + 1) +
    (linkAuxiliaryCutoff (K + 1) + 1) * 3 * (P * 4)

private theorem localMultiplicityNatBound_le_twoPow (cutoff : Nat) :
    localMultiplicityNatBound cutoff ≤ 2 ^ ((cutoff + 1) * 3) := by
  have hbase : cutoff + 1 ≤ 2 ^ (cutoff + 1) :=
    nat_le_two_pow (cutoff + 1)
  unfold localMultiplicityNatBound
  have hmul : (cutoff + 1) * ((cutoff + 1) * (cutoff + 1)) ≤
      (2 ^ (cutoff + 1)) *
        ((2 ^ (cutoff + 1)) * (2 ^ (cutoff + 1))) :=
    Nat.mul_le_mul hbase (Nat.mul_le_mul hbase hbase)
  refine Nat.le_trans hmul ?_
  rw [Nat.pow_mul]
  simp [Nat.pow_succ, Nat.mul_assoc]

theorem adjacentCutoffNatPrefactor_le_twoPow (K P : Nat) :
    adjacentCutoffNatPrefactor K P ≤
      2 ^ adjacentEntropyExponent K P := by
  have hdim : K + 2 ≤ 2 ^ (K + 2) := nat_le_two_pow (K + 2)
  have hfaces : (K + 2) ^ P ≤ (2 ^ (K + 2)) ^ P :=
    Nat.pow_le_pow_left hdim P
  have hlocal := localMultiplicityNatBound_le_twoPow
    (linkAuxiliaryCutoff (K + 1))
  have hlinks :
      localMultiplicityNatBound (linkAuxiliaryCutoff (K + 1)) ^ (P * 4) ≤
        (2 ^ ((linkAuxiliaryCutoff (K + 1) + 1) * 3)) ^ (P * 4) :=
    Nat.pow_le_pow_left hlocal (P * 4)
  have hproduct := Nat.mul_le_mul hfaces (Nat.mul_le_mul hdim hlinks)
  unfold adjacentCutoffNatPrefactor adjacentEntropyExponent
  calc
    (K + 2) ^ P *
        ((K + 2) *
          localMultiplicityNatBound (linkAuxiliaryCutoff (K + 1)) ^ (P * 4))
        ≤ (2 ^ (K + 2)) ^ P *
          ((2 ^ (K + 2)) *
            (2 ^ ((linkAuxiliaryCutoff (K + 1) + 1) * 3)) ^ (P * 4)) :=
          hproduct
    _ = 2 ^ ((K + 2) * (P + 1) +
        (linkAuxiliaryCutoff (K + 1) + 1) * 3 * (P * 4)) := by
      rw [← Nat.pow_mul, ← Nat.pow_mul]
      rw [← Nat.pow_add, ← Nat.pow_add]
      congr 1
      rw [Nat.mul_succ]
      exact (Nat.add_assoc
        ((K + 2) * P) (K + 2)
          ((linkAuxiliaryCutoff (K + 1) + 1) * 3 * (P * 4))).symm

/-! ## 2. A uniform coarse entropy budget -/

theorem adjacentEntropyExponent_le_coarse (K P : Nat) :
    adjacentEntropyExponent K P ≤
      (K + 1) * (100 * (P + 1)) := by
  have hdim : K + 2 ≤ 2 * (K + 1) := by omega
  have haux : linkAuxiliaryCutoff (K + 1) + 1 ≤ 8 * (K + 1) := by
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  have hfirst : (K + 2) * (P + 1) ≤
      (2 * (K + 1)) * (P + 1) :=
    Nat.mul_le_mul_right (P + 1) hdim
  have hsecond0 :
      (linkAuxiliaryCutoff (K + 1) + 1) * 3 ≤
        (8 * (K + 1)) * 3 :=
    Nat.mul_le_mul_right 3 haux
  have hsecond :
      (linkAuxiliaryCutoff (K + 1) + 1) * 3 * (P * 4) ≤
        ((8 * (K + 1)) * 3) * (P * 4) :=
    Nat.mul_le_mul_right (P * 4) hsecond0
  have hP : P ≤ P + 1 := by omega
  have hsecondCoarse :
      ((8 * (K + 1)) * 3) * (P * 4) ≤
        (96 * (K + 1)) * (P + 1) := by
    have hmul := Nat.mul_le_mul_left (96 * (K + 1)) hP
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  have hadd := Nat.add_le_add hfirst (Nat.le_trans hsecond hsecondCoarse)
  unfold adjacentEntropyExponent
  refine Nat.le_trans hadd ?_
  let X := (K + 1) * (P + 1)
  have hrearrange :
      (2 * (K + 1)) * (P + 1) +
          (96 * (K + 1)) * (P + 1) = 98 * X := by
    dsimp only [X]
    calc
      (2 * (K + 1)) * (P + 1) +
          (96 * (K + 1)) * (P + 1) =
          (2 * (K + 1) + 96 * (K + 1)) * (P + 1) := by
            rw [Nat.add_mul]
      _ = (98 * (K + 1)) * (P + 1) := by
            congr 1
            omega
      _ = 98 * ((K + 1) * (P + 1)) := by
            rw [Nat.mul_assoc]
  rw [hrearrange]
  have h98 : 98 * X ≤ 100 * X := Nat.mul_le_mul_right X (by decide)
  simpa [X, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h98

/-! ## 3. Exact rational normalization of the prefactor -/

private theorem ofNat_pow_eqv (a : Nat) : ∀ n : Nat,
    Q'.ofNat (a ^ n) ≈ (Q'.ofNat a) ^ n
  | 0 => by
      rw [Nat.pow_zero, Q'.pow_zero]
      change ((1 : Q') ≈ (1 : Q'))
      exact Q'.eqv_refl _
  | n + 1 => by
      rw [Nat.pow_succ, Q'.pow_succ]
      refine Q'.eqv_trans _
        (Q'.ofNat (a ^ n) * Q'.ofNat a) _
        (YMGap.Continuum.HeatKernelRGStep.ofNat_mul_eqv (a ^ n) a) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat a * Q'.ofNat (a ^ n)) _
        (Q'.mul_comm_eqv _ _) ?_
      exact Q'.mul_eqv_congr_left _ _ _ (ofNat_pow_eqv a n)

private theorem extract_heat_factor (a d h ell : Q') :
    a * ((d * h) * ell) ≈ (a * (d * ell)) * h := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

theorem adjacentCutoffVolumeMajorant_eqv_prefactor_halfPow (K n : Nat) :
    adjacentCutoffVolumeMajorant K n ≈
      Q'.ofNat
        (adjacentCutoffNatPrefactor K (plaquetteEdgeCount n)) *
          (HalfPow.half ^ c4 (K + 1)) := by
  let P := plaquetteEdgeCount n
  let M := localMultiplicityNatBound (linkAuxiliaryCutoff (K + 1))
  have hlinkPow :
      (Q'.ofNat M) ^ (P * 4) ≈ Q'.ofNat (M ^ (P * 4)) :=
    Q'.eqv_symm (ofNat_pow_eqv M (P * 4))
  have hinner :
      Q'.ofNat (K + 2) * (Q'.ofNat M) ^ (P * 4) ≈
        Q'.ofNat ((K + 2) * (M ^ (P * 4))) := by
    refine Q'.eqv_trans _
      (Q'.ofNat (K + 2) * Q'.ofNat (M ^ (P * 4))) _
      (Q'.mul_eqv_congr_left _ _ _ hlinkPow) ?_
    exact Q'.eqv_symm
      (YMGap.Continuum.HeatKernelRGStep.ofNat_mul_eqv
        (K + 2) (M ^ (P * 4)))
  have hprefix :
      Q'.ofNat ((K + 2) ^ P) *
          (Q'.ofNat (K + 2) * (Q'.ofNat M) ^ (P * 4)) ≈
        Q'.ofNat (adjacentCutoffNatPrefactor K P) := by
    refine Q'.eqv_trans _
      (Q'.ofNat ((K + 2) ^ P) *
        Q'.ofNat ((K + 2) * (M ^ (P * 4)))) _
      (Q'.mul_eqv_congr_left _ _ _ hinner) ?_
    exact Q'.eqv_symm
      (YMGap.Continuum.HeatKernelRGStep.ofNat_mul_eqv
        ((K + 2) ^ P) ((K + 2) * (M ^ (P * 4))))
  unfold adjacentCutoffVolumeMajorant firstOmittedCoefficient coeffW
    dimQ linkMultiplicityBound
  dsimp only [P, M] at hprefix ⊢
  refine Q'.eqv_trans _
    ((Q'.ofNat ((K + 2) ^ plaquetteEdgeCount n) *
      (Q'.ofNat (K + 2) *
        (Q'.ofNat
          (localMultiplicityNatBound (linkAuxiliaryCutoff (K + 1)))) ^
            (plaquetteEdgeCount n * 4))) *
      qpow coupling (c4 (K + 1))) _
    (extract_heat_factor _ _ _ _) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat
      (adjacentCutoffNatPrefactor K (plaquetteEdgeCount n)) *
        qpow coupling (c4 (K + 1))) _
    (Q'.mul_eqv_congr_right _ _ _ hprefix) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (qpow_coupling_eqv_halfPow (c4 (K + 1)))

/-! ## 4. Cancel the entropy against the Casimir reserve -/

theorem adjacentCutoffVolumeMajorant_le_halfPow_of_reserve
    (K n stage : Nat)
    (hreserve : adjacentEntropyExponent K (plaquetteEdgeCount n) + stage ≤
      c4 (K + 1)) :
    adjacentCutoffVolumeMajorant K n ≤ HalfPow.half ^ stage := by
  let P := plaquetteEdgeCount n
  let E := adjacentEntropyExponent K P
  let C := c4 (K + 1)
  let A := adjacentCutoffNatPrefactor K P
  have hA : A ≤ 2 ^ E := by
    dsimp only [A, E, P]
    exact adjacentCutoffNatPrefactor_le_twoPow K (plaquetteEdgeCount n)
  have hnat : Q'.ofNat A ≤ Q'.ofNat (2 ^ E) :=
    Q'.ofNat_le_ofNat hA
  have hhalf0 : (0 : Q') ≤ HalfPow.half ^ C :=
    Q'.pow_nonneg _ (by decide) _
  have hprefactor : Q'.ofNat A * (HalfPow.half ^ C) ≤
      Q'.ofNat (2 ^ E) * (HalfPow.half ^ C) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hnat hhalf0
  have hreserve' : E + stage ≤ C := by
    dsimp only [E, C, P]
    exact hreserve
  obtain ⟨r, hC⟩ := Nat.exists_eq_add_of_le hreserve'
  have hcancel : Q'.ofNat (2 ^ E) * (HalfPow.half ^ C) ≤
      HalfPow.half ^ stage := by
    have hC' : C = E + (stage + r) := by omega
    have heq : Q'.ofNat (2 ^ E) * (HalfPow.half ^ C) ≈
        HalfPow.half ^ (stage + r) := by
      rw [hC']
      exact twoPow_halfPow_add_eqv E (stage + r)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
      (halfPow_antitone (by omega))
  have hmajorant :=
    adjacentCutoffVolumeMajorant_eqv_prefactor_halfPow K n
  dsimp only [A, C, P] at hmajorant hprefactor hcancel ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hmajorant)
    (Q'.le_trans' _ _ _ hprefactor hcancel)

def interactingAdjacentCutoff (stage n : Nat) : Nat :=
  100 * (plaquetteEdgeCount n + 1) + stage

theorem interactingAdjacentCutoff_unbounded (n bound : Nat) :
    ∃ stage, bound ≤ interactingAdjacentCutoff stage n := by
  refine ⟨bound, ?_⟩
  unfold interactingAdjacentCutoff
  omega

theorem interactingAdjacentCutoff_entropy_reserve (stage n : Nat) :
    adjacentEntropyExponent (interactingAdjacentCutoff stage n)
        (plaquetteEdgeCount n) + stage ≤
      c4 (interactingAdjacentCutoff stage n + 1) := by
  let P := plaquetteEdgeCount n
  let K := interactingAdjacentCutoff stage n
  have hE : adjacentEntropyExponent K P ≤
      (K + 1) * (100 * (P + 1)) :=
    adjacentEntropyExponent_le_coarse K P
  have hstage : stage ≤ (K + 1) * stage := by
    have hone : 1 ≤ K + 1 := by omega
    simpa using Nat.mul_le_mul_right stage hone
  have hadd := Nat.add_le_add hE hstage
  have hbracket : 100 * (P + 1) + stage ≤ K + 3 := by
    dsimp only [K, P, interactingAdjacentCutoff]
    omega
  have hmul : (K + 1) * (100 * (P + 1) + stage) ≤
      (K + 1) * (K + 3) :=
    Nat.mul_le_mul_left (K + 1) hbracket
  have hrearrange :
      (K + 1) * (100 * (P + 1)) + (K + 1) * stage =
        (K + 1) * (100 * (P + 1) + stage) := by
    exact (Nat.mul_add (K + 1) (100 * (P + 1)) stage).symm
  dsimp only [K, P] at hE hadd hmul hrearrange ⊢
  unfold c4
  rw [hrearrange] at hadd
  exact Nat.le_trans hadd hmul

theorem interactingAdjacentCutoff_volumeMajorant_le_halfPow
    (stage n : Nat) :
    adjacentCutoffVolumeMajorant (interactingAdjacentCutoff stage n) n ≤
      HalfPow.half ^ stage :=
  adjacentCutoffVolumeMajorant_le_halfPow_of_reserve _ _ _
    (interactingAdjacentCutoff_entropy_reserve stage n)

/-- The actual interacting partition increment, including all retained
fusion-channel multiplicities, obeys the explicit dyadic schedule. -/
theorem interactingAdjacentCutoff_increment_le_halfPow (stage n : Nat) :
    fusionCompleteCutoffIncrement (interactingAdjacentCutoff stage n)
        (interactingAdjacentCutoff stage n + 1) n ≤
      HalfPow.half ^ stage :=
  Q'.le_trans' _ _ _
    (adjacentCutoffIncrement_le_volumeMajorant
      (interactingAdjacentCutoff stage n) n)
    (interactingAdjacentCutoff_volumeMajorant_le_halfPow stage n)

end YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule.adjacentCutoffNatPrefactor_le_twoPow
#print axioms YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule.adjacentEntropyExponent_le_coarse
#print axioms YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule.adjacentCutoffVolumeMajorant_eqv_prefactor_halfPow
#print axioms YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule.interactingAdjacentCutoff_entropy_reserve
#print axioms YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule.interactingAdjacentCutoff_increment_le_halfPow
