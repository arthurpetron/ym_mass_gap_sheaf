/-
Track 11.7-fusion / R3p -- fixed 640-block terminal endpoint-step reduction.

# Result

The convex chord already replaces the full physical theta sum by fixed-block
geometric moments.  A still simpler lower bound freezes the power in each
block at its right endpoint.  With 640 blocks the physical length is

    L_k = 640 * 2^(k-7),  k >= 7,

so the number of frozen endpoint powers is independent of scale.  Their
dyadic evolution is monotone by the proved physical heat-power transport
`w_k <= w_(k+1)^4`.  This leaves a fixed finite endpoint table plus scalar
power bounds, rather than a growing theta evaluation.

No inhabitant of the final fixed-table inequality is asserted here.

# Constructivity

Finite-sum monotonicity, exact schedule arithmetic, power antitonicity on
`[0,1]`, and the proved physical fourth-power comparison only.  No
`Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaTerminalGeoMoments

namespace YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointStep

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleHeatPower
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
open YMGap.Continuum.P2BlockCompatibleThetaTerminalTenChord
open YMGap.Continuum.P2BlockCompatibleThetaTerminalRadial
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast,
               Q'.add_num_cast, Q'.add_den_cast, Int.mul_one];
             ac_rfl))

private theorem mul_nested_swap (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  refine Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ ((b * a) * c) _
    (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

/-- Right-endpoint square exponent for block `b`. -/
def endpointStepExponent (H b : Nat) : Nat :=
  ((b + 1) * H) * ((b + 1) * H)

/-- Freeze every power in a block at the block's right endpoint. -/
def weightedEndpointStepBlock (q : Q') (H b : Nat) : Q' :=
  fsum (fun r =>
    Q'.ofNat ((b * H + r + 1) * (b * H + r + 1)) *
      qpow q (endpointStepExponent H b)) H

def weightedEndpointStepBlocks (q : Q') (H B : Nat) : Q' :=
  fsum (fun b => weightedEndpointStepBlock q H b) B

/-! ## Exact block square mass and its scale-free cubic lower bound -/

/-- Sum of `(a+1)^2,...,(a+H)^2` in `Nat`, kept separate from the rational
power calculation. -/
def natSquareRangeMass (a : Nat) : Nat -> Nat
  | 0 => 0
  | H + 1 => natSquareRangeMass a H + (a + H + 1) * (a + H + 1)

theorem fsum_squareRange_eqv_ofNat (a : Nat) : forall H,
    fsum (fun r => Q'.ofNat ((a + r + 1) * (a + r + 1))) H ≈
      Q'.ofNat (natSquareRangeMass a H)
  | 0 => Q'.eqv_refl 0
  | H + 1 => by
      change fsum (fun r => Q'.ofNat ((a + r + 1) * (a + r + 1))) H +
          Q'.ofNat ((a + H + 1) * (a + H + 1)) ≈
        Q'.ofNat (natSquareRangeMass a H +
          (a + H + 1) * (a + H + 1))
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (fsum_squareRange_eqv_ofNat a H)
          (Q'.eqv_refl _))
        (Q'.eqv_symm (Q'.ofNat_add_eqv _ _))

private theorem cube_succ_eq (n : Nat) :
    (n + 1) * (n + 1) * (n + 1) =
      n * n * n + 3 * (n * n) + 3 * n + 1 := by
  have hsq : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  rw [hsq]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  have htwo : 2 * n * n = 2 * (n * n) := by rw [Nat.mul_assoc]
  rw [htwo]
  omega

private theorem cube_succ_le_three_square (n : Nat) :
    (n + 1) * (n + 1) * (n + 1) <=
      n * n * n + 3 * ((n + 1) * (n + 1)) := by
  rw [cube_succ_eq]
  have hsq : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  rw [hsq]
  omega

private theorem cube_range_le_mass (a : Nat) : forall H,
    (a + H) * (a + H) * (a + H) <=
      a * a * a + 3 * natSquareRangeMass a H
  | 0 => by simp [natSquareRangeMass]
  | H + 1 => by
      have ih := cube_range_le_mass a H
      have hs := cube_succ_le_three_square (a + H)
      have hidx : a + (H + 1) = a + H + 1 := by omega
      rw [hidx]
      refine Nat.le_trans hs ?_
      change (a + H) * (a + H) * (a + H) +
          3 * ((a + H + 1) * (a + H + 1)) <=
        a * a * a +
          3 * (natSquareRangeMass a H +
            (a + H + 1) * (a + H + 1))
      have hadd := Nat.add_le_add_right ih
        (3 * ((a + H + 1) * (a + H + 1)))
      refine Nat.le_trans hadd ?_
      rw [Nat.mul_add]
      omega

/-- Cubic shell weight `(b+1)^3-b^3`, in subtraction-free form. -/
def endpointShellCubic (b : Nat) : Nat :=
  3 * (b * b) + 3 * b + 1

private theorem endpoint_cube_split (H b : Nat) :
    ((b + 1) * H) * ((b + 1) * H) * ((b + 1) * H) =
      (b * H) * (b * H) * (b * H) +
        endpointShellCubic b * (H * H * H) := by
  have hfine :
      ((b + 1) * H) * ((b + 1) * H) * ((b + 1) * H) =
        ((b + 1) * (b + 1) * (b + 1)) * (H * H * H) := by
    ac_rfl
  have hcoarse :
      (b * H) * (b * H) * (b * H) =
        (b * b * b) * (H * H * H) := by
    ac_rfl
  rw [hfine, hcoarse, cube_succ_eq]
  unfold endpointShellCubic
  simp only [Nat.add_mul, Nat.one_mul]
  omega

/-- Three times the literal square mass in block `b` dominates its exact
scale-free cubic shell weight. -/
theorem shellCube_le_three_squareRangeMass (H b : Nat) :
    endpointShellCubic b * (H * H * H) <=
      3 * natSquareRangeMass (b * H) H := by
  have h := cube_range_le_mass (b * H) H
  have hlen : b * H + H = (b + 1) * H := by
    rw [Nat.add_mul]
    omega
  rw [hlen, endpoint_cube_split] at h
  omega

private theorem chordExponent_le_endpointStepExponent
    {H b r : Nat} (hr : r < H) :
    weightedChordExponent H b r <= endpointStepExponent H b := by
  unfold weightedChordExponent endpointStepExponent
  have hr1 : r + 1 <= H := by omega
  let x := b * H
  have hhi : (b + 1) * H = x + H := by
    dsimp only [x]
    rw [Nat.add_mul]
    omega
  have hmul := Nat.mul_le_mul_left
    ((((b + 1) * H) + b * H)) hr1
  have hsum := Nat.add_le_add_left hmul (b * H * (b * H))
  refine Nat.le_trans hsum ?_
  rw [hhi]
  dsimp only [x]
  simp only [Nat.add_mul, Nat.mul_add]
  rw [Nat.mul_comm H (b * H)]
  omega

/-- The frozen endpoint block is below the convex chord block. -/
theorem weightedEndpointStepBlock_le_chord
    {q : Q'} (hq0 : (0 : Q') <= q) (hq1 : q <= (1 : Q'))
    (H b : Nat) :
    weightedEndpointStepBlock q H b <= weightedChordBlock q H b := by
  unfold weightedEndpointStepBlock weightedChordBlock
  apply CubeRatioBounds.fsum_mono_lt
  intro r hr
  have hp := HeatKernelRGStep.qpow_antitone hq0 hq1
    (weightedChordExponent H b r) (endpointStepExponent H b)
    (chordExponent_le_endpointStepExponent hr)
  exact Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat ((b * H + r + 1) * (b * H + r + 1))) hp
    (HeatKernelRGStep.zero_le_ofNat _)

theorem weightedEndpointStepBlocks_le_chord
    {q : Q'} (hq0 : (0 : Q') <= q) (hq1 : q <= (1 : Q'))
    (H B : Nat) :
    weightedEndpointStepBlocks q H B <= weightedChordBlocks q H B := by
  unfold weightedEndpointStepBlocks weightedChordBlocks
  apply CubeRatioBounds.fsum_mono_lt
  intro b _
  exact weightedEndpointStepBlock_le_chord hq0 hq1 H b

/-- Hence every fixed endpoint-step sum is a lower bound for the matching
integer-theta prefix. -/
theorem weightedEndpointStepBlocks_le_integerThetaSum
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    {H B : Nat} (hBH : 0 < B * H) :
    weightedEndpointStepBlocks (w * w) H B <=
      integerThetaSum w (B * H - 1) := by
  have hq0 : (0 : Q') <= w * w := Q'.mul_nonneg _ _ hw0 hw0
  have hq1 : w * w <= (1 : Q') := by
    have hm := Q'.mul_le_mul_of_nonneg hw1 hw1 (by decide) hw0
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  exact Q'.le_trans' _ _ _
    (weightedEndpointStepBlocks_le_chord hq0 hq1 H B)
    (weightedChordBlocks_le_integerThetaSum hw0 hw1 hBH)

/-- The physical cutoff is exactly 640 dyadic blocks throughout the `k>=7`
tail. -/
theorem blockCutoffLength_eq_640_dyadicBlocks
    {k : Nat} (hk : 7 <= k) :
    blockNcut k + 1 = 640 * 2 ^ (k - 7) := by
  have hdecomp : k = 7 + (k - 7) := by omega
  rw [blockCutoffLength_closed, hdecomp, Nat.pow_add]
  have hsub : 7 + (k - 7) - 7 = k - 7 := by omega
  rw [hsub]
  change 5 * (128 * 2 ^ (k - 7)) = 640 * 2 ^ (k - 7)
  omega

/-- The 640-block endpoint-step sum is a physical lower bound at every open
tail scale. -/
theorem weighted640EndpointSteps_le_integerThetaSum
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    {k : Nat} (hk : 7 <= k) :
    weightedEndpointStepBlocks (w * w) (2 ^ (k - 7)) 640 <=
      integerThetaSum w (blockNcut k) := by
  have hpow : 0 < 2 ^ (k - 7) := Nat.pow_pos (by decide)
  have hlen := blockCutoffLength_eq_640_dyadicBlocks hk
  have h := weightedEndpointStepBlocks_le_integerThetaSum hw0 hw1
    (H := 2 ^ (k - 7)) (B := 640) (by omega)
  have hN : 640 * 2 ^ (k - 7) - 1 = blockNcut k := by omega
  rw [hN] at h
  exact h

/-- The endpoint power written directly in the underlying fine heat weight.
The exponent `8*endpoint^2` is exactly the square of the fourth-power theta
weight. -/
def physicalEndpointPower (k b : Nat) : Q' :=
  let H := 2 ^ (k - 7)
  qpow (blockWeight (k + 1))
    (8 * (((b + 1) * H) * ((b + 1) * H)))

private theorem endpointSquare_doubles
    {k : Nat} (hk : 7 <= k) (b : Nat) :
    ((b + 1) * 2 ^ (k + 1 - 7)) *
        ((b + 1) * 2 ^ (k + 1 - 7)) =
      4 * (((b + 1) * 2 ^ (k - 7)) *
        ((b + 1) * 2 ^ (k - 7))) := by
  have hsub : k + 1 - 7 = (k - 7) + 1 := by omega
  rw [hsub, Nat.pow_succ]
  let a := (b + 1) * 2 ^ (k - 7)
  have ha : (b + 1) * (2 ^ (k - 7) * 2) = 2 * a := by
    dsimp only [a]
    ac_rfl
  rw [ha]
  change (2 * a) * (2 * a) = 4 * (a * a)
  calc
    (2 * a) * (2 * a) = (2 * 2) * (a * a) := by ac_rfl
    _ = 4 * (a * a) := rfl

/-- Each fixed right-endpoint power is monotone along the physical dyadic
tail.  This is the all-scale reduction: a lower bound checked at `k=7`
persists at every later cutoff. -/
theorem physicalEndpointPower_mono
    {k : Nat} (hk : 7 <= k) (b : Nat) :
    physicalEndpointPower k b <= physicalEndpointPower (k + 1) b := by
  let e := ((b + 1) * 2 ^ (k - 7)) *
    ((b + 1) * 2 ^ (k - 7))
  have hbase := blockWeight_le_fine_fourth (k + 1)
  have hpow := HeatKernelGap.qpow_mono
    (blockWeight_nonneg (k + 1)) hbase (8 * e)
  have hiter := HeatKernelRGStep.qpow_qpow
    (blockWeight (k + 2)) 4 (8 * e)
  have hesq := endpointSquare_doubles hk b
  have hexp : 4 * (8 * e) =
      8 * (((b + 1) * 2 ^ (k + 1 - 7)) *
        ((b + 1) * 2 ^ (k + 1 - 7))) := by
    rw [hesq]
    omega
  unfold physicalEndpointPower
  dsimp only
  refine Q'.le_trans' _ _ _ hpow ?_
  have hright :
      qpow (qpow (blockWeight (k + 2)) 4) (8 * e) ≈
        qpow (blockWeight (k + 2))
          (8 * (((b + 1) * 2 ^ (k + 1 - 7)) *
            ((b + 1) * 2 ^ (k + 1 - 7)))) := by
    refine Q'.eqv_trans _ _ _ hiter ?_
    rw [hexp]
    exact Q'.eqv_refl _
  simpa only [e] using Q'.le_of_eqv hright

/-- The theta-square endpoint power is exactly the underlying fine heat
weight raised to `8*endpoint^2`. -/
theorem endpointStepPower_eq_physical (k b : Nat) :
    let H := 2 ^ (k - 7)
    let w4 := qpow (blockWeight (k + 1)) 4
    qpow (w4 * w4) (endpointStepExponent H b) ≈
      physicalEndpointPower k b := by
  let H := 2 ^ (k - 7)
  let w := blockWeight (k + 1)
  let w4 := qpow w 4
  let e := endpointStepExponent H b
  have hsquare := YMGap.Continuum.FusionQuotientCollapse.qpow_mul_self w4 e
  have hadd := HeatKernelRGStep.qpow_add w4 e e
  have hiter := HeatKernelRGStep.qpow_qpow w 4 (e + e)
  have hexp : 4 * (e + e) = 8 * e := by omega
  dsimp only [H, w4, e, w]
  refine Q'.eqv_trans _ (qpow (qpow (blockWeight (k + 1)) 4)
      (endpointStepExponent (2 ^ (k - 7)) b +
        endpointStepExponent (2 ^ (k - 7)) b)) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _ hsquare (Q'.eqv_symm hadd)
  · refine Q'.eqv_trans _ _ _ hiter ?_
    rw [hexp]
    change qpow (blockWeight (k + 1))
      (8 * (((b + 1) * 2 ^ (k - 7)) *
        ((b + 1) * 2 ^ (k - 7)))) ≈ physicalEndpointPower k b
    unfold physicalEndpointPower
    exact Q'.eqv_refl _

/-- Monotonicity iterated from the first open scale: every fixed endpoint
power is bounded below by its `k=7` value. -/
theorem physicalEndpointPower_seven_le
    {k : Nat} (hk : 7 <= k) (b : Nat) :
    physicalEndpointPower 7 b <= physicalEndpointPower k b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
      exact Q'.le_trans' _ _ _ (ih (by omega))
        (physicalEndpointPower_mono (k := 7 + d) (by omega) b)

/-! ## Collapse of every scale to one fixed 640-entry lower table -/

def physicalEndpointStepBlock (k b : Nat) : Q' :=
  let H := 2 ^ (k - 7)
  let w4 := qpow (blockWeight (k + 1)) 4
  weightedEndpointStepBlock (w4 * w4) H b

def physicalEndpointStepBlocks (k : Nat) : Q' :=
  fsum (fun b => physicalEndpointStepBlock k b) 640

theorem physicalEndpointStepBlock_eq_mass_mul_power (k b : Nat) :
    let H := 2 ^ (k - 7)
    physicalEndpointStepBlock k b ≈
      Q'.ofNat (natSquareRangeMass (b * H) H) *
        physicalEndpointPower k b := by
  let H := 2 ^ (k - 7)
  let w4 := qpow (blockWeight (k + 1)) 4
  let P := physicalEndpointPower k b
  have hp : qpow (w4 * w4) (endpointStepExponent H b) ≈ P := by
    simpa only [H, w4, P] using endpointStepPower_eq_physical k b
  unfold physicalEndpointStepBlock weightedEndpointStepBlock
  dsimp only [H, w4]
  refine Q'.eqv_trans _
    (fsum (fun r =>
      Q'.ofNat ((b * 2 ^ (k - 7) + r + 1) *
          (b * 2 ^ (k - 7) + r + 1)) * P) (2 ^ (k - 7))) _ ?_ ?_
  · exact CubeRatioBounds.fsum_eqv_congr _ _
      (fun r => Q'.mul_eqv_congr_left _ _ _ hp) _
  · refine Q'.eqv_trans _
      (fsum (fun r => Q'.ofNat
          ((b * 2 ^ (k - 7) + r + 1) *
            (b * 2 ^ (k - 7) + r + 1))) (2 ^ (k - 7)) * P) _
      (Q'.eqv_symm (CubeRatioBounds.fsum_mul_const
        (fun r => Q'.ofNat
          ((b * 2 ^ (k - 7) + r + 1) *
            (b * 2 ^ (k - 7) + r + 1))) P (2 ^ (k - 7)))) ?_
    exact Q'.mul_eqv_congr_right _ _ P
      (fsum_squareRange_eqv_ofNat (b * 2 ^ (k - 7)) (2 ^ (k - 7)))

theorem physicalEndpointStepBlocks_eq_weighted (k : Nat) :
    let H := 2 ^ (k - 7)
    let w4 := qpow (blockWeight (k + 1)) 4
    weightedEndpointStepBlocks (w4 * w4) H 640 ≈
      physicalEndpointStepBlocks k := by
  unfold weightedEndpointStepBlocks physicalEndpointStepBlocks
  exact CubeRatioBounds.fsum_eqv_congr _ _
    (fun b => Q'.eqv_refl _) 640

/-- The single fixed lower table at the first open scale. -/
def fixedEndpointTable : Q' :=
  fsum (fun b =>
    Q'.ofNat (endpointShellCubic b) * physicalEndpointPower 7 b) 640

private theorem scaled_base_term_le_physical
    {k : Nat} (hk : 7 <= k) (b : Nat) :
    let H := 2 ^ (k - 7)
    Q'.ofNat (endpointShellCubic b * (H * H * H)) *
        physicalEndpointPower 7 b <=
      Q'.ofNat 3 * physicalEndpointStepBlock k b := by
  let H := 2 ^ (k - 7)
  let M := natSquareRangeMass (b * H) H
  let P7 := physicalEndpointPower 7 b
  let Pk := physicalEndpointPower k b
  have hmassNat : endpointShellCubic b * (H * H * H) <= 3 * M :=
    shellCube_le_three_squareRangeMass H b
  have hmass : Q'.ofNat (endpointShellCubic b * (H * H * H)) <=
      Q'.ofNat (3 * M) := Q'.ofNat_le_ofNat hmassNat
  have hP70 : (0 : Q') <= P7 := by
    unfold P7 physicalEndpointPower
    exact qpow_nonneg _ (blockWeight_nonneg 8) _
  have hPk0 : (0 : Q') <= Pk := by
    unfold Pk physicalEndpointPower
    exact qpow_nonneg _ (blockWeight_nonneg (k + 1)) _
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _ P7 hmass hP70
  have hp : P7 <= Pk := physicalEndpointPower_seven_le hk b
  have h3M0 : (0 : Q') <= Q'.ofNat (3 * M) :=
    HeatKernelRGStep.zero_le_ofNat _
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (3 * M)) hp h3M0
  have hblock := physicalEndpointStepBlock_eq_mass_mul_power k b
  have hfinal : Q'.ofNat (3 * M) * Pk ≈
      Q'.ofNat 3 * physicalEndpointStepBlock k b := by
    refine Q'.eqv_trans _ ((Q'.ofNat 3 * Q'.ofNat M) * Pk) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ Pk
        (HeatKernelRGStep.ofNat_mul_eqv 3 M)
    · refine Q'.eqv_trans _
        (Q'.ofNat 3 * (Q'.ofNat M * Pk)) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      exact Q'.mul_eqv_congr_left (Q'.ofNat 3) _ _
        (Q'.eqv_symm (by simpa only [H, M, Pk] using hblock))
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hfinal))

/-- Every scale-dependent 640-block lower sum dominates the fixed `k=7`
endpoint table with the exact cubic factor `H^3`. -/
theorem scaledFixedEndpointTable_le_physicalBlocks
    {k : Nat} (hk : 7 <= k) :
    let H := 2 ^ (k - 7)
    fsum (fun b =>
        Q'.ofNat (endpointShellCubic b * (H * H * H)) *
          physicalEndpointPower 7 b) 640 <=
      Q'.ofNat 3 * physicalEndpointStepBlocks k := by
  let H := 2 ^ (k - 7)
  have hsum :
      fsum (fun b =>
          Q'.ofNat (endpointShellCubic b * (H * H * H)) *
            physicalEndpointPower 7 b) 640 <=
        fsum (fun b => Q'.ofNat 3 * physicalEndpointStepBlock k b) 640 := by
    apply CubeRatioBounds.fsum_mono_lt
    intro b _
    simpa only [H] using scaled_base_term_le_physical hk b
  have hpull :
      fsum (fun b => Q'.ofNat 3 * physicalEndpointStepBlock k b) 640 ≈
        Q'.ofNat 3 * physicalEndpointStepBlocks k := by
    unfold physicalEndpointStepBlocks
    exact Q'.eqv_symm (CubeRatioBounds.fsum_const_mul
      (Q'.ofNat 3) (fun b => physicalEndpointStepBlock k b) 640)
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hpull)

/-- Pull the common cubic scale out of the fixed table. -/
theorem scaledFixedEndpointTable_eqv (H : Nat) :
    fsum (fun b =>
        Q'.ofNat (endpointShellCubic b * (H * H * H)) *
          physicalEndpointPower 7 b) 640 ≈
      Q'.ofNat (H * H * H) * fixedEndpointTable := by
  let H3 := H * H * H
  have hterm : forall b,
      Q'.ofNat (endpointShellCubic b * H3) *
          physicalEndpointPower 7 b ≈
        Q'.ofNat H3 *
          (Q'.ofNat (endpointShellCubic b) *
            physicalEndpointPower 7 b) := by
    intro b
    refine Q'.eqv_trans _
      ((Q'.ofNat (endpointShellCubic b) * Q'.ofNat H3) *
        physicalEndpointPower 7 b) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (HeatKernelRGStep.ofNat_mul_eqv (endpointShellCubic b) H3)
    · refine Q'.eqv_trans _
        ((Q'.ofNat H3 * Q'.ofNat (endpointShellCubic b)) *
          physicalEndpointPower 7 b) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv _ _)
      · exact Q'.mul_assoc_eqv _ _ _
  refine Q'.eqv_trans _
    (fsum (fun b => Q'.ofNat H3 *
      (Q'.ofNat (endpointShellCubic b) *
        physicalEndpointPower 7 b)) 640) _
    (CubeRatioBounds.fsum_eqv_congr _ _ hterm 640) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat H3 * fsum (fun b =>
      Q'.ofNat (endpointShellCubic b) *
        physicalEndpointPower 7 b) 640) _
    (Q'.eqv_symm (CubeRatioBounds.fsum_const_mul
      (Q'.ofNat H3)
      (fun b => Q'.ofNat (endpointShellCubic b) *
        physicalEndpointPower 7 b) 640)) ?_
  unfold fixedEndpointTable
  exact Q'.eqv_refl _

/-- The complete physical integer-theta sum has a scale-free lower bound by
the single fixed endpoint table. -/
theorem fixedEndpointTable_lower_integerTheta
    {k : Nat} (hk : 7 <= k) :
    let H := 2 ^ (k - 7)
    let w4 := qpow (blockWeight (k + 1)) 4
    Q'.ofNat (H * H * H) * fixedEndpointTable <=
      Q'.ofNat 3 * integerThetaSum w4 (blockNcut k) := by
  let H := 2 ^ (k - 7)
  let w4 := qpow (blockWeight (k + 1)) 4
  have hscaled := scaledFixedEndpointTable_le_physicalBlocks hk
  have hfactor := scaledFixedEndpointTable_eqv H
  have hw40 : (0 : Q') <= w4 := by
    unfold w4
    exact qpow_nonneg _ (blockWeight_nonneg (k + 1)) 4
  have hw41 : w4 <= (1 : Q') := by
    unfold w4
    exact HeatKernelGap.qpow_le_one
      (blockWeight_nonneg (k + 1)) (blockWeight_le_one (k + 1)) 4
  have hstep := weighted640EndpointSteps_le_integerThetaSum hw40 hw41 hk
  have hblocks := physicalEndpointStepBlocks_eq_weighted k
  have hphysical : physicalEndpointStepBlocks k <=
      integerThetaSum w4 (blockNcut k) := by
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by
      simpa only [H, w4] using hblocks)) hstep
  have hthree0 : (0 : Q') <= Q'.ofNat 3 :=
    HeatKernelRGStep.zero_le_ofNat 3
  have hthree := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat 3) hphysical hthree0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hfactor))
    (Q'.le_trans' _ _ _ (by simpa only [H] using hscaled) hthree)

/-! ## Fixed certificate compiler for the terminal theta field -/

theorem blockWeight_mono (k : Nat) :
    blockWeight k <= blockWeight (k + 1) := by
  have hfour := blockWeight_le_fine_fourth k
  have hdrop := HeatKernelRGStep.qpow_antitone
    (blockWeight_nonneg (k + 1)) (blockWeight_le_one (k + 1))
    1 4 (by omega)
  have hone : qpow (blockWeight (k + 1)) 1 ≈ blockWeight (k + 1) := by
    change (1 : Q') * blockWeight (k + 1) ≈ blockWeight (k + 1)
    exact Q'.one_mul_eqv _
  exact Q'.le_trans' _ _ _ hfour
    (Q'.le_trans' _ _ _ hdrop (Q'.le_of_eqv hone))

theorem blockWeight_eight_le
    {k : Nat} (hk : 7 <= k) :
    blockWeight 8 <= blockWeight (k + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
      have hi := ih (by omega)
      have hmid : 7 + d + 1 = 8 + d := by omega
      rw [hmid] at hi
      have htarget : 7 + (d + 1) + 1 = (8 + d) + 1 := by omega
      rw [htarget]
      exact Q'.le_trans' _ _ _ hi (blockWeight_mono (8 + d))

/-- Fixed lower weight attached to the first open scale. -/
def fixedEndpointWeight : Q' := qpow (blockWeight 8) 4

theorem fixedEndpointWeight_le
    {k : Nat} (hk : 7 <= k) :
    fixedEndpointWeight <= qpow (blockWeight (k + 1)) 4 := by
  unfold fixedEndpointWeight
  exact HeatKernelGap.qpow_mono (blockWeight_nonneg 8)
    (blockWeight_eight_le hk) 4

/-- Exact normalization of the terminal boundary term by `640^3 H^3` and
the physical endpoint power at block 639. -/
theorem terminalBoundary_eq_cube_mul_endpointPower
    {k : Nat} (hk : 7 <= k) :
    let H := 2 ^ (k - 7)
    let w4 := qpow (blockWeight (k + 1)) 4
    blockLength k * integerThetaTerm w4 (blockNcut k + 1) ≈
      Q'.ofNat (640 * 640 * 640) *
        (Q'.ofNat (H * H * H) * physicalEndpointPower k 639) := by
  let H := 2 ^ (k - 7)
  let L := blockNcut k + 1
  let w4 := qpow (blockWeight (k + 1)) 4
  have hL : L = 640 * H := by
    simpa only [L, H] using blockCutoffLength_eq_640_dyadicBlocks hk
  have hpow : qpow (w4 * w4) (L * L) ≈
      physicalEndpointPower k 639 := by
    have hp := endpointStepPower_eq_physical k 639
    have hexp : endpointStepExponent H 639 = L * L := by
      unfold endpointStepExponent
      rw [hL]
    simpa only [H, w4, hexp] using hp
  have hcube : L * (L * L) =
      (640 * 640 * 640) * (H * H * H) := by
    rw [hL]
    ac_rfl
  unfold blockLength integerThetaTerm
  dsimp only [L, H, w4]
  refine Q'.eqv_trans _
    ((Q'.ofNat (blockNcut k + 1) *
        Q'.ofNat ((blockNcut k + 1) * (blockNcut k + 1))) *
      qpow (qpow (blockWeight (k + 1)) 4 *
        qpow (blockWeight (k + 1)) 4)
        ((blockNcut k + 1) * (blockNcut k + 1))) _ ?_ ?_
  · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  · refine Q'.eqv_trans _
      (Q'.ofNat ((blockNcut k + 1) *
          ((blockNcut k + 1) * (blockNcut k + 1))) *
        qpow (qpow (blockWeight (k + 1)) 4 *
          qpow (blockWeight (k + 1)) 4)
          ((blockNcut k + 1) * (blockNcut k + 1))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv _ _))
    · rw [hcube]
      refine Q'.eqv_trans _
        ((Q'.ofNat (640 * 640 * 640) * Q'.ofNat (H * H * H)) *
          qpow (w4 * w4) (L * L)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (HeatKernelRGStep.ofNat_mul_eqv _ _)
      · refine Q'.eqv_trans _
          (Q'.ofNat (640 * 640 * 640) *
            (Q'.ofNat (H * H * H) *
              qpow (w4 * w4) (L * L))) _
          (Q'.mul_assoc_eqv _ _ _) ?_
        exact Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hpow)

/-- One third of the original `5/16` terminal theta budget. -/
def terminalEndpointTableCoeff : Q' := Q'.mkPos 5 48 (by decide)

theorem terminalEndpointTableCoeff_mul_three :
    terminalEndpointTableCoeff * Q'.ofNat 3 ≈ terminalOuterSplitCoeff := by
  unfold terminalEndpointTableCoeff terminalOuterSplitCoeff
  decide

/-- The remaining endpoint theorem has been reduced to one scalar all-scale
power ceiling and one fixed 640-entry rational table comparison. -/
structure TerminalEndpointFixedCertificate : Type where
  powerCeil : Q'
  powerCeil_nonneg : (0 : Q') <= powerCeil
  endpointPower_le : forall k, 7 <= k ->
    physicalEndpointPower k 639 <= powerCeil
  fixedTable :
    Q'.ofNat (640 * 640 * 640) * powerCeil <=
      terminalEndpointTableCoeff *
        (fixedEndpointWeight * fixedEndpointTable)

theorem fixedEndpointTable_nonneg : (0 : Q') <= fixedEndpointTable := by
  unfold fixedEndpointTable
  apply fsum_nonneg
  intro b
  exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
    (by
      unfold physicalEndpointPower
      exact qpow_nonneg _ (blockWeight_nonneg 8) _)

theorem integerThetaSum_nonneg_local
    {w : Q'} (hw0 : (0 : Q') <= w) (N : Nat) :
    (0 : Q') <= integerThetaSum w N := by
  unfold integerThetaSum
  rw [← MovingCutoff.fsum_eq_finSum]
  apply fsum_nonneg
  intro j
  unfold integerThetaTerm
  exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
    (qpow_nonneg _ (Q'.mul_nonneg _ _ hw0 hw0) _)

/-- The two certificate fields imply the genuine all-cutoff terminal theta
inequality.  No growing sum or cutoff-indexed certificate remains. -/
theorem TerminalEndpointFixedCertificate.terminalTheta
    (C : TerminalEndpointFixedCertificate)
    (k : Nat) (hk : 7 <= k) :
    let w4 := qpow (blockWeight (k + 1)) 4
    blockLength k * integerThetaTerm w4 (blockNcut k + 1) <=
      terminalOuterSplitCoeff *
        (w4 * integerThetaSum w4 (blockNcut k)) := by
  let H := 2 ^ (k - 7)
  let H3 := Q'.ofNat (H * H * H)
  let K3 := Q'.ofNat (640 * 640 * 640)
  let P := physicalEndpointPower k 639
  let U := C.powerCeil
  let c := terminalEndpointTableCoeff
  let wf := fixedEndpointWeight
  let T := fixedEndpointTable
  let w4 := qpow (blockWeight (k + 1)) 4
  let Theta := integerThetaSum w4 (blockNcut k)
  have hboundary := terminalBoundary_eq_cube_mul_endpointPower hk
  have hP : P <= U := C.endpointPower_le k hk
  have hH30 : (0 : Q') <= H3 := HeatKernelRGStep.zero_le_ofNat _
  have hK30 : (0 : Q') <= K3 := HeatKernelRGStep.zero_le_ofNat _
  have hc0 : (0 : Q') <= c := by
    unfold c terminalEndpointTableCoeff
    decide
  have hwf0 : (0 : Q') <= wf := by
    unfold wf fixedEndpointWeight
    exact qpow_nonneg _ (blockWeight_nonneg 8) 4
  have hw40 : (0 : Q') <= w4 := by
    unfold w4
    exact qpow_nonneg _ (blockWeight_nonneg (k + 1)) 4
  have hTheta0 : (0 : Q') <= Theta :=
    integerThetaSum_nonneg_local hw40 (blockNcut k)
  have hHP : H3 * P <= H3 * U :=
    Q'.mul_le_mul_of_nonneg_left _ _ H3 hP hH30
  have hleft : K3 * (H3 * P) <= K3 * (H3 * U) :=
    Q'.mul_le_mul_of_nonneg_left _ _ K3 hHP hK30
  have hfixedScaled : K3 * (H3 * U) <=
      c * (wf * (H3 * T)) := by
    have hmul := Q'.mul_le_mul_of_nonneg_left _ _ H3 C.fixedTable hH30
    have hleftEq : K3 * (H3 * U) ≈ H3 * (K3 * U) :=
      mul_nested_swap K3 H3 U
    have hrightEq : H3 * (c * (wf * T)) ≈
        c * (wf * (H3 * T)) := by
      refine Q'.eqv_trans _ (c * (H3 * (wf * T))) _
        (mul_nested_swap H3 c (wf * T)) ?_
      exact Q'.mul_eqv_congr_left c _ _ (mul_nested_swap H3 wf T)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleftEq)
      (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hrightEq))
  have htable := fixedEndpointTable_lower_integerTheta hk
  have htable' : H3 * T <= Q'.ofNat 3 * Theta := by
    simpa only [H, H3, T, w4, Theta] using htable
  have hwTable : wf * (H3 * T) <= wf * (Q'.ofNat 3 * Theta) :=
    Q'.mul_le_mul_of_nonneg_left _ _ wf htable' hwf0
  have hcTable : c * (wf * (H3 * T)) <=
      c * (wf * (Q'.ofNat 3 * Theta)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ c hwTable hc0
  have hwfloor : wf <= w4 := by
    simpa only [wf, w4] using fixedEndpointWeight_le hk
  have hthreeTheta0 : (0 : Q') <= Q'.ofNat 3 * Theta :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat 3) hTheta0
  have hweight : wf * (Q'.ofNat 3 * Theta) <=
      w4 * (Q'.ofNat 3 * Theta) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hwfloor hthreeTheta0
  have hcWeight : c * (wf * (Q'.ofNat 3 * Theta)) <=
      c * (w4 * (Q'.ofNat 3 * Theta)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ c hweight hc0
  have hfinal : c * (w4 * (Q'.ofNat 3 * Theta)) ≈
      terminalOuterSplitCoeff * (w4 * Theta) := by
    refine Q'.eqv_trans _ (c * (Q'.ofNat 3 * (w4 * Theta))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left c _ _
        (mul_nested_swap w4 (Q'.ofNat 3) Theta)
    · refine Q'.eqv_trans _ ((c * Q'.ofNat 3) * (w4 * Theta)) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      exact Q'.mul_eqv_congr_right _ _ _
        terminalEndpointTableCoeff_mul_three
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
      simpa only [H, H3, K3, P, w4] using hboundary))
    (Q'.le_trans' _ _ _ hleft
      (Q'.le_trans' _ _ _ hfixedScaled
        (Q'.le_trans' _ _ _ hcTable
          (Q'.le_trans' _ _ _ hcWeight (Q'.le_of_eqv hfinal)))))

#print axioms weightedEndpointStepBlocks_le_integerThetaSum
#print axioms blockCutoffLength_eq_640_dyadicBlocks
#print axioms weighted640EndpointSteps_le_integerThetaSum
#print axioms physicalEndpointPower_mono
#print axioms endpointStepPower_eq_physical
#print axioms physicalEndpointPower_seven_le
#print axioms shellCube_le_three_squareRangeMass
#print axioms physicalEndpointStepBlock_eq_mass_mul_power
#print axioms scaledFixedEndpointTable_le_physicalBlocks
#print axioms scaledFixedEndpointTable_eqv
#print axioms fixedEndpointTable_lower_integerTheta
#print axioms blockWeight_mono
#print axioms terminalBoundary_eq_cube_mul_endpointPower
#print axioms TerminalEndpointFixedCertificate.terminalTheta

end YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointStep
