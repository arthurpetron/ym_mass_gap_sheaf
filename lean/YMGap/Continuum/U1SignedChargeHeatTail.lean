/-
# Quantitative all-label tails for the one-coordinate U(1) heat series

The BF4 U(1) carrier enumerates signed charges by natural labels

    0, +1, -1, +2, -2, ...

through `BF4U1SameCarrierPushforward.decodeCharge`.  This module groups that
actual carrier into complete signed pairs and proves an explicit geometric
tail for the one-coordinate heat series

    1 + 2 * sum_{n >= 1} w^(n^2),       0 < w < 1.

The Gaussian exponent is used only to dominate the `n`-th signed shell by
`2 w^(n+1)`.  Consequently the closed tail after `M` nonzero signed pairs is

    2 w^(M+1) / (1-w).

The data-level cutoff is obtained from `HKConvGen.powBaseCutoff`; no choice
operator is used.

## Honest scope

This is the exact one-coordinate, all-label U(1) heat carrier and a
quantitative rational tail theorem at a fixed rational nome `0 < w < 1`.
It does not identify a BF4 continuum trajectory or prove a spacing-uniform
bound as `w` approaches an endpoint.

## Constructivity

Only exact `Q'` order/equivalence, finite sums, and explicit natural cutoffs
are used.  There is no `Classical.*`, `Real`, `native_decide`, `sorry`,
noncomputable declaration, or custom axiom.
-/

import YMGap.Continuum.BF4U1SameCarrierPushforward
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.KPLimit

namespace YMGap.Continuum.U1SignedChargeHeatTail

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.AbelianFusionCLT
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.HKConvGen

local infix:50 " ≈ " => Q'.eqv

private theorem add_nonnegative {a b : Q'}
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ a + b := by
  have h := Q'.add_le_add ha hb
  rw [Q'.zero_add'] at h
  exact h

/-! ## 1. The actual signed-label heat carrier -/

/-- Heat weight of one natural carrier label.  By `decodeCharge_natAbs`, this
is `w^(|charge|^2)` for the signed charge decoded from `label`. -/
def signedChargeHeatWeight (w : Q') (label : Nat) : Q' :=
  abelCoeff w (chargeMagnitude label)

/-- The two labels carrying charges `+(n+1)` and `-(n+1)`. -/
def signedChargeShell (w : Q') (n : Nat) : Q' :=
  signedChargeHeatWeight w (2 * n + 1) +
    signedChargeHeatWeight w (2 * n + 2)

/-- The first `K` complete nonzero signed-charge pairs, together with the
vacuum charge. -/
def pairedHeatPartial (w : Q') (K : Nat) : Q' :=
  1 + finSum (signedChargeShell w) K

/-- The same partial sum written directly on the BF4 natural-label carrier.
The length `2*K+1` includes labels `0,...,2*K`. -/
def symmetricLabelPartial (w : Q') (K : Nat) : Q' :=
  finSum (signedChargeHeatWeight w) (2 * K + 1)

@[simp] theorem chargeMagnitude_positive_label (n : Nat) :
    chargeMagnitude (2 * n + 1) = n + 1 := by
  unfold chargeMagnitude
  omega

@[simp] theorem chargeMagnitude_negative_label (n : Nat) :
    chargeMagnitude (2 * n + 2) = n + 1 := by
  unfold chargeMagnitude
  omega

theorem signedChargeHeatWeight_decode (w : Q') (label : Nat) :
    signedChargeHeatWeight w label =
      abelCoeff w (decodeCharge label).natAbs := by
  unfold signedChargeHeatWeight
  rw [decodeCharge_natAbs]

theorem signedChargeShell_eq (w : Q') (n : Nat) :
    signedChargeShell w n =
      abelCoeff w (n + 1) + abelCoeff w (n + 1) := by
  simp [signedChargeShell, signedChargeHeatWeight]

/-- Grouping the actual natural labels into complete signed pairs loses no
term: labels `0,...,2K` are exactly the vacuum plus the first `K` shells. -/
theorem symmetricLabelPartial_eqv_paired (w : Q') :
    ∀ K, symmetricLabelPartial w K ≈ pairedHeatPartial w K
  | 0 => by
      change ((0 : Q') + abelCoeff w 0) ≈ (1 + 0)
      simp only [abelCoeff_zero]
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq (Q'.zero_add' 1)) ?_
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' 1))
  | K + 1 => by
      have ih := symmetricLabelPartial_eqv_paired w K
      change
        finSum (signedChargeHeatWeight w) (2 * K + 1) ≈
          1 + finSum (signedChargeShell w) K at ih
      have hlen : 2 * (K + 1) + 1 = (2 * K + 1) + 2 := by omega
      rw [symmetricLabelPartial, hlen]
      change
        (finSum (signedChargeHeatWeight w) (2 * K + 1) +
            signedChargeHeatWeight w (2 * K + 1)) +
              signedChargeHeatWeight w (2 * K + 2) ≈
          1 + (finSum (signedChargeShell w) K +
            signedChargeShell w K)
      have hpair :
          signedChargeHeatWeight w (2 * K + 1) +
              signedChargeHeatWeight w (2 * K + 2) =
            signedChargeShell w K := rfl
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv
          (finSum (signedChargeHeatWeight w) (2 * K + 1))
          (signedChargeHeatWeight w (2 * K + 1))
          (signedChargeHeatWeight w (2 * K + 2))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (finSum (signedChargeHeatWeight w) (2 * K + 1))
          _ _ (Q'.eqv_of_eq hpair)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (signedChargeShell w K) ih) ?_
      exact Q'.add_assoc_eqv 1 (finSum (signedChargeShell w) K)
        (signedChargeShell w K)

/-! ## 2. Gaussian shell domination by a geometric series -/

/-- The strict-fold heat power agrees extensionally with the ordinary
constructive rational power. -/
theorem rgQpow_eqv_pow (w : Q') :
    ∀ n, RGTransport.qpow w n ≈ w ^ n
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      have ih := rgQpow_eqv_pow w n
      show RGTransport.qpow w n * w ≈ w * w ^ n
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ w ih) ?_
      exact Q'.mul_comm_eqv (w ^ n) w

theorem abelCoeff_eqv_pow (w : Q') (n : Nat) :
    abelCoeff w n ≈ w ^ (n * n) :=
  rgQpow_eqv_pow w (n * n)

/-- One Gaussian coefficient in shell `n` is bounded by the corresponding
geometric coefficient `w^(n+1)`. -/
theorem abelCoeff_succ_le_geometric
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (n : Nat) :
    abelCoeff w (n + 1) ≤ w * w ^ n := by
  have hexp : n + 1 ≤ (n + 1) * (n + 1) := by
    have hOne : 1 ≤ n + 1 := by omega
    have hmul := Nat.mul_le_mul_left (n + 1) hOne
    simpa using hmul
  have hpow :
      w ^ ((n + 1) * (n + 1)) ≤ w ^ (n + 1) :=
    pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hexp
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (abelCoeff_eqv_pow w (n + 1))) ?_
  refine Q'.le_trans' _ _ _ hpow ?_
  exact Q'.le_of_eqv (Q'.eqv_refl (w * w ^ n))

/-- Both signed charges in shell `n` are dominated by the geometric
increment `(w+w) * w^n`. -/
theorem signedChargeShell_le_geo
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (n : Nat) :
    signedChargeShell w n ≤ geoIncrBase (w + w) w n := by
  rw [signedChargeShell_eq]
  have hone := abelCoeff_succ_le_geometric hw0 hw1 n
  have htwo :
      abelCoeff w (n + 1) + abelCoeff w (n + 1) ≤
        w * w ^ n + w * w ^ n :=
    Q'.add_le_add hone hone
  refine Q'.le_trans' _ _ _ htwo ?_
  unfold geoIncrBase
  exact Q'.le_of_eqv
    (Q'.eqv_symm (Q'.add_mul_eqv w w (w ^ n)))

theorem signedChargeShell_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (n : Nat) :
    (0 : Q') ≤ signedChargeShell w n := by
  rw [signedChargeShell_eq]
  exact add_nonnegative
    (abelCoeff_nonneg (Q'.le_of_lt hw0) (n + 1))
    (abelCoeff_nonneg (Q'.le_of_lt hw0) (n + 1))

theorem pairedHeatPartial_step_upper
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (n : Nat) :
    pairedHeatPartial w (n + 1) ≤
      pairedHeatPartial w n + geoIncrBase (w + w) w n := by
  unfold pairedHeatPartial
  rw [finSum_succ]
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.add_assoc_eqv 1 (finSum (signedChargeShell w) n)
          (signedChargeShell w n)))) ?_
  exact Q'.add_le_add_left
    (1 + finSum (signedChargeShell w) n) _ _
    (signedChargeShell_le_geo hw0 hw1 n)

theorem pairedHeatPartial_step_lower
    {w : Q'} (hw0 : (0 : Q') < w) (n : Nat) :
    pairedHeatPartial w n ≤
      pairedHeatPartial w (n + 1) + geoIncrBase (w + w) w n := by
  have hshell0 := signedChargeShell_nonnegative hw0 n
  have hmono :
      pairedHeatPartial w n ≤ pairedHeatPartial w (n + 1) := by
    unfold pairedHeatPartial
    rw [finSum_succ]
    refine Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg
        (1 + finSum (signedChargeShell w) n)
        (signedChargeShell w n) hshell0) ?_
    exact Q'.le_of_eqv
      (Q'.add_assoc_eqv 1 (finSum (signedChargeShell w) n)
        (signedChargeShell w n))
  have hgeo0 :
      (0 : Q') ≤ geoIncrBase (w + w) w n := by
    unfold geoIncrBase
    exact Q'.mul_nonneg _ _
      (add_nonnegative (Q'.le_of_lt hw0) (Q'.le_of_lt hw0))
      (Q'.pow_nonneg w (Q'.le_of_lt hw0) n)
  exact Q'.le_trans' _ _ _ hmono
    (Q'.add_le_self_of_nonneg
      (pairedHeatPartial w (n + 1))
      (geoIncrBase (w + w) w n) hgeo0)

/-! ## 3. Closed finite-block tail -/

/-- Closed geometric majorant after `M` complete nonzero signed pairs. -/
def signedChargeClosedTail (w : Q') (M : Nat) : Q' :=
  geoTailBase (w + w) w M

theorem signedChargeClosedTail_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (M : Nat) :
    (0 : Q') ≤ signedChargeClosedTail w M := by
  exact geoTailBase_nonneg
    (add_nonnegative (Q'.le_of_lt hw0) (Q'.le_of_lt hw0))
    (Q'.le_of_lt hw0) M

/-- Every later finite symmetric all-label partial lies below the retained
partial plus the explicit closed tail. -/
theorem pairedHeatPartial_block_upper
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (M L : Nat) :
    pairedHeatPartial w (M + L) ≤
      pairedHeatPartial w M + signedChargeClosedTail w M := by
  have htel :=
    telescope_up
      (pairedHeatPartial w)
      (geoIncrBase (w + w) w)
      (pairedHeatPartial_step_upper hw0 hw1) M L
  have hsum :
      finSum (fun i => geoIncrBase (w + w) w (M + i)) L ≤
        signedChargeClosedTail w M := by
    exact geoTailBase_series_le
      (add_nonnegative (Q'.le_of_lt hw0) (Q'.le_of_lt hw0))
      hw0 hw1 M L
  exact Q'.le_trans' _ _ _ htel
    (Q'.add_le_add_left (pairedHeatPartial w M) _ _ hsum)

/-- Reverse finite-block estimate.  The partials are monotone, so the same
closed nonnegative tail is more than sufficient in this direction. -/
theorem pairedHeatPartial_block_lower
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (M L : Nat) :
    pairedHeatPartial w M ≤
      pairedHeatPartial w (M + L) + signedChargeClosedTail w M := by
  have htel :=
    telescope_lo
      (pairedHeatPartial w)
      (geoIncrBase (w + w) w)
      (pairedHeatPartial_step_lower hw0) M L
  have hsum :
      finSum (fun i => geoIncrBase (w + w) w (M + i)) L ≤
        signedChargeClosedTail w M := by
    exact geoTailBase_series_le
      (add_nonnegative (Q'.le_of_lt hw0) (Q'.le_of_lt hw0))
      hw0 hw1 M L
  exact Q'.le_trans' _ _ _ htel
    (Q'.add_le_add_left (pairedHeatPartial w (M + L)) _ _ hsum)

theorem pairedHeatPartial_block_twoSided
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (M L : Nat) :
    pairedHeatPartial w (M + L) + -pairedHeatPartial w M ≤
        signedChargeClosedTail w M ∧
      pairedHeatPartial w M + -pairedHeatPartial w (M + L) ≤
        signedChargeClosedTail w M := by
  exact
    ⟨Q'.sub_le_of_le_add (pairedHeatPartial_block_upper hw0 hw1 M L),
      Q'.sub_le_of_le_add (pairedHeatPartial_block_lower hw0 hw1 M L)⟩

/-- The same upper block estimate stated directly on the BF4 natural-label
partials.  This is the form consumed by a later score-tube estimate. -/
theorem symmetricLabelPartial_block_upper
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (M L : Nat) :
    symmetricLabelPartial w (M + L) ≤
      symmetricLabelPartial w M + signedChargeClosedTail w M := by
  have hfuture := symmetricLabelPartial_eqv_paired w (M + L)
  have hbase := symmetricLabelPartial_eqv_paired w M
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfuture) ?_
  refine Q'.le_trans' _ _ _
    (pairedHeatPartial_block_upper hw0 hw1 M L) ?_
  exact Q'.add_le_add_right
    (pairedHeatPartial w M) (symmetricLabelPartial w M)
    (signedChargeClosedTail w M) (Q'.ge_of_eqv hbase)

/-- Reverse block estimate on the actual natural-label partials. -/
theorem symmetricLabelPartial_block_lower
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (M L : Nat) :
    symmetricLabelPartial w M ≤
      symmetricLabelPartial w (M + L) +
        signedChargeClosedTail w M := by
  have hfuture := symmetricLabelPartial_eqv_paired w (M + L)
  have hbase := symmetricLabelPartial_eqv_paired w M
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hbase) ?_
  refine Q'.le_trans' _ _ _
    (pairedHeatPartial_block_lower hw0 hw1 M L) ?_
  exact Q'.add_le_add_right
    (pairedHeatPartial w (M + L))
    (symmetricLabelPartial w (M + L))
    (signedChargeClosedTail w M) (Q'.ge_of_eqv hfuture)

theorem symmetricLabelPartial_block_twoSided
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (M L : Nat) :
    symmetricLabelPartial w (M + L) + -symmetricLabelPartial w M ≤
        signedChargeClosedTail w M ∧
      symmetricLabelPartial w M + -symmetricLabelPartial w (M + L) ≤
        signedChargeClosedTail w M := by
  exact
    ⟨Q'.sub_le_of_le_add
        (symmetricLabelPartial_block_upper hw0 hw1 M L),
      Q'.sub_le_of_le_add
        (symmetricLabelPartial_block_lower hw0 hw1 M L)⟩

/-! ## 4. Explicit spacing/nome-dependent cutoff -/

/-- Positive constant in
`signedChargeClosedTail w M ≈ signedChargeTailConstant w * w^M`. -/
def signedChargeTailConstant (w : Q') : Q' :=
  (w + w) * HKConv.divPos 1 (1 + (-w))

theorem signedChargeTailConstant_pos
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < signedChargeTailConstant w :=
  HKPos.q_mul_pos
    (Q'.add_pos hw0 hw0)
    (HKConv.divPos_pos (by decide))

theorem signedChargeTailConstant_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') ≤ signedChargeTailConstant w :=
  Q'.le_of_lt (signedChargeTailConstant_pos hw0)

/-- Explicit number of complete nonzero signed-charge pairs needed for
tolerance `ε`. -/
def signedChargePairCutoff (w ε : Q') : Nat :=
  powBaseCutoff w
    (HKConv.divPos ε (signedChargeTailConstant w))

/-- Corresponding natural-label partial length.  It retains precisely labels
`0,...,2*pairCutoff`, hence is a cutoff on the actual BF4 carrier. -/
def signedChargeLabelCutoff (w ε : Q') : Nat :=
  2 * signedChargePairCutoff w ε + 1

/-- The explicit cutoff makes the closed all-label tail at most `ε`. -/
theorem signedChargeClosedTail_le_of_cutoff
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε) (M : Nat)
    (hM : signedChargePairCutoff w ε ≤ M) :
    signedChargeClosedTail w M ≤ ε := by
  have hCnum :
      0 < (signedChargeTailConstant w).num :=
    CReal.num_pos_of_pos (signedChargeTailConstant_pos hw0)
  have hδpos :
      (0 : Q') <
        HKConv.divPos ε (signedChargeTailConstant w) :=
    HKConv.divPos_pos (CReal.num_pos_of_pos hε)
  have hCδ :
      (signedChargeTailConstant w *
          HKConv.divPos ε (signedChargeTailConstant w)) ≈ ε := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv
        (signedChargeTailConstant w)
        (HKConv.divPos ε (signedChargeTailConstant w))) ?_
    exact HKConv.divPos_mul_eqv hCnum
  have hpow :
      w ^ M ≤ HKConv.divPos ε (signedChargeTailConstant w) := by
    refine Q'.le_trans' _ _ _
      (pow_base_antitone
        (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hM) ?_
    exact pow_base_le_cutoff hw0 hw1 hδpos
  have he :
      signedChargeClosedTail w M ≈
        signedChargeTailConstant w * w ^ M := by
    show (((w + w) * w ^ M) *
        HKConv.divPos 1 (1 + (-w))) ≈
      (((w + w) * HKConv.divPos 1 (1 + (-w))) * w ^ M)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (w + w) (w ^ M)
        (HKConv.divPos 1 (1 + (-w)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (w + w) _ _
        (Q'.mul_comm_eqv (w ^ M)
          (HKConv.divPos 1 (1 + (-w))))) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (w + w)
        (HKConv.divPos 1 (1 + (-w))) (w ^ M))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left
      (w ^ M)
      (HKConv.divPos ε (signedChargeTailConstant w))
      (signedChargeTailConstant w)
      hpow (signedChargeTailConstant_nonnegative hw0)) ?_
  exact Q'.le_of_eqv hCδ

/-- Quantitative all-label Cauchy modulus at the explicit paired cutoff. -/
theorem symmetricLabelPartial_cauchy_of_cutoff
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε) (M L : Nat)
    (hM : signedChargePairCutoff w ε ≤ M) :
    pairedHeatPartial w (M + L) + -pairedHeatPartial w M ≤ ε ∧
      pairedHeatPartial w M + -pairedHeatPartial w (M + L) ≤ ε := by
  have htwo := pairedHeatPartial_block_twoSided hw0 hw1 M L
  have htail := signedChargeClosedTail_le_of_cutoff hw0 hw1 hε M hM
  exact
    ⟨Q'.le_trans' _ _ _ htwo.1 htail,
      Q'.le_trans' _ _ _ htwo.2 htail⟩

/-- Cauchy modulus stated on the actual BF4 natural-label carrier. -/
theorem actualLabelPartial_cauchy_of_cutoff
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε) (M L : Nat)
    (hM : signedChargePairCutoff w ε ≤ M) :
    symmetricLabelPartial w (M + L) + -symmetricLabelPartial w M ≤ ε ∧
      symmetricLabelPartial w M + -symmetricLabelPartial w (M + L) ≤ ε := by
  have htwo := symmetricLabelPartial_block_twoSided hw0 hw1 M L
  have htail := signedChargeClosedTail_le_of_cutoff hw0 hw1 hε M hM
  exact
    ⟨Q'.le_trans' _ _ _ htwo.1 htail,
      Q'.le_trans' _ _ _ htwo.2 htail⟩

/-! ## 5. Type-valued cutoff datum for a later score tube -/

/-- Explicit analytic datum exported to a later BF4 score-tube construction.

`pairStage` is the number of complete nonzero signed pairs retained.
`labelLength` is the corresponding length on the actual natural carrier.
The two `corridor` fields are uniform in every later finite extension and
therefore can be rescaled by a score Lipschitz constant before constructing
an `AtlasScoreTube`.  No score-functional Lipschitz estimate is asserted
here. -/
structure SignedChargeToleranceDatum
    (w ε : Q') : Type where
  pairStage : Nat
  pairStage_eq : pairStage = signedChargePairCutoff w ε
  labelLength : Nat
  labelLength_eq : labelLength = 2 * pairStage + 1
  tail_nonnegative :
    (0 : Q') ≤ signedChargeClosedTail w pairStage
  tail_le_error :
    signedChargeClosedTail w pairStage ≤ ε
  corridor_forward :
    ∀ L : Nat,
      symmetricLabelPartial w (pairStage + L) +
          -symmetricLabelPartial w pairStage ≤ ε
  corridor_backward :
    ∀ L : Nat,
      symmetricLabelPartial w pairStage +
          -symmetricLabelPartial w (pairStage + L) ≤ ε

/-- Canonical score-tube cutoff datum at every rational `0 < w < 1` and
positive tolerance. -/
def signedChargeToleranceDatum
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε) :
    SignedChargeToleranceDatum w ε where
  pairStage := signedChargePairCutoff w ε
  pairStage_eq := rfl
  labelLength := signedChargeLabelCutoff w ε
  labelLength_eq := rfl
  tail_nonnegative :=
    signedChargeClosedTail_nonnegative hw0
      (signedChargePairCutoff w ε)
  tail_le_error :=
    signedChargeClosedTail_le_of_cutoff hw0 hw1 hε
      (signedChargePairCutoff w ε) (Nat.le_refl _)
  corridor_forward := by
    intro L
    exact
      (actualLabelPartial_cauchy_of_cutoff hw0 hw1 hε
        (signedChargePairCutoff w ε) L (Nat.le_refl _)).1
  corridor_backward := by
    intro L
    exact
      (actualLabelPartial_cauchy_of_cutoff hw0 hw1 hε
        (signedChargePairCutoff w ε) L (Nat.le_refl _)).2

end YMGap.Continuum.U1SignedChargeHeatTail

#print axioms YMGap.Continuum.U1SignedChargeHeatTail.symmetricLabelPartial_eqv_paired
#print axioms YMGap.Continuum.U1SignedChargeHeatTail.signedChargeShell_le_geo
#print axioms YMGap.Continuum.U1SignedChargeHeatTail.pairedHeatPartial_block_twoSided
#print axioms YMGap.Continuum.U1SignedChargeHeatTail.signedChargeClosedTail_le_of_cutoff
#print axioms YMGap.Continuum.U1SignedChargeHeatTail.symmetricLabelPartial_cauchy_of_cutoff
#print axioms YMGap.Continuum.U1SignedChargeHeatTail.actualLabelPartial_cauchy_of_cutoff
#print axioms YMGap.Continuum.U1SignedChargeHeatTail.signedChargeToleranceDatum
