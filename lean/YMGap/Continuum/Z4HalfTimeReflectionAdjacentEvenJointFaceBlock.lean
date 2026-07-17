/-
# Duplicate-free joint fixed-face block at the adjacent-even interface

A spatial face on the reflection plane is shared by four fixed spatial
links.  Its representation label must therefore be summed once and applied
simultaneously to all four open link channels.  Independent per-link
resummation duplicates that shared variable and is false; the first section
banks a closed exact counterexample.

The correct excited joint-face block is the common-label sum of a fourfold
product of fusion indicators.  This file proves a cutoff-uniform row bound
at the exact anchor.  The character dimension and four output-row counts
cost degree five, paid by the derived Gaussian tail at `1/400`.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceBlock

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FusedFreeSplit
open YMGap.Continuum.FusionPositivity
open YMGap.Continuum.MovingCutoff
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceResummedKernel
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenInterfaceLinkGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Fence: a shared face cannot be independently resummed per link -/

/-- One fixed label acts on two test links simultaneously.  This two-link
minor is already enough to refute duplicated independent resummation. -/
def sharedTwoLinkFixedFaceKernel (w : Q') : Q' :=
  fsum (fun fixed =>
    coeffW w fixed *
      (fusionInd 0 fixed 1 * fusionInd 0 fixed 0)) 2

/-- The false duplicated expression: each link receives its own independent
copy of the fixed-face sum. -/
def independentlyResummedTwoLinkKernel (w : Q') : Q' :=
  adjacentEvenResummedFaceChannelKernel 1 w 0 1 *
    adjacentEvenResummedFaceChannelKernel 1 w 0 0

theorem sharedTwoLinkFixedFaceKernel_anchor_eq_zero :
    sharedTwoLinkFixedFaceKernel anchorCoupling ≈ 0 := by
  decide

theorem independentlyResummedTwoLinkKernel_anchor_ne_zero :
    ¬ (independentlyResummedTwoLinkKernel anchorCoupling ≈ 0) := by
  decide

/-- Machine-checked fence against duplicating a shared fixed-face variable. -/
theorem sharedFace_not_independentLinkResummation :
    ¬ (sharedTwoLinkFixedFaceKernel anchorCoupling ≈
      independentlyResummedTwoLinkKernel anchorCoupling) := by
  decide

/-! ## 2. The duplicate-free four-channel block -/

structure FourChannels where
  first : Nat
  second : Nat
  third : Nat
  fourth : Nat
deriving DecidableEq

def fourFusionIndicator
    (source : FourChannels) (fixed : Nat)
    (target : FourChannels) : Q' :=
  fusionInd source.first fixed target.first *
    (fusionInd source.second fixed target.second *
      (fusionInd source.third fixed target.third *
        fusionInd source.fourth fixed target.fourth))

/-- The correct common-label excited block.  `faceCutoff` is the external
face cutoff; the four channel coordinates may live in a larger auxiliary
window. -/
def anchorJointFourExcitedFaceKernel
    (faceCutoff : Nat) (source target : FourChannels) : Q' :=
  fsum (fun index =>
    coeffW anchorCoupling (1 + index) *
      fourFusionIndicator source (1 + index) target) faceCutoff

theorem fourFusionIndicator_nonnegative
    (source : FourChannels) (fixed : Nat)
    (target : FourChannels) :
    (0 : Q') ≤ fourFusionIndicator source fixed target := by
  unfold fourFusionIndicator
  exact Q'.mul_nonneg _ _
    (fusionInd_nonneg source.first fixed target.first)
    (Q'.mul_nonneg _ _
      (fusionInd_nonneg source.second fixed target.second)
      (Q'.mul_nonneg _ _
        (fusionInd_nonneg source.third fixed target.third)
        (fusionInd_nonneg source.fourth fixed target.fourth)))

theorem fourFusionIndicator_symmetric
    (source : FourChannels) (fixed : Nat)
    (target : FourChannels) :
    fourFusionIndicator source fixed target ≈
      fourFusionIndicator target fixed source := by
  unfold fourFusionIndicator fusionInd
  rw [fusionOK_reverse_step source.first fixed target.first,
    fusionOK_reverse_step source.second fixed target.second,
    fusionOK_reverse_step source.third fixed target.third,
    fusionOK_reverse_step source.fourth fixed target.fourth]
  exact Q'.eqv_refl _

theorem anchorJointFourExcitedFaceKernel_nonnegative
    (faceCutoff : Nat) (source target : FourChannels) :
    (0 : Q') ≤
      anchorJointFourExcitedFaceKernel faceCutoff source target := by
  unfold anchorJointFourExcitedFaceKernel
  exact fsum_nonneg (fun index =>
    Q'.mul_nonneg _ _
      (coeffW_nonneg (by decide) (1 + index))
      (fourFusionIndicator_nonnegative
        source (1 + index) target)) faceCutoff

theorem anchorJointFourExcitedFaceKernel_symmetric
    (faceCutoff : Nat) (source target : FourChannels) :
    anchorJointFourExcitedFaceKernel faceCutoff source target ≈
      anchorJointFourExcitedFaceKernel faceCutoff target source := by
  unfold anchorJointFourExcitedFaceKernel
  apply fsum_eqv_congr
  intro index
  exact Q'.mul_eqv_congr_left _ _ _
    (fourFusionIndicator_symmetric source (1 + index) target)

/-! ## 3. Fourfold output-row factorization -/

def fourNestedSum
    (term : Nat → Nat → Nat → Nat → Q')
    (count : Nat) : Q' :=
  fsum (fun first =>
    fsum (fun second =>
      fsum (fun third =>
        fsum (term first second third) count)
        count) count) count

private theorem fsum4_congr
    (left right : Nat → Nat → Nat → Nat → Q')
    (h : ∀ first second third fourth,
      left first second third fourth ≈
        right first second third fourth)
    (count : Nat) :
    fourNestedSum left count ≈ fourNestedSum right count := by
  unfold fourNestedSum
  apply fsum_eqv_congr
  intro first
  apply fsum_eqv_congr
  intro second
  apply fsum_eqv_congr
  intro third
  apply fsum_eqv_congr
  intro fourth
  exact h first second third fourth

private theorem rightProduct4_reassociate
    (a b c d : Q') :
    a * (b * (c * d)) ≈ ((a * b) * c) * d := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a (b * c) d)) ?_
  exact Q'.mul_eqv_congr_right _ _ d
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))

private theorem fourNestedProduct_eq_productSums
    (first second third fourth : Nat → Q') (count : Nat) :
    fourNestedSum (fun i j k l =>
      first i * (second j * (third k * fourth l))) count ≈
      fsum first count *
        (fsum second count *
          (fsum third count * fsum fourth count)) := by
  unfold fourNestedSum
  have hfourth : ∀ i j k,
      fsum (fun l =>
          first i * (second j * (third k * fourth l))) count ≈
        ((first i * second j) * third k) *
          fsum fourth count := by
    intro i j k
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr _ _ (fun l =>
        rightProduct4_reassociate
          (first i) (second j) (third k) (fourth l)) count) ?_
    exact Q'.eqv_symm
      (fsum_const_mul
        ((first i * second j) * third k) fourth count)
  have hthird : ∀ i j,
      fsum (fun k =>
        fsum (fun l =>
          first i * (second j * (third k * fourth l))) count)
        count ≈
      (first i * second j) *
        (fsum third count * fsum fourth count) := by
    intro i j
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr _ _ (fun k => hfourth i j k) count) ?_
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr _ _ (fun k =>
        Q'.mul_assoc_eqv (first i * second j)
          (third k) (fsum fourth count)) count) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (fsum_const_mul
        (first i * second j)
        (fun k => third k * fsum fourth count) count)) ?_
    refine Q'.mul_eqv_congr_left (first i * second j) _ _ ?_
    exact Q'.eqv_symm (fsum_mul_const third
      (fsum fourth count) count)
  have hsecond : ∀ i,
      fsum (fun j =>
        fsum (fun k =>
          fsum (fun l =>
            first i * (second j * (third k * fourth l))) count)
          count) count ≈
      first i *
        (fsum second count *
          (fsum third count * fsum fourth count)) := by
    intro i
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr _ _ (fun j => hthird i j) count) ?_
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr _ _ (fun j =>
        Q'.mul_assoc_eqv (first i) (second j)
          (fsum third count * fsum fourth count)) count) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (fsum_const_mul (first i)
        (fun j => second j *
          (fsum third count * fsum fourth count)) count)) ?_
    exact Q'.mul_eqv_congr_left (first i) _ _
      (Q'.eqv_symm (fsum_mul_const second
        (fsum third count * fsum fourth count) count))
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ hsecond count) ?_
  exact Q'.eqv_symm
    (fsum_mul_const first
      (fsum second count *
        (fsum third count * fsum fourth count)) count)

private theorem fourNestedSum_swap_last
    (term : Nat → Nat → Nat → Nat → Nat → Q')
    (count indexCount : Nat) :
    fourNestedSum (fun a b c d =>
        fsum (fun index => term a b c d index) indexCount) count ≈
      fsum (fun index =>
        fourNestedSum (fun a b c d =>
          term a b c d index) count) indexCount := by
  unfold fourNestedSum
  have hthird : ∀ a b c,
      fsum (fun d =>
          fsum (fun index => term a b c d index) indexCount) count ≈
        fsum (fun index =>
          fsum (fun d => term a b c d index) count) indexCount := by
    intro a b c
    exact fsum_swap (fun d index => term a b c d index)
      count indexCount
  have hsecond : ∀ a b,
      fsum (fun c =>
        fsum (fun d =>
          fsum (fun index => term a b c d index) indexCount) count)
        count ≈
      fsum (fun index =>
        fsum (fun c => fsum (fun d =>
          term a b c d index) count) count) indexCount := by
    intro a b
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr _ _ (fun c => hthird a b c) count) ?_
    exact fsum_swap
      (fun c index =>
        fsum (fun d => term a b c d index) count)
      count indexCount
  have hfirst : ∀ a,
      fsum (fun b =>
        fsum (fun c =>
          fsum (fun d =>
            fsum (fun index => term a b c d index) indexCount) count)
          count) count ≈
      fsum (fun index =>
        fsum (fun b => fsum (fun c => fsum (fun d =>
          term a b c d index) count) count) count) indexCount := by
    intro a
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr _ _ (fun b => hsecond a b) count) ?_
    exact fsum_swap
      (fun b index =>
        fsum (fun c => fsum (fun d =>
          term a b c d index) count) count)
      count indexCount
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ hfirst count) ?_
  exact fsum_swap
    (fun a index =>
      fsum (fun b => fsum (fun c => fsum (fun d =>
        term a b c d index) count) count) count)
    count indexCount

/-! ## 4. Degree-five anchor payment -/

def anchorJointFourExcitedRowSum
    (faceCutoff channelCutoff : Nat)
    (source : FourChannels) : Q' :=
  fourNestedSum (fun first second third fourth =>
    anchorJointFourExcitedFaceKernel faceCutoff source
      ⟨first, second, third, fourth⟩) (channelCutoff + 1)

private theorem anchorCoeff_fourDimensions_eq_tailTerm
    (fixed : Nat) :
    coeffW anchorCoupling fixed * Q'.ofNat ((fixed + 1) ^ 4) ≈
      tailTerm anchorCoupling 5 fixed := by
  unfold coeffW dimQ tailTerm
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv
      (Q'.ofNat (fixed + 1))
      (qpow anchorCoupling (c4 fixed))
      (Q'.ofNat ((fixed + 1) ^ 4))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat (fixed + 1)) _ _
      (Q'.mul_comm_eqv
        (qpow anchorCoupling (c4 fixed))
        (Q'.ofNat ((fixed + 1) ^ 4)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv
      (Q'.ofNat (fixed + 1))
      (Q'.ofNat ((fixed + 1) ^ 4))
      (qpow anchorCoupling (c4 fixed)))) ?_
  apply Q'.mul_eqv_congr_right
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (ofNat_mul_eqv (fixed + 1) ((fixed + 1) ^ 4))) ?_
  have hpow : (fixed + 1) * (fixed + 1) ^ 4 =
      (fixed + 1) ^ 5 := by
    rw [Nat.pow_succ]
    exact Nat.mul_comm _ _
  rw [hpow]
  exact Q'.eqv_refl _

theorem anchorJointFourExcitedTail_le_half (faceCutoff : Nat) :
    tailWindow anchorCoupling 5 1 faceCutoff ≤ dyad 1 := by
  exact tail_modulus
    (w := anchorCoupling) (by decide) (by decide)
    5 1 1 (by decide) (by decide) faceCutoff

private theorem rightProduct4_le_pow
    {a b c d bound : Q'}
    (hb0 : (0 : Q') ≤ b)
    (hc0 : (0 : Q') ≤ c) (hd0 : (0 : Q') ≤ d)
    (habound : a ≤ bound) (hbbound : b ≤ bound)
    (hcbound : c ≤ bound) (hdbound : d ≤ bound)
    (hbound0 : (0 : Q') ≤ bound) :
    a * (b * (c * d)) ≤
      bound * (bound * (bound * bound)) := by
  have hcd1 : c * d ≤ bound * d :=
    Q'.mul_le_mul_of_nonneg_right c bound d hcbound hd0
  have hcd2 : bound * d ≤ bound * bound :=
    Q'.mul_le_mul_of_nonneg_left d bound bound hdbound hbound0
  have hcd : c * d ≤ bound * bound :=
    Q'.le_trans' _ _ _ hcd1 hcd2
  have hcd0 : (0 : Q') ≤ c * d := Q'.mul_nonneg _ _ hc0 hd0
  have hbb1 : b * (c * d) ≤ bound * (c * d) :=
    Q'.mul_le_mul_of_nonneg_right b bound (c * d) hbbound hcd0
  have hboundSquare0 : (0 : Q') ≤ bound * bound :=
    Q'.mul_nonneg _ _ hbound0 hbound0
  have hbb2 : bound * (c * d) ≤ bound * (bound * bound) :=
    Q'.mul_le_mul_of_nonneg_left
      (c * d) (bound * bound) bound hcd hbound0
  have hbb : b * (c * d) ≤ bound * (bound * bound) :=
    Q'.le_trans' _ _ _ hbb1 hbb2
  have hbcd0 : (0 : Q') ≤ b * (c * d) :=
    Q'.mul_nonneg _ _ hb0 hcd0
  have hlast1 : a * (b * (c * d)) ≤
      bound * (b * (c * d)) :=
    Q'.mul_le_mul_of_nonneg_right
      a bound (b * (c * d)) habound hbcd0
  have hlast2 : bound * (b * (c * d)) ≤
      bound * (bound * (bound * bound)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ bound hbb hbound0
  exact Q'.le_trans' _ _ _ hlast1 hlast2

/-- Uniform heterogeneous row bound for the duplicate-free four-link block.
The fixed label cutoff and the open-channel cutoff are independent. -/
theorem anchorJointFourExcitedRowSum_le_half
    (faceCutoff channelCutoff : Nat) (source : FourChannels) :
    anchorJointFourExcitedRowSum
        faceCutoff channelCutoff source ≤ dyad 1 := by
  let count := channelCutoff + 1
  let term : Nat → Nat → Nat → Nat → Nat → Q' :=
    fun first second third fourth index =>
      coeffW anchorCoupling (1 + index) *
        fourFusionIndicator source (1 + index)
          ⟨first, second, third, fourth⟩
  have hswap :
      anchorJointFourExcitedRowSum
          faceCutoff channelCutoff source ≈
        fsum (fun index =>
          fourNestedSum (fun first second third fourth =>
            term first second third fourth index) count)
          faceCutoff := by
    unfold anchorJointFourExcitedRowSum
      anchorJointFourExcitedFaceKernel
    exact fourNestedSum_swap_last term count faceCutoff
  have hterm : ∀ index,
      fourNestedSum (fun first second third fourth =>
          term first second third fourth index) count ≤
        tailTerm anchorCoupling 5 (1 + index) := by
    intro index
    let fixed := 1 + index
    let coeff := coeffW anchorCoupling fixed
    let row0 := fsum (fun target =>
      fusionInd source.first fixed target) count
    let row1 := fsum (fun target =>
      fusionInd source.second fixed target) count
    let row2 := fsum (fun target =>
      fusionInd source.third fixed target) count
    let row3 := fsum (fun target =>
      fusionInd source.fourth fixed target) count
    have hfactor :
        fourNestedSum (fun first second third fourth =>
            term first second third fourth index) count ≈
          coeff * (row0 * (row1 * (row2 * row3))) := by
      have hrearrange :
          fourNestedSum (fun first second third fourth =>
              term first second third fourth index) count ≈
            fourNestedSum (fun first second third fourth =>
              (coeff * fusionInd source.first fixed first) *
                (fusionInd source.second fixed second *
                  (fusionInd source.third fixed third *
                    fusionInd source.fourth fixed fourth))) count := by
        apply fsum4_congr
        intro first second third fourth
        unfold term fourFusionIndicator fixed coeff
        exact Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (coeffW anchorCoupling (1 + index))
            (fusionInd source.first (1 + index) first)
            (fusionInd source.second (1 + index) second *
              (fusionInd source.third (1 + index) third *
                fusionInd source.fourth (1 + index) fourth)))
      have hproduct := fourNestedProduct_eq_productSums
        (fun first => coeff * fusionInd source.first fixed first)
        (fun second => fusionInd source.second fixed second)
        (fun third => fusionInd source.third fixed third)
        (fun fourth => fusionInd source.fourth fixed fourth) count
      have hcoeffRow :
          fsum (fun first =>
            coeff * fusionInd source.first fixed first) count ≈
            coeff * row0 := by
        unfold row0
        exact Q'.eqv_symm
          (fsum_const_mul coeff
            (fun target => fusionInd source.first fixed target) count)
      exact Q'.eqv_trans _ _ _ hrearrange
        (Q'.eqv_trans _ _ _ hproduct
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _
              (row1 * (row2 * row3)) hcoeffRow)
            (Q'.mul_assoc_eqv coeff row0
              (row1 * (row2 * row3)))))
    have hrow0 : row0 ≤ Q'.ofNat (fixed + 1) := by
      unfold row0 count
      exact fusionOutputRowCount_le_dimension
        channelCutoff source.first fixed
    have hrow1 : row1 ≤ Q'.ofNat (fixed + 1) := by
      unfold row1 count
      exact fusionOutputRowCount_le_dimension
        channelCutoff source.second fixed
    have hrow2 : row2 ≤ Q'.ofNat (fixed + 1) := by
      unfold row2 count
      exact fusionOutputRowCount_le_dimension
        channelCutoff source.third fixed
    have hrow3 : row3 ≤ Q'.ofNat (fixed + 1) := by
      unfold row3 count
      exact fusionOutputRowCount_le_dimension
        channelCutoff source.fourth fixed
    have hrow0nonneg : (0 : Q') ≤ row0 := by
      unfold row0
      exact fsum_nonneg (fun target =>
        fusionInd_nonneg source.first fixed target) count
    have hrow1nonneg : (0 : Q') ≤ row1 := by
      unfold row1
      exact fsum_nonneg (fun target =>
        fusionInd_nonneg source.second fixed target) count
    have hrow2nonneg : (0 : Q') ≤ row2 := by
      unfold row2
      exact fsum_nonneg (fun target =>
        fusionInd_nonneg source.third fixed target) count
    have hrow3nonneg : (0 : Q') ≤ row3 := by
      unfold row3
      exact fsum_nonneg (fun target =>
        fusionInd_nonneg source.fourth fixed target) count
    have hrows : row0 * (row1 * (row2 * row3)) ≤
        Q'.ofNat (fixed + 1) *
          (Q'.ofNat (fixed + 1) *
            (Q'.ofNat (fixed + 1) * Q'.ofNat (fixed + 1))) :=
      rightProduct4_le_pow
        hrow1nonneg hrow2nonneg hrow3nonneg
        hrow0 hrow1 hrow2 hrow3 (zero_le_ofNat _)
    have hpowEqv :
        Q'.ofNat (fixed + 1) *
            (Q'.ofNat (fixed + 1) *
              (Q'.ofNat (fixed + 1) * Q'.ofNat (fixed + 1))) ≈
          Q'.ofNat ((fixed + 1) ^ 4) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm
              (ofNat_mul_eqv (fixed + 1) (fixed + 1))))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm
            (ofNat_mul_eqv (fixed + 1)
              ((fixed + 1) * (fixed + 1))))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (ofNat_mul_eqv (fixed + 1)
            ((fixed + 1) * ((fixed + 1) * (fixed + 1))))) ?_
      have hnat :
          (fixed + 1) * ((fixed + 1) *
            ((fixed + 1) * (fixed + 1))) = (fixed + 1) ^ 4 := by
        simp [Nat.pow_succ, Nat.mul_assoc]
      rw [hnat]
      exact Q'.eqv_refl _
    have hrowsPow : row0 * (row1 * (row2 * row3)) ≤
        Q'.ofNat ((fixed + 1) ^ 4) :=
      Q'.le_trans' _ _ _ hrows (Q'.le_of_eqv hpowEqv)
    have hscaled :
        coeff * (row0 * (row1 * (row2 * row3))) ≤
          coeff * Q'.ofNat ((fixed + 1) ^ 4) :=
      Q'.mul_le_mul_of_nonneg_left _ _ coeff hrowsPow
        (coeffW_nonneg (by decide) fixed)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv
          (anchorCoeff_fourDimensions_eq_tailTerm fixed)))
  have hsum := fsum_mono hterm faceCutoff
  have htail :
      fsum (fun index =>
        tailTerm anchorCoupling 5 (1 + index)) faceCutoff =
        tailWindow anchorCoupling 5 1 faceCutoff := by
    unfold tailWindow
    rw [← fsum_eq_finSum]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hswap)
    (Q'.le_trans' _ _ _ hsum (by
      rw [htail]
      exact anchorJointFourExcitedTail_le_half faceCutoff))

/-! ## 5. Exact finite four-channel enumeration -/

def fourChannelRawSpace (channelCutoff : Nat) :
    List (((Nat × Nat) × Nat) × Nat) :=
  let channels := List.range (channelCutoff + 1)
  cartesian (cartesian (cartesian channels channels) channels) channels

def rawToFourChannels
    (raw : ((Nat × Nat) × Nat) × Nat) : FourChannels :=
  ⟨raw.1.1.1, raw.1.1.2, raw.1.2, raw.2⟩

def fourChannelSpace (channelCutoff : Nat) : List FourChannels :=
  (fourChannelRawSpace channelCutoff).map rawToFourChannels

private theorem rangeNodupLocal (count : Nat) :
    (List.range count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ count ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = count := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl count)

private theorem rawToFourChannels_injective
    {left right : ((Nat × Nat) × Nat) × Nat}
    (h : rawToFourChannels left = rawToFourChannels right) :
    left = right := by
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := left
  obtain ⟨⟨⟨a', b'⟩, c'⟩, d'⟩ := right
  simp only [rawToFourChannels] at h
  injection h with ha hb hc hd
  simp [ha, hb, hc, hd]

theorem fourChannelSpace_nodup (channelCutoff : Nat) :
    (fourChannelSpace channelCutoff).Nodup := by
  let channels := List.range (channelCutoff + 1)
  have hchannels : channels.Nodup := rangeNodupLocal _
  have hraw : (fourChannelRawSpace channelCutoff).Nodup := by
    unfold fourChannelRawSpace
    exact cartesian_nodup _ _
      (cartesian_nodup _ _
        (cartesian_nodup channels channels hchannels hchannels)
        hchannels)
      hchannels
  unfold fourChannelSpace
  exact nodup_map_of_injOn rawToFourChannels
    (fourChannelRawSpace channelCutoff) hraw
    (fun left _ right _ h => rawToFourChannels_injective h)

private theorem listQSum_cartesian_eq_nested_local
    {A B : Type} (value : A × B → Q')
    (left : List A) (right : List B) :
    listQSum value (cartesian left right) ≈
      listQSum (fun first =>
        listQSum (fun second => value (first, second)) right) left := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value
      (fun first => right.map (fun second => (first, second))) left) ?_
  apply listQSum_congr
  intro first
  rw [listQSum_map]
  exact Q'.eqv_refl _

private theorem listQSum_fourChannelSpace_eqv_nested
    (channelCutoff : Nat) (value : FourChannels → Q') :
    listQSum value (fourChannelSpace channelCutoff) ≈
      fourNestedSum (fun first second third fourth =>
        value ⟨first, second, third, fourth⟩) (channelCutoff + 1) := by
  let channels := List.range (channelCutoff + 1)
  let pairs := cartesian channels channels
  let triples := cartesian pairs channels
  let rawValue : (((Nat × Nat) × Nat) × Nat) → Q' :=
    fun raw => value (rawToFourChannels raw)
  have hmap :
      listQSum value (fourChannelSpace channelCutoff) =
        listQSum rawValue (fourChannelRawSpace channelCutoff) := by
    unfold fourChannelSpace rawValue
    exact listQSum_map value rawToFourChannels _
  rw [hmap]
  change listQSum rawValue (cartesian triples channels) ≈ _
  refine Q'.eqv_trans _ _ _
    (listQSum_cartesian_eq_nested_local
      rawValue triples channels) ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_cartesian_eq_nested_local
      (fun pair : ((Nat × Nat) × Nat) =>
        listQSum (fun fourth => rawValue (pair, fourth)) channels)
      pairs channels) ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_cartesian_eq_nested_local
      (fun pair : Nat × Nat =>
        listQSum (fun third =>
          listQSum (fun fourth =>
            rawValue ((pair, third), fourth)) channels) channels)
      channels channels) ?_
  unfold fourNestedSum rawValue rawToFourChannels
  refine Q'.eqv_trans _ _ _
    (listQSum_range_eq_fsum
      (fun first =>
        listQSum
          (fun second =>
            listQSum
              (fun third =>
                listQSum
                  (fun fourth => value
                    ⟨first, second, third, fourth⟩)
                  (List.range (channelCutoff + 1)))
              (List.range (channelCutoff + 1)))
          (List.range (channelCutoff + 1)))
      (channelCutoff + 1)) ?_
  apply fsum_eqv_congr
  intro first
  refine Q'.eqv_trans _ _ _
    (listQSum_range_eq_fsum
      (fun second =>
        listQSum
          (fun third =>
            listQSum
              (fun fourth => value
                ⟨first, second, third, fourth⟩)
              (List.range (channelCutoff + 1)))
          (List.range (channelCutoff + 1)))
      (channelCutoff + 1)) ?_
  apply fsum_eqv_congr
  intro second
  refine Q'.eqv_trans _ _ _
    (listQSum_range_eq_fsum
      (fun third =>
        listQSum
          (fun fourth => value
            ⟨first, second, third, fourth⟩)
          (List.range (channelCutoff + 1)))
      (channelCutoff + 1)) ?_
  apply fsum_eqv_congr
  intro third
  exact listQSum_range_eq_fsum
    (fun fourth => value ⟨first, second, third, fourth⟩)
    (channelCutoff + 1)

def anchorJointFourExcitedListRowSum
    (faceCutoff channelCutoff : Nat) (source : FourChannels) : Q' :=
  listQSum
    (anchorJointFourExcitedFaceKernel faceCutoff source)
    (fourChannelSpace channelCutoff)

theorem anchorJointFourExcitedListRowSum_le_half
    (faceCutoff channelCutoff : Nat) (source : FourChannels) :
    anchorJointFourExcitedListRowSum
        faceCutoff channelCutoff source ≤ dyad 1 := by
  have hid :
      anchorJointFourExcitedListRowSum
          faceCutoff channelCutoff source ≈
        anchorJointFourExcitedRowSum
          faceCutoff channelCutoff source := by
    unfold anchorJointFourExcitedListRowSum
      anchorJointFourExcitedRowSum
    exact listQSum_fourChannelSpace_eqv_nested
      channelCutoff
      (anchorJointFourExcitedFaceKernel faceCutoff source)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hid)
    (anchorJointFourExcitedRowSum_le_half
      faceCutoff channelCutoff source)

/-! ## 6. A constructive index for the finite channel list -/

def reverseListAt (fallback : A) : List A → Nat → A
  | [], _ => fallback
  | head :: tail, index =>
      if index < tail.length then reverseListAt fallback tail index
      else head

def reverseListPosition [DecidableEq A] (item : A) : List A → Nat
  | [] => 0
  | head :: tail =>
      if item = head then tail.length
      else reverseListPosition item tail

private theorem reverseListPosition_lt_of_mem
    [DecidableEq A] (item : A) : ∀ {items : List A},
    item ∈ items → reverseListPosition item items < items.length
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      by_cases hhead : item = head
      · simp [reverseListPosition, hhead]
      · have htail : item ∈ tail := by
          rcases List.mem_cons.mp hmem with heq | htail
          · exact False.elim (hhead heq)
          · exact htail
        simp only [reverseListPosition, if_neg hhead,
          List.length_cons]
        exact Nat.lt_succ_of_lt
          (reverseListPosition_lt_of_mem item htail)

private theorem reverseListAt_position_of_mem
    [DecidableEq A] (fallback item : A) : ∀ {items : List A},
    item ∈ items →
      reverseListAt fallback items
        (reverseListPosition item items) = item
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      by_cases hhead : item = head
      · subst item
        simp [reverseListPosition, reverseListAt]
      · have htail : item ∈ tail := by
          rcases List.mem_cons.mp hmem with heq | htail
          · exact False.elim (hhead heq)
          · exact htail
        have hlt := reverseListPosition_lt_of_mem item htail
        simp only [reverseListPosition, if_neg hhead, reverseListAt,
          if_pos hlt]
        exact reverseListAt_position_of_mem fallback item htail

private theorem fsum_reverseListAt_eqv_listQSum
    (fallback : A) (value : A → Q') : ∀ items : List A,
    fsum (fun index => value (reverseListAt fallback items index))
      items.length ≈ listQSum value items
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      simp only [List.length_cons, fsum_succ, listQSum]
      have hprefix :
          fsum (fun index =>
            value (reverseListAt fallback (head :: tail) index))
              tail.length ≈
            fsum (fun index =>
              value (reverseListAt fallback tail index))
              tail.length := by
        apply fsum_eqv_congr_lt
        intro index hindex
        simp only [reverseListAt, if_pos hindex]
        exact Q'.eqv_refl _
      have hlast :
          reverseListAt fallback (head :: tail) tail.length = head := by
        simp [reverseListAt]
      rw [hlast]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ hprefix) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (fsum_reverseListAt_eqv_listQSum fallback value tail)) ?_
      exact Q'.add_comm_eqv _ _

def zeroFourChannels : FourChannels := ⟨0, 0, 0, 0⟩

def fourChannelAt (channelCutoff index : Nat) : FourChannels :=
  reverseListAt zeroFourChannels
    (fourChannelSpace channelCutoff) index

def fourChannelPosition
    (channelCutoff : Nat) (state : FourChannels) : Nat :=
  reverseListPosition state (fourChannelSpace channelCutoff)

theorem fourChannelPosition_lt
    {channelCutoff : Nat} {state : FourChannels}
    (hstate : state ∈ fourChannelSpace channelCutoff) :
    fourChannelPosition channelCutoff state <
      (fourChannelSpace channelCutoff).length :=
  reverseListPosition_lt_of_mem state hstate

theorem fourChannelAt_position
    {channelCutoff : Nat} {state : FourChannels}
    (hstate : state ∈ fourChannelSpace channelCutoff) :
    fourChannelAt channelCutoff
      (fourChannelPosition channelCutoff state) = state :=
  reverseListAt_position_of_mem zeroFourChannels state hstate

def anchorJointFourExcitedIndexKernel
    (faceCutoff channelCutoff source target : Nat) : Q' :=
  anchorJointFourExcitedFaceKernel faceCutoff
    (fourChannelAt channelCutoff source)
    (fourChannelAt channelCutoff target)

theorem anchorJointFourExcitedIndexKernel_nonnegative
    (faceCutoff channelCutoff source target : Nat) :
    (0 : Q') ≤ anchorJointFourExcitedIndexKernel
      faceCutoff channelCutoff source target :=
  anchorJointFourExcitedFaceKernel_nonnegative _ _ _

theorem anchorJointFourExcitedIndexKernel_symmetric
    (faceCutoff channelCutoff source target : Nat) :
    anchorJointFourExcitedIndexKernel
        faceCutoff channelCutoff source target ≈
      anchorJointFourExcitedIndexKernel
        faceCutoff channelCutoff target source :=
  anchorJointFourExcitedFaceKernel_symmetric _ _ _

theorem anchorJointFourExcitedIndexRowSum_le_one
    (faceCutoff channelCutoff source : Nat) :
    finiteRowSum
        (anchorJointFourExcitedIndexKernel
          faceCutoff channelCutoff)
        (fourChannelSpace channelCutoff).length source ≤ (1 : Q') := by
  have hindex :
      finiteRowSum
          (anchorJointFourExcitedIndexKernel
            faceCutoff channelCutoff)
          (fourChannelSpace channelCutoff).length source ≈
        anchorJointFourExcitedListRowSum
          faceCutoff channelCutoff
          (fourChannelAt channelCutoff source) := by
    unfold finiteRowSum anchorJointFourExcitedIndexKernel
      anchorJointFourExcitedListRowSum
    exact fsum_reverseListAt_eqv_listQSum zeroFourChannels
      (anchorJointFourExcitedFaceKernel faceCutoff
        (fourChannelAt channelCutoff source))
      (fourChannelSpace channelCutoff)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hindex)
    (Q'.le_trans' _ _ _
      (anchorJointFourExcitedListRowSum_le_half
        faceCutoff channelCutoff
        (fourChannelAt channelCutoff source)) (by
          unfold dyad YMGap.Constructive.HalfPow.half
          decide))

/-! ## 7. One-hot extraction of the dominated matrix -/

private theorem localDeltaFinSum
    (value : Nat → Q') (source count : Nat)
    (hsource : source < count) :
    finSum (fun target => delta source target * value target) count ≈
      value source := by
  have h := delta_fsum value source count hsource
  rw [fsum_eq_finSum] at h
  exact h

private theorem delta_mul_self_eqv (source target : Nat) :
    delta source target * delta source target ≈
      delta source target := by
  unfold delta
  split <;> decide

private theorem distinct_delta_product_eqv_zero
    {first second target : Nat} (hne : first ≠ second) :
    delta first target * delta second target ≈ 0 := by
  unfold delta
  by_cases hfirst : target = first
  · rw [if_pos hfirst, if_neg (by
      intro hsecond
      exact hne (hfirst.symm.trans hsecond))]
    exact Q'.mul_zero_eqv _
  · rw [if_neg hfirst]
    exact Q'.zero_mul_eqv _

private theorem gramDiagonalOneHot_eqv_delta
    {first second count : Nat}
    (hfirst : first < count) (hsecond : second < count) :
    gramDiagonalPair (delta first) (delta second) count ≈
      delta first second := by
  unfold gramDiagonalPair
  by_cases heq : first = second
  · subst second
    refine Q'.eqv_trans _ _ _
      (finSum_eqv_congr _ _ (fun target =>
        delta_mul_self_eqv first target) count) ?_
    refine Q'.eqv_trans _ _ _
      (finSum_eqv_congr _ _ (fun target =>
        Q'.eqv_symm (Q'.mul_one_eqv (delta first target))) count) ?_
    refine Q'.eqv_trans _ _ _
      (localDeltaFinSum (fun _ => (1 : Q')) first count hfirst) ?_
    unfold delta
    rw [if_pos rfl]
    exact Q'.eqv_refl _
  · refine Q'.eqv_trans _ _ _
      (finSum_eqv_congr _ _ (fun target =>
        distinct_delta_product_eqv_zero heq) count) ?_
    rw [finSum_zero_seq]
    unfold delta
    rw [if_neg (fun h => heq h.symm)]
    exact Q'.eqv_refl _

private theorem mul_delta_rearrange
    (weight leftDelta rightDelta : Q') :
    weight * (leftDelta * rightDelta) ≈
      rightDelta * (weight * leftDelta) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv weight leftDelta rightDelta)) ?_
  exact Q'.mul_comm_eqv (weight * leftDelta) rightDelta

private theorem gramMatrixOneHot_eqv_entry
    (matrix : Nat → Nat → Q')
    {first second count : Nat}
    (hfirst : first < count) (hsecond : second < count) :
    gramMatrixBilinear matrix (delta first) (delta second) count ≈
      matrix first second := by
  unfold gramMatrixBilinear gramDoubleSum
  have hinner : ∀ row,
      finSum (fun column =>
        matrix row column *
          (delta first row * delta second column)) count ≈
        matrix row second * delta first row := by
    intro row
    refine Q'.eqv_trans _ _ _
      (finSum_eqv_congr _ _ (fun column =>
        mul_delta_rearrange (matrix row column)
          (delta first row) (delta second column)) count) ?_
    exact localDeltaFinSum
      (fun column => matrix row column * delta first row)
      second count hsecond
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ _ hinner count) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ _ (fun row =>
      Q'.mul_comm_eqv (matrix row second) (delta first row)) count) ?_
  exact localDeltaFinSum
    (fun row => matrix row second) first count hfirst

def jointFourOneHot
    (channelCutoff : Nat) (state : FourChannels) (channel : Nat) : Q' :=
  delta (fourChannelPosition channelCutoff state) channel

def anchorJointFourDominantFeaturePair
    (faceCutoff channelCutoff : Nat)
    (left right : FourChannels) : Q' :=
  gramDominantFeaturePair
    (anchorJointFourExcitedIndexKernel faceCutoff channelCutoff)
    (jointFourOneHot channelCutoff left)
    (jointFourOneHot channelCutoff right)
    (fourChannelSpace channelCutoff).length

theorem anchorJointFourDominantFeaturePair_eqv_delta_add_excited
    {faceCutoff channelCutoff : Nat} {left right : FourChannels}
    (hleft : left ∈ fourChannelSpace channelCutoff)
    (hright : right ∈ fourChannelSpace channelCutoff) :
    anchorJointFourDominantFeaturePair
        faceCutoff channelCutoff left right ≈
      delta (fourChannelPosition channelCutoff left)
          (fourChannelPosition channelCutoff right) +
        anchorJointFourExcitedFaceKernel
          faceCutoff left right := by
  let count := (fourChannelSpace channelCutoff).length
  let first := fourChannelPosition channelCutoff left
  let second := fourChannelPosition channelCutoff right
  have hfirst : first < count := fourChannelPosition_lt hleft
  have hsecond : second < count := fourChannelPosition_lt hright
  have hgeneric :=
    gramDominantFeaturePair_eqv_identityPlusBilinear
      (anchorJointFourExcitedIndexKernel
        faceCutoff channelCutoff)
      (jointFourOneHot channelCutoff left)
      (jointFourOneHot channelCutoff right) count
      (anchorJointFourExcitedIndexKernel_symmetric
        faceCutoff channelCutoff)
  have hdiag :
      gramDiagonalPair
          (jointFourOneHot channelCutoff left)
          (jointFourOneHot channelCutoff right) count ≈
        delta first second := by
    exact gramDiagonalOneHot_eqv_delta hfirst hsecond
  have hmatrix :
      gramMatrixBilinear
          (anchorJointFourExcitedIndexKernel
            faceCutoff channelCutoff)
          (jointFourOneHot channelCutoff left)
          (jointFourOneHot channelCutoff right) count ≈
        anchorJointFourExcitedFaceKernel
          faceCutoff left right := by
    refine Q'.eqv_trans _ _ _
      (gramMatrixOneHot_eqv_entry
        (anchorJointFourExcitedIndexKernel
          faceCutoff channelCutoff) hfirst hsecond) ?_
    unfold anchorJointFourExcitedIndexKernel
    rw [fourChannelAt_position hleft,
      fourChannelAt_position hright]
    exact Q'.eqv_refl _
  unfold anchorJointFourDominantFeaturePair
    gramIdentityPlusBilinear at hgeneric
  exact Q'.eqv_trans _ _ _ hgeneric
    (Q'.add_eqv_congr' hdiag hmatrix)

/-! ## 8. Identification with the literal heterogeneous heat-kernel block -/

/-- Literal common-label fixed-face sum.  Only the face label is cut off by
`faceCutoff`; the channel space is supplied separately by the caller. -/
def anchorJointFourResummedFaceKernel
    (faceCutoff : Nat) (source target : FourChannels) : Q' :=
  listQSum (fun fixed =>
    coeffAt (heatKernelPacket faceCutoff anchorCoupling) fixed *
      fourFusionIndicator source fixed target)
    (List.range (faceCutoff + 1))

theorem anchorJointFourResummedFaceKernel_eqv_vacuum_add_excited
    (faceCutoff : Nat) (source target : FourChannels) :
    anchorJointFourResummedFaceKernel faceCutoff source target ≈
      fourFusionIndicator source 0 target +
        anchorJointFourExcitedFaceKernel faceCutoff source target := by
  let packetTerm : Nat → Q' := fun fixed =>
    coeffAt (heatKernelPacket faceCutoff anchorCoupling) fixed *
      fourFusionIndicator source fixed target
  let fusionTerm : Nat → Q' := fun fixed =>
    coeffW anchorCoupling fixed *
      fourFusionIndicator source fixed target
  have htoFsum :
      anchorJointFourResummedFaceKernel faceCutoff source target ≈
        fsum packetTerm (faceCutoff + 1) := by
    unfold anchorJointFourResummedFaceKernel
    exact listQSum_range_eq_fsum packetTerm (faceCutoff + 1)
  have hpacket :
      fsum packetTerm (faceCutoff + 1) ≈
        fsum fusionTerm (faceCutoff + 1) := by
    apply fsum_eqv_congr_lt
    intro fixed hfixed
    unfold packetTerm fusionTerm
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_of_eq (coeffAt_heatKernelPacket hfixed))
  have hpeel :
      fsum fusionTerm (faceCutoff + 1) ≈
        fusionTerm 0 +
          fsum (fun index => fusionTerm (index + 1)) faceCutoff :=
    fsum_peel fusionTerm faceCutoff
  have hvacuum :
      fusionTerm 0 ≈ fourFusionIndicator source 0 target := by
    unfold fusionTerm
    rw [coeffW_zero]
    exact Q'.one_mul_eqv _
  have hexcited :
      fsum (fun index => fusionTerm (index + 1)) faceCutoff ≈
        anchorJointFourExcitedFaceKernel faceCutoff source target := by
    unfold fusionTerm anchorJointFourExcitedFaceKernel
    apply fsum_eqv_congr
    intro index
    have hindex : index + 1 = 1 + index := by omega
    rw [hindex]
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ htoFsum
    (Q'.eqv_trans _ _ _ hpacket
      (Q'.eqv_trans _ _ _ hpeel
        (Q'.add_eqv_congr' hvacuum hexcited)))

private theorem fusionInd_zero_middle_eq_delta
    (source target : Nat) :
    fusionInd source 0 target = delta source target := by
  unfold fusionInd delta
  rw [fusionOK_zero_right_eq_decide]
  by_cases heq : target = source
  · rw [if_pos heq]
    simp [heq]
  · rw [if_neg heq]
    simp [heq]

private theorem fourFusionIndicator_zero_eqv_delta_position
    {channelCutoff : Nat} {source target : FourChannels}
    (hsource : source ∈ fourChannelSpace channelCutoff)
    (htarget : target ∈ fourChannelSpace channelCutoff) :
    fourFusionIndicator source 0 target ≈
      delta (fourChannelPosition channelCutoff source)
        (fourChannelPosition channelCutoff target) := by
  have hpositionInjective :
      fourChannelPosition channelCutoff source =
          fourChannelPosition channelCutoff target →
        source = target := by
    intro hposition
    have hsourceAt := fourChannelAt_position hsource
    have htargetAt := fourChannelAt_position htarget
    rw [hposition] at hsourceAt
    exact hsourceAt.symm.trans htargetAt
  by_cases hstate : source = target
  · subst target
    unfold fourFusionIndicator
    rw [fusionInd_zero_middle_eq_delta,
      fusionInd_zero_middle_eq_delta,
      fusionInd_zero_middle_eq_delta,
      fusionInd_zero_middle_eq_delta]
    unfold delta
    simp
    decide
  · have hposition :
        fourChannelPosition channelCutoff source ≠
          fourChannelPosition channelCutoff target :=
      fun h => hstate (hpositionInjective h)
    have hdeltaPosition :
        delta (fourChannelPosition channelCutoff source)
          (fourChannelPosition channelCutoff target) = 0 := by
      unfold delta
      rw [if_neg (fun h => hposition h.symm)]
    unfold fourFusionIndicator
    rw [fusionInd_zero_middle_eq_delta,
      fusionInd_zero_middle_eq_delta,
      fusionInd_zero_middle_eq_delta,
      fusionInd_zero_middle_eq_delta, hdeltaPosition]
    obtain ⟨a, b, c, d⟩ := source
    obtain ⟨a', b', c', d'⟩ := target
    by_cases ha : a' = a <;>
      by_cases hb : b' = b <;>
      by_cases hc : c' = c <;>
      by_cases hd : d' = d <;>
      simp [delta, ha, hb, hc, hd] at * <;>
      decide

/-- Exact heterogeneous block identification: the literal common-label sum
is the dominated feature pairing, with face cutoff and channel cutoff kept
independent. -/
theorem anchorJointFourResummedFaceKernel_eqv_dominantFeatures
    {faceCutoff channelCutoff : Nat} {source target : FourChannels}
    (hsource : source ∈ fourChannelSpace channelCutoff)
    (htarget : target ∈ fourChannelSpace channelCutoff) :
    anchorJointFourResummedFaceKernel faceCutoff source target ≈
      anchorJointFourDominantFeaturePair
        faceCutoff channelCutoff source target := by
  refine Q'.eqv_trans _ _ _
    (anchorJointFourResummedFaceKernel_eqv_vacuum_add_excited
      faceCutoff source target) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (fourFusionIndicator_zero_eqv_delta_position
        hsource htarget)) ?_
  exact Q'.eqv_symm
    (anchorJointFourDominantFeaturePair_eqv_delta_add_excited
      hsource htarget)

/-! ## 9. Explicit `GramRep` for the literal joint-face block -/

def anchorJointFourResidualFeatureMatrix
    (faceCutoff channelCutoff : Nat)
    (state : Nat → FourChannels) (left right : Nat) : Q' :=
  gramDominantResidualPair
    (anchorJointFourExcitedIndexKernel faceCutoff channelCutoff)
    (jointFourOneHot channelCutoff (state left))
    (jointFourOneHot channelCutoff (state right))
    (fourChannelSpace channelCutoff).length

def anchorJointFourEdgeFeatureMatrix
    (faceCutoff channelCutoff : Nat)
    (state : Nat → FourChannels) (left right : Nat) : Q' :=
  gramSymmetricEdgePair
    (anchorJointFourExcitedIndexKernel faceCutoff channelCutoff)
    (jointFourOneHot channelCutoff (state left))
    (jointFourOneHot channelCutoff (state right))
    (fourChannelSpace channelCutoff).length

def anchorJointFourFeatureMatrix
    (faceCutoff channelCutoff : Nat)
    (state : Nat → FourChannels) (left right : Nat) : Q' :=
  anchorJointFourResidualFeatureMatrix
      faceCutoff channelCutoff state left right +
    anchorJointFourEdgeFeatureMatrix
      faceCutoff channelCutoff state left right

def anchorJointFourResidualFeatureGramRep
    (faceCutoff channelCutoff : Nat)
    (state : Nat → FourChannels) :
    GramRep (anchorJointFourResidualFeatureMatrix
      faceCutoff channelCutoff state) where
  r := (fourChannelSpace channelCutoff).length
  d := fun channel =>
    (1 : Q') + -finiteRowSum
      (anchorJointFourExcitedIndexKernel faceCutoff channelCutoff)
      (fourChannelSpace channelCutoff).length channel
  hd := fun channel =>
    Q'.sub_nonneg_of_le
      (anchorJointFourExcitedIndexRowSum_le_one
        faceCutoff channelCutoff channel)
  v := fun channel configuration =>
    jointFourOneHot channelCutoff (state configuration) channel
  hM := by
    intro left right
    exact Q'.eqv_refl _

private theorem localHalfNestedFinSum_eqv_flattened
    (term : Nat → Nat → Q') (count : Nat) :
    YMGap.Constructive.HalfPow.half *
        finSum (fun row => finSum (term row) count) count ≈
      finSum (fun packed =>
        YMGap.Constructive.HalfPow.half *
          term (packed / count) (packed % count))
        (count * count) := by
  have hpushOuter :
      YMGap.Constructive.HalfPow.half *
          finSum (fun row => finSum (term row) count) count ≈
        finSum (fun row =>
          YMGap.Constructive.HalfPow.half *
            finSum (term row) count) count :=
    const_mul_finSum
      (fun row => finSum (term row) count)
      YMGap.Constructive.HalfPow.half count
  have hpushInner :
      finSum (fun row =>
          YMGap.Constructive.HalfPow.half *
            finSum (term row) count) count ≈
        finSum (fun row => finSum (fun column =>
          YMGap.Constructive.HalfPow.half *
            term row column) count) count := by
    apply finSum_eqv_congr
    intro row
    exact const_mul_finSum (term row)
      YMGap.Constructive.HalfPow.half count
  exact Q'.eqv_trans _ _ _ hpushOuter
    (Q'.eqv_trans _ _ _ hpushInner
      (Q'.eqv_symm
        (finSum_flatten
          (fun row column =>
            YMGap.Constructive.HalfPow.half * term row column)
          count count)))

def anchorJointFourEdgeFeatureGramRep
    (faceCutoff channelCutoff : Nat)
    (state : Nat → FourChannels) :
    GramRep (anchorJointFourEdgeFeatureMatrix
      faceCutoff channelCutoff state) where
  r := (fourChannelSpace channelCutoff).length *
    (fourChannelSpace channelCutoff).length
  d := fun packed =>
    let count := (fourChannelSpace channelCutoff).length
    YMGap.Constructive.HalfPow.half *
      anchorJointFourExcitedIndexKernel faceCutoff channelCutoff
        (packed / count) (packed % count)
  hd := fun packed =>
    Q'.mul_nonneg _ _ (by decide)
      (anchorJointFourExcitedIndexKernel_nonnegative
        faceCutoff channelCutoff _ _)
  v := fun packed configuration =>
    let count := (fourChannelSpace channelCutoff).length
    jointFourOneHot channelCutoff (state configuration)
        (packed / count) +
      jointFourOneHot channelCutoff (state configuration)
        (packed % count)
  hM := by
    intro left right
    unfold anchorJointFourEdgeFeatureMatrix
      gramSymmetricEdgePair gramDoubleSum
    let count := (fourChannelSpace channelCutoff).length
    let term : Nat → Nat → Q' := fun source target =>
      anchorJointFourExcitedIndexKernel
          faceCutoff channelCutoff source target *
        ((jointFourOneHot channelCutoff (state left) source +
          jointFourOneHot channelCutoff (state left) target) *
        (jointFourOneHot channelCutoff (state right) source +
          jointFourOneHot channelCutoff (state right) target))
    have hflatten := localHalfNestedFinSum_eqv_flattened term count
    refine Q'.eqv_trans _ _ _ hflatten ?_
    apply finSum_eqv_congr
    intro packed
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        YMGap.Constructive.HalfPow.half
        (anchorJointFourExcitedIndexKernel
          faceCutoff channelCutoff
          (packed / count) (packed % count))
        ((jointFourOneHot channelCutoff (state left)
              (packed / count) +
            jointFourOneHot channelCutoff (state left)
              (packed % count)) *
          (jointFourOneHot channelCutoff (state right)
              (packed / count) +
            jointFourOneHot channelCutoff (state right)
              (packed % count))))

def anchorJointFourFeatureGramRep
    (faceCutoff channelCutoff : Nat)
    (state : Nat → FourChannels) :
    GramRep (anchorJointFourFeatureMatrix
      faceCutoff channelCutoff state) :=
  gramRep_add
    (anchorJointFourResidualFeatureGramRep
      faceCutoff channelCutoff state)
    (anchorJointFourEdgeFeatureGramRep
      faceCutoff channelCutoff state)

def anchorJointFourProductionMatrix
    (faceCutoff : Nat) (state : Nat → FourChannels)
    (left right : Nat) : Q' :=
  anchorJointFourResummedFaceKernel
    faceCutoff (state left) (state right)

/-- Explicit Gram carrier for one literal, duplicate-free fixed-face block.
The exact production specialization is `channelCutoff = 6*K`. -/
def anchorJointFourProductionGramRep
    (faceCutoff channelCutoff : Nat)
    (state : Nat → FourChannels)
    (hstate : ∀ configuration,
      state configuration ∈ fourChannelSpace channelCutoff) :
    GramRep (anchorJointFourProductionMatrix faceCutoff state) := by
  let rep := anchorJointFourFeatureGramRep
    faceCutoff channelCutoff state
  exact {
    r := rep.r
    d := rep.d
    hd := rep.hd
    v := rep.v
    hM := fun left right =>
      Q'.eqv_trans _ _ _
        (anchorJointFourResummedFaceKernel_eqv_dominantFeatures
          (hstate left) (hstate right))
        (rep.hM left right)
  }

/-! ## 10. Duplicate-free finite face-network gluing -/

def anchorJointFaceNetworkKernel
    (faceCutoff : Nat)
    (localChannels : Nat → Nat → FourChannels) :
    Nat → Nat → Nat → Q'
  | 0, _, _ => 1
  | faceCount + 1, left, right =>
      anchorJointFaceNetworkKernel
          faceCutoff localChannels faceCount left right *
        anchorJointFourProductionMatrix faceCutoff
          (localChannels faceCount) left right

/-- Each fixed face is resummed exactly once, while shared boundary-link
channels may occur in several local four-tuples.  Repeated Schur products
give the explicit finite network Gram. -/
def anchorJointFaceNetworkGramRep
    (faceCutoff channelCutoff : Nat)
    (localChannels : Nat → Nat → FourChannels)
    (hstate : ∀ face configuration,
      localChannels face configuration ∈
        fourChannelSpace channelCutoff) :
    ∀ faceCount,
      GramRep (anchorJointFaceNetworkKernel
        faceCutoff localChannels faceCount)
  | 0 => onesGramRep
  | faceCount + 1 =>
      schur_product
        (anchorJointFaceNetworkGramRep
          faceCutoff channelCutoff localChannels hstate faceCount)
        (anchorJointFourProductionGramRep
          faceCutoff channelCutoff
          (localChannels faceCount) (hstate faceCount))

theorem anchorJointFaceNetworkQuadratic_nonnegative
    (faceCutoff channelCutoff : Nat)
    (localChannels : Nat → Nat → FourChannels)
    (hstate : ∀ face configuration,
      localChannels face configuration ∈
        fourChannelSpace channelCutoff)
    (faceCount : Nat) (coefficient : Nat → Q')
    (configurationCount : Nat) :
    (0 : Q') ≤ gramQuadForm
      (anchorJointFaceNetworkKernel
        faceCutoff localChannels faceCount)
      coefficient configurationCount :=
  gramPSD_quadForm_nonneg
    (anchorJointFaceNetworkGramRep
      faceCutoff channelCutoff localChannels hstate faceCount)
    coefficient configurationCount

#print axioms sharedFace_not_independentLinkResummation
#print axioms fourFusionIndicator_nonnegative
#print axioms fourFusionIndicator_symmetric
#print axioms anchorJointFourExcitedFaceKernel_nonnegative
#print axioms anchorJointFourExcitedFaceKernel_symmetric
#print axioms anchorJointFourExcitedTail_le_half
#print axioms anchorJointFourExcitedRowSum_le_half
#print axioms fourChannelSpace_nodup
#print axioms anchorJointFourExcitedListRowSum_le_half
#print axioms anchorJointFourExcitedIndexRowSum_le_one
#print axioms anchorJointFourDominantFeaturePair_eqv_delta_add_excited
#print axioms anchorJointFourResummedFaceKernel_eqv_vacuum_add_excited
#print axioms anchorJointFourResummedFaceKernel_eqv_dominantFeatures
#print axioms anchorJointFourResidualFeatureGramRep
#print axioms anchorJointFourEdgeFeatureGramRep
#print axioms anchorJointFourFeatureGramRep
#print axioms anchorJointFourProductionGramRep
#print axioms anchorJointFaceNetworkGramRep
#print axioms anchorJointFaceNetworkQuadratic_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceBlock
