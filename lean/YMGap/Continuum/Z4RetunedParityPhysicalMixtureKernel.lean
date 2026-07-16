/-
# A retuned multi-face parity/physical mixture kernel

This module constructs a genuine finite-state positive Markov kernel on the
existing cutoff-one coarse spin-foam state space.  Its source-dependent
branch is the exact cellular-parity pushforward.  Its second branch refreshes
from the normalized coarse physical finite-volume law.  At mixing parameter
`retuneCube w` the kernel is positive and row normalized for `0 <= w <= 1`.

For every explicitly normalized source mass the pushed law has the exact
pointwise decomposition

  mu K = r (D_* mu) + (1-r) q

and hence exact pointwise remainder `r (D_* mu - q)`, together with an
explicit scaled L1 bound.

Two limitations are deliberately fenced.  First, the physical refresh branch
is globally source-independent, so this is not yet a spatially local block
kernel.  Second, the old full-box face coordinates have no exact reflection
action; reflection-positive compatibility remains open until this kernel is
localized and transported to the boundary-complete slab.
-/

import YMGap.Continuum.Z4OldBoxReflectionKernelFence
import YMGap.Continuum.Z4DyadicSU2ParityActivityMatchedDefect
import YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
import YMGap.Continuum.RationalProjectiveRetuneAllCutoffs
import YMGap.Continuum.TsumDeriv

namespace YMGap.Continuum.Z4RetunedParityPhysicalMixtureKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CoarseUnitCubeActivity
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicSU2ParityActivityMatchedDefect
open YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
open YMGap.Continuum.Z4DyadicSU2ParitySpinKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4UnitCubeBareCouplingShift
open YMGap.Continuum.RationalProjectiveRetuneAllCutoffs

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl
/-- Cancellation-free exact rational rebracketing closer. -/
local macro "ac_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

/-! ## 1. Exact normalized finite physical masses -/

/-- The normalized physical mass of one labelling in the canonical finite
spin-foam enumeration. -/
def normalizedPhysicalMass (w : Q') (hw0 : (0 : Q') ≤ w)
    (K n : Nat) (physical : EdgeLabelling) : Q' :=
  Q'.divPos (parametricKPhysicalTerm w K n physical)
    (parametricKPhysicalPartition w K n)
    (couplingKPhysicalPartition_pos hw0 K n)

theorem normalizedPhysicalMass_nonnegative
    (w : Q') (hw0 : (0 : Q') ≤ w) (K n : Nat)
    (physical : EdgeLabelling) :
    (0 : Q') ≤ normalizedPhysicalMass w hw0 K n physical := by
  unfold normalizedPhysicalMass Q'.divPos
  exact Q'.mul_nonneg _ _
    (parametricKPhysicalTerm_nonnegative hw0 K n physical)
    (Q'.le_of_lt
      (Q'.recipPos_pos _ (couplingKPhysicalPartition_pos hw0 K n)))

/-- The physical point masses sum exactly to one over the full canonical
finite labelling enumeration. -/
theorem normalizedPhysicalMass_total
    (w : Q') (hw0 : (0 : Q') ≤ w) (K n : Nat) :
    listQSum (normalizedPhysicalMass w hw0 K n)
        (explicitPhysicalLabellings K n) ≈ 1 := by
  unfold normalizedPhysicalMass Q'.divPos
    parametricKPhysicalPartition explicitPhysicalLabellings physicalFaceEdges
  refine Q'.eqv_trans _
    (listQSum (parametricKPhysicalTerm w K n)
        (boundedEdgeLabellings K (List.range (plaquetteEdgeCount n))) *
      Q'.recipPos
        (listQSum (parametricKPhysicalTerm w K n)
          (boundedEdgeLabellings K (List.range (plaquetteEdgeCount n))))
        (couplingKPhysicalPartition_pos hw0 K n)) _ ?_ ?_
  · exact
      YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization.listQSum_mul_const
        (parametricKPhysicalTerm w K n)
        (Q'.recipPos
          (listQSum (parametricKPhysicalTerm w K n)
            (boundedEdgeLabellings K (List.range (plaquetteEdgeCount n))))
          (couplingKPhysicalPartition_pos hw0 K n))
        (boundedEdgeLabellings K (List.range (plaquetteEdgeCount n)))
  · exact Q'.mul_recipPos_eqv _
      (couplingKPhysicalPartition_pos hw0 K n)

/-! ## 2. Retune bounds and the mixed kernel -/

theorem retuneCube_le_one {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    retuneCube w ≤ (1 : Q') := by
  have hadd : (1 : Q') + w ≤ (1 : Q') + 1 :=
    Q'.add_le_add_left 1 w 1 hw1
  have hbase0 : (0 : Q') ≤ retuneBase w := by
    unfold retuneBase
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (by decide) hw0)
  have hbase1 : retuneBase w ≤ (1 : Q') := by
    unfold retuneBase
    have hmul := Q'.mul_le_mul_of_nonneg_left _ _
      (Q'.mkPos 1 2 (by decide)) hadd (by decide)
    exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (by decide))
  unfold retuneCube
  exact HeatKernelGap.qpow_le_one hbase0 hbase1 3

theorem retuneCube_pos {w : Q'} (hw0 : (0 : Q') ≤ w) :
    (0 : Q') < retuneCube w := by
  have hsum : (0 : Q') < (1 : Q') + w :=
    Q'.pos_add_nonneg (by decide) hw0
  have hbase : (0 : Q') < retuneBase w := by
    unfold retuneBase
    exact Q'.mul_pos (by decide) hsum
  unfold retuneCube
  exact BondMovingScaledNorm.qpow_pos hbase 3

/-- The globally refreshed branch.  It is a valid physical probability row,
but it ignores the fine source completely. -/
def coarsePhysicalRefreshKernel (w : Q') (hw0 : (0 : Q') ≤ w)
    (n : Nat) (_fine coarse : EdgeLabelling) : Q' :=
  normalizedPhysicalMass w hw0 1 n coarse

/-- Exact machine fence for the nonlocal-refresh limitation: all refresh rows
are literally identical, independent of every fine coordinate. -/
theorem coarsePhysicalRefreshKernel_rows_identical
    (w : Q') (hw0 : (0 : Q') ≤ w) (n : Nat)
    (fineLeft fineRight coarse : EdgeLabelling) :
    coarsePhysicalRefreshKernel w hw0 n fineLeft coarse =
      coarsePhysicalRefreshKernel w hw0 n fineRight coarse := by
  rfl

theorem coarsePhysicalRefreshKernel_row_normalized
    (w : Q') (hw0 : (0 : Q') ≤ w) (n : Nat)
    (fine : EdgeLabelling) :
    listQSum (coarsePhysicalRefreshKernel w hw0 n fine)
        (explicitPhysicalLabellings 1 n) ≈ 1 := by
  exact normalizedPhysicalMass_total w hw0 1 n

/-- A multi-coordinate Markov kernel: retain the exact cellular-parity image
with weight `retuneCube w`, otherwise refresh from the complete normalized
coarse physical law. -/
def retunedParityPhysicalKernel (w : Q') (hw0 : (0 : Q') ≤ w)
    (n : Nat) (fine coarse : EdgeLabelling) : Q' :=
  retuneCube w * dyadicParityGlobalKernel n fine coarse +
    ((1 : Q') - retuneCube w) *
      coarsePhysicalRefreshKernel w hw0 n fine coarse

theorem retunedParityPhysicalKernel_nonnegative
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (n : Nat) (fine coarse : EdgeLabelling) :
    (0 : Q') ≤ retunedParityPhysicalKernel w hw0 n fine coarse := by
  unfold retunedParityPhysicalKernel
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (retuneCube_nonnegative hw0)
      (dyadicParityGlobalKernel_nonnegative n fine coarse))
    (Q'.mul_nonneg _ _
      (Q'.sub_nonneg_of_le (retuneCube_le_one hw0 hw1))
      (normalizedPhysicalMass_nonnegative w hw0 1 n coarse))

theorem retunedParityPhysicalKernel_row_normalized
    (w : Q') (hw0 : (0 : Q') ≤ w)
    (n : Nat) (fine : EdgeLabelling) :
    listQSum (retunedParityPhysicalKernel w hw0 n fine)
        (explicitPhysicalLabellings 1 n) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
        (fun coarse =>
          retuneCube w * dyadicParityGlobalKernel n fine coarse)
        (explicitPhysicalLabellings 1 n) +
      listQSum
        (fun coarse =>
          ((1 : Q') - retuneCube w) *
            coarsePhysicalRefreshKernel w hw0 n fine coarse)
        (explicitPhysicalLabellings 1 n)) _ ?_ ?_
  · exact listQSum_add _ _ _
  · refine Q'.eqv_trans _
      (retuneCube w *
          listQSum (dyadicParityGlobalKernel n fine)
            (explicitPhysicalLabellings 1 n) +
        ((1 : Q') - retuneCube w) *
          listQSum (coarsePhysicalRefreshKernel w hw0 n fine)
            (explicitPhysicalLabellings 1 n)) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (listQSum_mul_left (retuneCube w)
          (dyadicParityGlobalKernel n fine)
          (explicitPhysicalLabellings 1 n))
        (listQSum_mul_left ((1 : Q') - retuneCube w)
          (coarsePhysicalRefreshKernel w hw0 n fine)
          (explicitPhysicalLabellings 1 n))
    · have hD := dyadicParityGlobalKernel_row_normalized n fine
      have hq := coarsePhysicalRefreshKernel_row_normalized w hw0 n fine
      refine Q'.eqv_trans _
        (retuneCube w * 1 + ((1 : Q') - retuneCube w) * 1) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left (retuneCube w) _ _ hD)
          (Q'.mul_eqv_congr_left ((1 : Q') - retuneCube w) _ _ hq)
      · refine Q'.eqv_trans _
          (retuneCube w + ((1 : Q') - retuneCube w)) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.mul_one_eqv (retuneCube w))
            (Q'.mul_one_eqv ((1 : Q') - retuneCube w))
        · exact BernsteinVariance.add_one_sub_eqv_one (retuneCube w)

/-! ## 3. Exact finite pushforward and remainder -/

def parityPushforwardOf (K n : Nat) (mu : EdgeLabelling → Q')
    (coarse : EdgeLabelling) : Q' :=
  listQSum
    (fun fine => mu fine * dyadicParityGlobalKernel n fine coarse)
    (dyadicParityFineStateSpace K n)

def retunedPhysicalPushforwardOf
    (w : Q') (hw0 : (0 : Q') ≤ w) (K n : Nat)
    (mu : EdgeLabelling → Q') (coarse : EdgeLabelling) : Q' :=
  listQSum
    (fun fine => mu fine * retunedParityPhysicalKernel w hw0 n fine coarse)
    (dyadicParityFineStateSpace K n)

theorem retunedPhysicalPushforwardOf_decomposition
    (w : Q') (hw0 : (0 : Q') ≤ w) (K n : Nat)
    (mu : EdgeLabelling → Q') (coarse : EdgeLabelling) :
    retunedPhysicalPushforwardOf w hw0 K n mu coarse ≈
      retuneCube w * parityPushforwardOf K n mu coarse +
        (((1 : Q') - retuneCube w) *
          normalizedPhysicalMass w hw0 1 n coarse) *
        listQSum mu (dyadicParityFineStateSpace K n) := by
  unfold retunedPhysicalPushforwardOf retunedParityPhysicalKernel
    coarsePhysicalRefreshKernel parityPushforwardOf
  let sources := dyadicParityFineStateSpace K n
  let q := normalizedPhysicalMass w hw0 1 n coarse
  let r := retuneCube w
  let s := (1 : Q') - r
  have hpoint :
      listQSum
          (fun fine =>
            mu fine *
              (r * dyadicParityGlobalKernel n fine coarse + s * q))
          sources ≈
        listQSum
          (fun fine =>
            r * (mu fine * dyadicParityGlobalKernel n fine coarse) +
              (s * q) * mu fine)
          sources := by
    apply listQSum_congr_on
    intro fine hfine
    ac_qeqv
  refine Q'.eqv_trans _ _ _ hpoint ?_
  refine Q'.eqv_trans _
    (listQSum
        (fun fine => r * (mu fine * dyadicParityGlobalKernel n fine coarse))
        sources +
      listQSum (fun fine => (s * q) * mu fine) sources) _
    (listQSum_add _ _ sources) ?_
  exact Q'.add_eqv_congr'
    (listQSum_mul_left r
      (fun fine => mu fine * dyadicParityGlobalKernel n fine coarse) sources)
    (listQSum_mul_left (s * q) mu sources)

theorem retunedPhysicalPushforwardOf_normalized
    (w : Q') (hw0 : (0 : Q') ≤ w) (K n : Nat)
    (mu : EdgeLabelling → Q')
    (hmu : listQSum mu (dyadicParityFineStateSpace K n) ≈ 1)
    (coarse : EdgeLabelling) :
    retunedPhysicalPushforwardOf w hw0 K n mu coarse ≈
      retuneCube w * parityPushforwardOf K n mu coarse +
        ((1 : Q') - retuneCube w) *
          normalizedPhysicalMass w hw0 1 n coarse := by
  refine Q'.eqv_trans _ _ _
    (retunedPhysicalPushforwardOf_decomposition w hw0 K n mu coarse) ?_
  have htotal := Q'.mul_eqv_congr_left
    (((1 : Q') - retuneCube w) *
      normalizedPhysicalMass w hw0 1 n coarse) _ _ hmu
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) htotal) ?_
  exact Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.mul_one_eqv
      (((1 : Q') - retuneCube w) *
        normalizedPhysicalMass w hw0 1 n coarse))

theorem retunedPhysicalPushforwardOf_remainder_exact
    (w : Q') (hw0 : (0 : Q') ≤ w) (K n : Nat)
    (mu : EdgeLabelling → Q')
    (hmu : listQSum mu (dyadicParityFineStateSpace K n) ≈ 1)
    (coarse : EdgeLabelling) :
    retunedPhysicalPushforwardOf w hw0 K n mu coarse +
        -normalizedPhysicalMass w hw0 1 n coarse ≈
      retuneCube w *
        (parityPushforwardOf K n mu coarse +
          -normalizedPhysicalMass w hw0 1 n coarse) := by
  have hpush := retunedPhysicalPushforwardOf_normalized
    w hw0 K n mu hmu coarse
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hpush (Q'.eqv_refl _)) ?_
  let r := retuneCube w
  let D := parityPushforwardOf K n mu coarse
  let q := normalizedPhysicalMass w hw0 1 n coarse
  have hcomplement : (((1 : Q') - r) * q) ≈ q + -(r * q) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-r) q) ?_
    exact Q'.add_eqv_congr'
      (Q'.one_mul_eqv q)
      (Q'.neg_mul_eqv r q)
  have hrewrite :
      (r * D + ((1 : Q') - r) * q) + -q ≈
        (r * D + (q + -(r * q))) + -q := by
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hcomplement)
      (Q'.eqv_refl _)
  have hreorder :
      (r * D + (q + -(r * q))) + -q ≈
        q + ((r * D + -(r * q)) + -q) := by
    ac_qeqv
  have hcancel :
      q + ((r * D + -(r * q)) + -q) ≈
        r * D + -(r * q) :=
    Q'.eqv_symm (Q'.add_sub_cancel_eqv (r * D + -(r * q)) q)
  have hfactor :
      r * (D + -q) ≈ r * D + -(r * q) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv r D (-q)) ?_
    exact Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_neg_eqv r q)
  exact Q'.eqv_trans _ _ _ hrewrite
    (Q'.eqv_trans _ _ _ hreorder
      (Q'.eqv_trans _ _ _ hcancel (Q'.eqv_symm hfactor)))

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ xs : List A,
    (∀ x, x ∈ xs → lower x ≤ upper x) →
      listQSum lower xs ≤ listQSum upper xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, h =>
      Q'.add_le_add (h head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun x hx => h x (List.mem_cons_of_mem head hx)))

def finiteL1Remainder (targets : List EdgeLabelling)
    (left right : EdgeLabelling → Q') : Q' :=
  listQSum (fun coarse => Q'.abs (left coarse + -right coarse)) targets

/-- The exact pointwise remainder yields a fully explicit scaled L1 bound.
No measured constant enters: the factor is exactly `retuneCube w`. -/
theorem retunedPhysicalPushforwardOf_l1_scaled
    (w : Q') (hw0 : (0 : Q') ≤ w) (K n : Nat)
    (mu : EdgeLabelling → Q')
    (hmu : listQSum mu (dyadicParityFineStateSpace K n) ≈ 1) :
    finiteL1Remainder (explicitPhysicalLabellings 1 n)
        (retunedPhysicalPushforwardOf w hw0 K n mu)
        (normalizedPhysicalMass w hw0 1 n) ≤
      retuneCube w *
        finiteL1Remainder (explicitPhysicalLabellings 1 n)
          (parityPushforwardOf K n mu)
          (normalizedPhysicalMass w hw0 1 n) := by
  unfold finiteL1Remainder
  have hterms : ∀ coarse,
      coarse ∈ explicitPhysicalLabellings 1 n →
      Q'.abs
          (retunedPhysicalPushforwardOf w hw0 K n mu coarse +
            -normalizedPhysicalMass w hw0 1 n coarse) ≤
        retuneCube w *
          Q'.abs
            (parityPushforwardOf K n mu coarse +
              -normalizedPhysicalMass w hw0 1 n coarse) := by
    intro coarse hcoarse
    have hrem := retunedPhysicalPushforwardOf_remainder_exact
      w hw0 K n mu hmu coarse
    have habs := Q'.abs_eqv_congr hrem
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv habs) ?_
    refine Q'.le_trans' _ _ _
      (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
        (retuneCube w)
        (parityPushforwardOf K n mu coarse +
          -normalizedPhysicalMass w hw0 1 n coarse)) ?_
    have hrabs := YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
      (retuneCube_nonnegative hw0)
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.le_of_eqv hrabs)
      (Q'.abs_nonneg _)
  have hsum := listQSum_mono_local _ _
    (explicitPhysicalLabellings 1 n) hterms
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (listQSum_mul_left (retuneCube w)
        (fun coarse =>
          Q'.abs
            (parityPushforwardOf K n mu coarse +
              -normalizedPhysicalMass w hw0 1 n coarse))
        (explicitPhysicalLabellings 1 n)))

/-! ## 4. The normalized physical source and an inhabited source witness -/

def normalizedFinePhysicalMass
    (w : Q') (hw0 : (0 : Q') ≤ w) (K n : Nat) :
    EdgeLabelling → Q' :=
  normalizedPhysicalMass w hw0 K (2 * n)

theorem normalizedFinePhysicalMass_total
    (w : Q') (hw0 : (0 : Q') ≤ w) (K n : Nat) :
    listQSum (normalizedFinePhysicalMass w hw0 K n)
        (dyadicParityFineStateSpace K n) ≈ 1 := by
  exact normalizedPhysicalMass_total w hw0 K (2 * n)

theorem normalizedFinePhysical_l1_scaled
    (w : Q') (hw0 : (0 : Q') ≤ w) (K n : Nat) :
    finiteL1Remainder (explicitPhysicalLabellings 1 n)
        (retunedPhysicalPushforwardOf w hw0 K n
          (normalizedFinePhysicalMass w hw0 K n))
        (normalizedPhysicalMass w hw0 1 n) ≤
      retuneCube w *
        finiteL1Remainder (explicitPhysicalLabellings 1 n)
          (parityPushforwardOf K n
            (normalizedFinePhysicalMass w hw0 K n))
          (normalizedPhysicalMass w hw0 1 n) := by
  exact retunedPhysicalPushforwardOf_l1_scaled w hw0 K n _
    (normalizedFinePhysicalMass_total w hw0 K n)

theorem dyadicParityGlobalKernel_zero_to_coarseCube :
    dyadicParityGlobalKernel 2 zeroEdgeLabelling
        (componentLabel coarseUnitCubeSupportIds) = 0 := by
  unfold dyadicParityGlobalKernel deterministicKernel
  rw [excitedPlaquetteIds_componentLabel_eq_support
    coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports]
  rw [dyadicParityTargetSupportIds_zeroEdgeLabelling]
  have hne : coarseUnitCubeSupportIds ≠ [] := by
    intro h
    have hlen : ([] : List Nat).length = 6 := by
      simpa [h] using coarseUnitCubeSupportIds_length
    exact (by decide : ([] : List Nat).length ≠ 6) hlen
  rw [if_neg hne]

/-- An inhabited, bounded witness that the complete mixed kernel is genuinely
source dependent.  The zero source and the literal 24-face refined cube are
both cutoff-one fine states; at the coarse cube target their rows differ by
the strictly positive amount `retuneCube w`. -/
theorem retunedParityPhysicalKernel_source_witness
    (w : Q') (hw0 : (0 : Q') ≤ w) :
    zeroEdgeLabelling ∈ dyadicParityFineStateSpace 1 2 ∧
      componentLabel dyadicUnitCubeSupportIds ∈
        dyadicParityFineStateSpace 1 2 ∧
      retunedParityPhysicalKernel w hw0 2 zeroEdgeLabelling
          (componentLabel coarseUnitCubeSupportIds) + retuneCube w ≈
        retunedParityPhysicalKernel w hw0 2
          (componentLabel dyadicUnitCubeSupportIds)
          (componentLabel coarseUnitCubeSupportIds) ∧
      (0 : Q') < retuneCube w := by
  constructor
  · unfold dyadicParityFineStateSpace explicitPhysicalLabellings
      physicalFaceEdges
    exact zeroEdgeLabelling_mem_bounded 1 (2 * 2)
  · constructor
    · exact refinedUnitCubeLabel_mem_fineStateSpace
    · constructor
      · unfold retunedParityPhysicalKernel
        rw [dyadicParityGlobalKernel_zero_to_coarseCube]
        rw [dyadicParityGlobalKernel_refinedUnitCube_to_coarseCube]
        unfold coarsePhysicalRefreshKernel
        let r := retuneCube w
        let s := (1 : Q') - r
        let q := normalizedPhysicalMass w hw0 1 2
          (componentLabel coarseUnitCubeSupportIds)
        have hleft : (r * 0 + s * q) + r ≈ r + s * q := by
          refine Q'.eqv_trans _
            ((0 : Q') + s * q + r) _ ?_ ?_
          · exact Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.mul_zero_eqv r) (Q'.eqv_refl _))
              (Q'.eqv_refl _)
          · rw [Q'.zero_add']
            exact Q'.add_comm_eqv (s * q) r
        have hright : r + s * q ≈ r * 1 + s * q := by
          exact Q'.add_eqv_congr'
            (Q'.eqv_symm (Q'.mul_one_eqv r)) (Q'.eqv_refl _)
        exact Q'.eqv_trans _ _ _ hleft hright
      · exact retuneCube_pos hw0

/-! ## 5. Existing gauge/closure interface and RP fence -/

/-- The deterministic branch carries the already checked F2 cellular closure
theorem.  This is the precise gauge-closure content available here; it is not
an assertion that the source-independent refresh has been localized. -/
theorem deterministicParityBranch_closed_of_nonzero_weight
    {K n : Nat} {finePhysical : EdgeLabelling}
    (hnonzero :
      ¬ explicitSpinFoamWeight K (2 * n) finePhysical ≈ 0) :
    YMGap.Continuum.Z4DyadicDeterministicSupportKernel.EvenFaceIncidence
      (coarseOddSpinSupport n finePhysical) :=
  coarseOddSpinSupport_evenFaceIncidence_of_nonzero_weight hnonzero

/-- Exact RP fence for this old-box presentation.  A facewise reflection
intertwiner for the same target enumeration is impossible at nonzero volume;
the corrected boundary-complete slab remains the open physical interface. -/
theorem oldBox_facewise_RP_interface_impossible
    {n : Nat} (hn : 0 < n) :
    YMGap.Continuum.Z4OldBoxReflectionKernelFence.OldBoxFacewiseReflectionKernel
        1 n → False :=
  YMGap.Continuum.Z4OldBoxReflectionKernelFence.no_cutoffOne_oldBoxFacewiseReflectionKernel
    hn

#print axioms normalizedPhysicalMass_total
#print axioms retuneCube_le_one
#print axioms retunedParityPhysicalKernel_nonnegative
#print axioms retunedParityPhysicalKernel_row_normalized
#print axioms retunedPhysicalPushforwardOf_decomposition
#print axioms retunedPhysicalPushforwardOf_remainder_exact
#print axioms retunedPhysicalPushforwardOf_l1_scaled
#print axioms normalizedFinePhysical_l1_scaled
#print axioms retunedParityPhysicalKernel_source_witness
#print axioms deterministicParityBranch_closed_of_nonzero_weight
#print axioms oldBox_facewise_RP_interface_impossible

end YMGap.Continuum.Z4RetunedParityPhysicalMixtureKernel
