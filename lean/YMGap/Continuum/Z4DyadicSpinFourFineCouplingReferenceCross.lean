/-
# Coupling-one reference cross and localized Casimir perturbation

The cancellation-preserving receiver reduction consumes a signed difference
of two four-cell masses, not the full pushed target law.  This module lifts the
one-column coupling perturbation estimate to exactly that signed cross.

The coupling-one reference pair mass is the product of the two literal
coupling-one pushed columns.  Its perturbation is charged to a pair-local
Casimir moment, and summing only over the source and opposite target cells
gives

  |referenceCross - actualPushedCross|
    <= (1 - fineCoupling) * localizedFourCellCasimirMoment.

On the matched AF window the scalar factor is at most `2*g^2`.  A final
corollary identifies the actual cross with the assignment-saturated receiver
raw-column cross already used by the finite covariance bridge.

This is a finite constructive reduction.  It does not prove that the
coupling-one reference cross vanishes, that the localized moment is uniform in
the volume, all-cutoff persistence, a continuum measure, OS/GNS
reconstruction, a Hamiltonian gap, or the Yang--Mills mass gap.

Constructive contract: finite list induction, exact rational algebra,
positivity, and the preceding Bernoulli estimate only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceCross

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation
open YMGap.Continuum.Z4DyadicSpinFourReceiverRawColumnCrossCalibration

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem cross_sub_cross_eqv_loss_difference
    (referenceSource referenceTarget actualSource actualTarget : Q') :
    (referenceSource - referenceTarget) -
        (actualSource - actualTarget) ≈
      (referenceSource - actualSource) -
        (referenceTarget - actualTarget) := by
  change
    ((referenceSource + -referenceTarget) +
        -(actualSource + -actualTarget)) ≈
      (referenceSource + -actualSource) +
        -(referenceTarget + -actualTarget)
  ring_qeqv

private theorem listQSum_neg_local {A : Type}
    (value : A → Q') : ∀ items : List A,
    listQSum (fun item => -(value item)) items ≈
      -(listQSum value items)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_refl _) (listQSum_neg_local value tail)
      · exact Q'.eqv_symm
          (Q'.neg_add_eqv (value head) (listQSum value tail))

private theorem listQSum_sub_local {A : Type}
    (left right : A → Q') (items : List A) :
    listQSum left items - listQSum right items ≈
      listQSum (fun item => left item - right item) items := by
  exact Q'.eqv_symm
    (Q'.eqv_trans _
      (listQSum left items +
        listQSum (fun item => -(right item)) items) _
      (listQSum_add left (fun item => -(right item)) items)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (listQSum_neg_local right items)))

private theorem listQSum_mono_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local left right tail
          (fun item hitem => hle item
            (List.mem_cons_of_mem head hitem)))

private theorem abs_sub_nonnegative_le_add
    {left right : Q'}
    (left_nonnegative : (0 : Q') ≤ left)
    (right_nonnegative : (0 : Q') ≤ right) :
    Q'.abs (left - right) ≤ left + right := by
  apply Q'.abs_le
  · have neg_left_le_left : -left ≤ left :=
      Q'.le_trans' _ _ _
        (Q'.nonpos_neg_of_nonneg left_nonnegative)
        left_nonnegative
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_add_eqv left right))
      (Q'.add_le_add_right (-left) left (-right)
        neg_left_le_left)
  · have neg_right_le_right : -right ≤ right :=
      Q'.le_trans' _ _ _
        (Q'.nonpos_neg_of_nonneg right_nonnegative)
        right_nonnegative
    exact Q'.add_le_add_left left (-right) right
      neg_right_le_right

/-! ## 1. Monotonicity of the pushed coupling-one columns -/

/-- Below coupling one, every bounded fine physical summand is at most its
coupling-one reference value. -/
theorem slabParametricKPhysicalTerm_le_atOne
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1)
    (K extent : Nat) (physical : EdgeLabelling)
    (hphysical : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent)) :
    slabParametricKPhysicalTerm w K extent physical ≤
      slabParametricKPhysicalTerm 1 K extent physical := by
  let exponent := slabPhysicalCasimirExponent extent physical
  let reference := slabParametricKPhysicalTerm 1 K extent physical
  have hfactor :
      slabParametricKPhysicalTerm w K extent physical ≈
        qpow w exponent * reference := by
    simpa only [exponent, reference] using
      (slabParametricKPhysicalTerm_eqv_power_mul_atOne
        w K extent physical hphysical)
  have hpow := YMGap.Continuum.HeatKernelGap.qpow_le_one
    hw0 hw1 exponent
  have href0 : (0 : Q') ≤ reference :=
    slabParametricKPhysicalTerm_nonnegative
      (by decide : (0 : Q') ≤ (1 : Q')) K extent physical
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hfactor)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ reference hpow href0)
      (Q'.le_of_eqv (Q'.one_mul_eqv reference)))

/-- Actual mass in every literal pushed receiver column is nonnegative. -/
theorem pushedPhysicalTargetRawMass_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    {target : EdgeLabelling}
    (htarget : target ∈ S.coarse.physicalLabellings) :
    (0 : Q') ≤ pushedPhysicalTargetRawMass K target := by
  unfold pushedPhysicalTargetRawMass
  apply listQSum_nonnegative_on
  intro source hsource
  exact Q'.mul_nonneg _ _
    (slabParametricKPhysicalTerm_nonnegative
      S.fine.coupling_nonnegative S.fine.cutoff
      S.fine.extent source)
    (K.nonnegative source target hsource htarget)

/-- The pushed coupling-one reference column is nonnegative. -/
theorem fineUnitCouplingPushedTargetRawMass_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    {target : EdgeLabelling}
    (htarget : target ∈ S.coarse.physicalLabellings) :
    (0 : Q') ≤ fineUnitCouplingPushedTargetRawMass K target := by
  unfold fineUnitCouplingPushedTargetRawMass
  apply listQSum_nonnegative_on
  intro source hsource
  exact Q'.mul_nonneg _ _
    (slabParametricKPhysicalTerm_nonnegative
      (by decide : (0 : Q') ≤ (1 : Q')) S.fine.cutoff
      S.fine.extent source)
    (K.nonnegative source target hsource htarget)

/-- The actual pushed column is pointwise dominated by its coupling-one
reference on `0 <= fineCoupling <= 1`. -/
theorem pushedPhysicalTargetRawMass_le_fineUnitCoupling
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    {target : EdgeLabelling}
    (htarget : target ∈ S.coarse.physicalLabellings) :
    pushedPhysicalTargetRawMass K target ≤
      fineUnitCouplingPushedTargetRawMass K target := by
  unfold pushedPhysicalTargetRawMass
    fineUnitCouplingPushedTargetRawMass
  apply listQSum_mono_local
  intro source hsource
  exact Q'.mul_le_mul_of_nonneg_right _ _ (K.kernel source target)
    (slabParametricKPhysicalTerm_le_atOne
      S.fine.coupling_nonnegative hfineCoupling_le_one
      S.fine.cutoff S.fine.extent source
      (by simpa only [SlabPhysicalData.physicalLabellings,
          SlabPhysicalData.faceEdges] using hsource))
    (K.nonnegative source target hsource htarget)

/-! ## 2. Pair-local reference masses and moments -/

/-- Product reference mass of a literal coarse target pair at fine coupling
one. -/
def fineUnitCouplingPushedTargetPairRawMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  fineUnitCouplingPushedTargetRawMass K pair.1 *
    fineUnitCouplingPushedTargetRawMass K pair.2

/-- Product-rule Casimir moment controlling the perturbation of one target
pair. -/
def fineUnitCouplingPushedTargetPairCasimirMoment
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  fineUnitCouplingPushedTargetRawMass K pair.1 *
      fineUnitCouplingPushedTargetCasimirMoment K pair.2 +
    fineUnitCouplingPushedTargetRawMass K pair.2 *
      fineUnitCouplingPushedTargetCasimirMoment K pair.1

theorem fineUnitCouplingPushedTargetPairCasimirMoment_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    {pair : EdgeLabelling × EdgeLabelling}
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    (0 : Q') ≤
      fineUnitCouplingPushedTargetPairCasimirMoment K pair := by
  unfold fineUnitCouplingPushedTargetPairCasimirMoment
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _
      (fineUnitCouplingPushedTargetRawMass_nonnegative K hleft)
      (fineUnitCouplingPushedTargetCasimirMoment_nonnegative K hright))
    (Q'.mul_nonneg _ _
      (fineUnitCouplingPushedTargetRawMass_nonnegative K hright)
      (fineUnitCouplingPushedTargetCasimirMoment_nonnegative K hleft))

private theorem pushedPhysicalTargetPairRawMass_le_fineUnitCoupling
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    {pair : EdgeLabelling × EdgeLabelling}
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    pushedPhysicalTargetPairRawMass K pair ≤
      fineUnitCouplingPushedTargetPairRawMass K pair := by
  unfold pushedPhysicalTargetPairRawMass
    fineUnitCouplingPushedTargetPairRawMass
  have hleftLe := pushedPhysicalTargetRawMass_le_fineUnitCoupling
    K hfineCoupling_le_one hleft
  have hrightLe := pushedPhysicalTargetRawMass_le_fineUnitCoupling
    K hfineCoupling_le_one hright
  have hactualRight0 := pushedPhysicalTargetRawMass_nonnegative K hright
  have hrefLeft0 :=
    fineUnitCouplingPushedTargetRawMass_nonnegative K hleft
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hleftLe hactualRight0)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hrightLe hrefLeft0)

/-- The loss in one pushed target-pair product is controlled by the scalar
coupling margin times its product-rule Casimir moment. -/
theorem fineUnitCouplingPushedTargetPairRawMass_sub_actual_le_margin_mul_moment
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    {pair : EdgeLabelling × EdgeLabelling}
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    fineUnitCouplingPushedTargetPairRawMass K pair -
        pushedPhysicalTargetPairRawMass K pair ≤
      (1 + -S.fine.coupling) *
        fineUnitCouplingPushedTargetPairCasimirMoment K pair := by
  let refLeft := fineUnitCouplingPushedTargetRawMass K pair.1
  let refRight := fineUnitCouplingPushedTargetRawMass K pair.2
  let actualLeft := pushedPhysicalTargetRawMass K pair.1
  let actualRight := pushedPhysicalTargetRawMass K pair.2
  let momentLeft := fineUnitCouplingPushedTargetCasimirMoment K pair.1
  let momentRight := fineUnitCouplingPushedTargetCasimirMoment K pair.2
  let margin := 1 + -S.fine.coupling
  have hrefLeft0 : (0 : Q') ≤ refLeft :=
    fineUnitCouplingPushedTargetRawMass_nonnegative K hleft
  have hrefRight0 : (0 : Q') ≤ refRight :=
    fineUnitCouplingPushedTargetRawMass_nonnegative K hright
  have hactualRight0 : (0 : Q') ≤ actualRight :=
    pushedPhysicalTargetRawMass_nonnegative K hright
  have hactualRightLe : actualRight ≤ refRight :=
    pushedPhysicalTargetRawMass_le_fineUnitCoupling
      K hfineCoupling_le_one hright
  have hmomentLeft0 : (0 : Q') ≤ momentLeft :=
    fineUnitCouplingPushedTargetCasimirMoment_nonnegative K hleft
  have hmomentRight0 : (0 : Q') ≤ momentRight :=
    fineUnitCouplingPushedTargetCasimirMoment_nonnegative K hright
  have hmargin0 : (0 : Q') ≤ margin :=
    Q'.sub_nonneg_of_le hfineCoupling_le_one
  have hrightLoss : refRight - actualRight ≤ margin * momentRight := by
    simpa only [refRight, actualRight, margin, momentRight] using
      (fineUnitCouplingPushedTargetRawMass_sub_actual_le_margin_mul_moment
        K hfineCoupling_le_one hright)
  have hleftLoss : refLeft - actualLeft ≤ margin * momentLeft := by
    simpa only [refLeft, actualLeft, margin, momentLeft] using
      (fineUnitCouplingPushedTargetRawMass_sub_actual_le_margin_mul_moment
        K hfineCoupling_le_one hleft)
  have hfirst :
      refLeft * (refRight - actualRight) ≤
        refLeft * (margin * momentRight) :=
    Q'.mul_le_mul_of_nonneg_left _ _ refLeft hrightLoss hrefLeft0
  have hsecondA :
      actualRight * (refLeft - actualLeft) ≤
        actualRight * (margin * momentLeft) :=
    Q'.mul_le_mul_of_nonneg_left _ _ actualRight
      hleftLoss hactualRight0
  have hmarginMomentLeft0 : (0 : Q') ≤ margin * momentLeft :=
    Q'.mul_nonneg _ _ hmargin0 hmomentLeft0
  have hsecondB :
      actualRight * (margin * momentLeft) ≤
        refRight * (margin * momentLeft) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hactualRightLe hmarginMomentLeft0
  have hdecomp :
      refLeft * refRight - actualLeft * actualRight ≈
        refLeft * (refRight - actualRight) +
          actualRight * (refLeft - actualLeft) :=
    CReal.mul_sub_decomp refLeft refRight actualLeft actualRight
  have hsum := Q'.add_le_add hfirst
    (Q'.le_trans' _ _ _ hsecondA hsecondB)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by
      unfold fineUnitCouplingPushedTargetPairRawMass
        pushedPhysicalTargetPairRawMass
      exact hdecomp))
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_))
  unfold fineUnitCouplingPushedTargetPairCasimirMoment
  simp only [refLeft, refRight, margin, momentLeft, momentRight]
  ring_qeqv

/-! ## 3. Localized four-cell reference cross -/

/-- Coupling-one mass on the source (`TT x FF`) pair cell. -/
def fineUnitCouplingPushedFourCellSourceRawMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  listQSum (fineUnitCouplingPushedTargetPairRawMass K)
    (pushedFaceRawFourCellSourcePairs (S := S) root target)

/-- Coupling-one mass on the opposite (`FT x TF`) pair cell. -/
def fineUnitCouplingPushedFourCellTargetRawMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  listQSum (fineUnitCouplingPushedTargetPairRawMass K)
    (pushedFaceRawFourCellTargetPairs (S := S) root target)

/-- Pair-local Casimir moment on the source pair cell. -/
def fineUnitCouplingPushedFourCellSourceCasimirMoment
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  listQSum (fineUnitCouplingPushedTargetPairCasimirMoment K)
    (pushedFaceRawFourCellSourcePairs (S := S) root target)

/-- Pair-local Casimir moment on the opposite target pair cell. -/
def fineUnitCouplingPushedFourCellTargetCasimirMoment
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  listQSum (fineUnitCouplingPushedTargetPairCasimirMoment K)
    (pushedFaceRawFourCellTargetPairs (S := S) root target)

/-- The signed coupling-one reference cross on exactly the two four-cell
pair carriers consumed by the observable. -/
def fineUnitCouplingPushedRawColumnCross
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  fineUnitCouplingPushedFourCellSourceRawMass K root target -
    fineUnitCouplingPushedFourCellTargetRawMass K root target

private theorem sourcePair_components_mem
    {S : SlabScalePair} {root target : Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hpair : pair ∈ pushedFaceRawFourCellSourcePairs
      (S := S) root target) :
    pair.1 ∈ S.coarse.physicalLabellings ∧
      pair.2 ∈ S.coarse.physicalLabellings := by
  unfold pushedFaceRawFourCellSourcePairs at hpair
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  exact ⟨(List.mem_filter.mp hmembers.1).1,
    (List.mem_filter.mp hmembers.2).1⟩

private theorem targetPair_components_mem
    {S : SlabScalePair} {root target : Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hpair : pair ∈ pushedFaceRawFourCellTargetPairs
      (S := S) root target) :
    pair.1 ∈ S.coarse.physicalLabellings ∧
      pair.2 ∈ S.coarse.physicalLabellings := by
  unfold pushedFaceRawFourCellTargetPairs at hpair
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  exact ⟨(List.mem_filter.mp hmembers.1).1,
    (List.mem_filter.mp hmembers.2).1⟩

theorem fineUnitCouplingPushedFourCellSourceCasimirMoment_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    (0 : Q') ≤
      fineUnitCouplingPushedFourCellSourceCasimirMoment K root target := by
  unfold fineUnitCouplingPushedFourCellSourceCasimirMoment
  apply listQSum_nonnegative_on
  intro pair hpair
  have hmembers := sourcePair_components_mem hpair
  exact fineUnitCouplingPushedTargetPairCasimirMoment_nonnegative
    K hmembers.1 hmembers.2

theorem fineUnitCouplingPushedFourCellTargetCasimirMoment_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    (0 : Q') ≤
      fineUnitCouplingPushedFourCellTargetCasimirMoment K root target := by
  unfold fineUnitCouplingPushedFourCellTargetCasimirMoment
  apply listQSum_nonnegative_on
  intro pair hpair
  have hmembers := targetPair_components_mem hpair
  exact fineUnitCouplingPushedTargetPairCasimirMoment_nonnegative
    K hmembers.1 hmembers.2

private theorem pushedFourCellSourceRawMass_le_fineUnitCoupling
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (root target : Nat) :
    listQSum (pushedPhysicalTargetPairRawMass K)
        (pushedFaceRawFourCellSourcePairs (S := S) root target) ≤
      fineUnitCouplingPushedFourCellSourceRawMass K root target := by
  unfold fineUnitCouplingPushedFourCellSourceRawMass
  apply listQSum_mono_local
  intro pair hpair
  have hmembers := sourcePair_components_mem hpair
  exact pushedPhysicalTargetPairRawMass_le_fineUnitCoupling
    K hfineCoupling_le_one hmembers.1 hmembers.2

private theorem pushedFourCellTargetRawMass_le_fineUnitCoupling
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (root target : Nat) :
    listQSum (pushedPhysicalTargetPairRawMass K)
        (pushedFaceRawFourCellTargetPairs (S := S) root target) ≤
      fineUnitCouplingPushedFourCellTargetRawMass K root target := by
  unfold fineUnitCouplingPushedFourCellTargetRawMass
  apply listQSum_mono_local
  intro pair hpair
  have hmembers := targetPair_components_mem hpair
  exact pushedPhysicalTargetPairRawMass_le_fineUnitCoupling
    K hfineCoupling_le_one hmembers.1 hmembers.2

private theorem fineUnitCouplingPushedFourCellSourceRawMass_sub_actual_le
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (root target : Nat) :
    fineUnitCouplingPushedFourCellSourceRawMass K root target -
        listQSum (pushedPhysicalTargetPairRawMass K)
          (pushedFaceRawFourCellSourcePairs (S := S) root target) ≤
      (1 + -S.fine.coupling) *
        fineUnitCouplingPushedFourCellSourceCasimirMoment
          K root target := by
  let pairs := pushedFaceRawFourCellSourcePairs (S := S) root target
  let reference := fineUnitCouplingPushedTargetPairRawMass K
  let actual := pushedPhysicalTargetPairRawMass K
  let moment := fineUnitCouplingPushedTargetPairCasimirMoment K
  have hsum :
      listQSum (fun pair => reference pair - actual pair) pairs ≤
        listQSum
          (fun pair => (1 + -S.fine.coupling) * moment pair)
          pairs := by
    apply listQSum_mono_local
    intro pair hpair
    have hmembers := sourcePair_components_mem
      (S := S) (root := root) (target := target)
      (by simpa only [pairs] using hpair)
    exact fineUnitCouplingPushedTargetPairRawMass_sub_actual_le_margin_mul_moment
      K hfineCoupling_le_one hmembers.1 hmembers.2
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _
      (listQSum (fun pair => reference pair - actual pair) pairs) _ ?_ ?_))
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_))
  · unfold fineUnitCouplingPushedFourCellSourceRawMass
    exact listQSum_sub_local reference actual pairs
  · exact Q'.eqv_refl _
  · refine Q'.eqv_trans _
      ((1 + -S.fine.coupling) * listQSum moment pairs) _
      (listQSum_mul_left (1 + -S.fine.coupling) moment pairs) ?_
    unfold fineUnitCouplingPushedFourCellSourceCasimirMoment
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_refl _)

private theorem fineUnitCouplingPushedFourCellTargetRawMass_sub_actual_le
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (root target : Nat) :
    fineUnitCouplingPushedFourCellTargetRawMass K root target -
        listQSum (pushedPhysicalTargetPairRawMass K)
          (pushedFaceRawFourCellTargetPairs (S := S) root target) ≤
      (1 + -S.fine.coupling) *
        fineUnitCouplingPushedFourCellTargetCasimirMoment
          K root target := by
  let pairs := pushedFaceRawFourCellTargetPairs (S := S) root target
  let reference := fineUnitCouplingPushedTargetPairRawMass K
  let actual := pushedPhysicalTargetPairRawMass K
  let moment := fineUnitCouplingPushedTargetPairCasimirMoment K
  have hsum :
      listQSum (fun pair => reference pair - actual pair) pairs ≤
        listQSum
          (fun pair => (1 + -S.fine.coupling) * moment pair)
          pairs := by
    apply listQSum_mono_local
    intro pair hpair
    have hmembers := targetPair_components_mem
      (S := S) (root := root) (target := target)
      (by simpa only [pairs] using hpair)
    exact fineUnitCouplingPushedTargetPairRawMass_sub_actual_le_margin_mul_moment
      K hfineCoupling_le_one hmembers.1 hmembers.2
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _
      (listQSum (fun pair => reference pair - actual pair) pairs) _ ?_ ?_))
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_))
  · unfold fineUnitCouplingPushedFourCellTargetRawMass
    exact listQSum_sub_local reference actual pairs
  · exact Q'.eqv_refl _
  · refine Q'.eqv_trans _
      ((1 + -S.fine.coupling) * listQSum moment pairs) _
      (listQSum_mul_left (1 + -S.fine.coupling) moment pairs) ?_
    unfold fineUnitCouplingPushedFourCellTargetCasimirMoment
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_refl _)

/-! ## 4. Signed cross perturbation and matched-AF specialization -/

/-- The signed actual pushed cross differs from its coupling-one reference by
only the Casimir moment localized to the two selected pair cells. -/
theorem fineUnitCouplingPushedRawColumnCross_sub_actual_abs_le_margin_mul_moment
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (root target : Nat) :
    Q'.abs
        (fineUnitCouplingPushedRawColumnCross K root target -
          pushedFaceRawFourCellCross K root target) ≤
      (1 + -S.fine.coupling) *
        (fineUnitCouplingPushedFourCellSourceCasimirMoment K root target +
          fineUnitCouplingPushedFourCellTargetCasimirMoment
            K root target) := by
  let actualSource :=
    listQSum (pushedPhysicalTargetPairRawMass K)
      (pushedFaceRawFourCellSourcePairs (S := S) root target)
  let actualTarget :=
    listQSum (pushedPhysicalTargetPairRawMass K)
      (pushedFaceRawFourCellTargetPairs (S := S) root target)
  let sourceLoss :=
    fineUnitCouplingPushedFourCellSourceRawMass K root target -
      actualSource
  let targetLoss :=
    fineUnitCouplingPushedFourCellTargetRawMass K root target -
      actualTarget
  let referenceSource :=
    fineUnitCouplingPushedFourCellSourceRawMass K root target
  let referenceTarget :=
    fineUnitCouplingPushedFourCellTargetRawMass K root target
  have hreference :
      fineUnitCouplingPushedRawColumnCross K root target ≈
        referenceSource - referenceTarget := by
    exact Q'.eqv_refl _
  have hactual :
      pushedFaceRawFourCellCross K root target ≈
        actualSource - actualTarget := by
    simpa only [actualSource, actualTarget] using
      (pushedFaceRawFourCellCross_eqv_pair_mass_difference
        K root target)
  have hdiff :
      fineUnitCouplingPushedRawColumnCross K root target -
          pushedFaceRawFourCellCross K root target ≈
        sourceLoss - targetLoss := by
    refine Q'.eqv_trans _
      ((referenceSource - referenceTarget) -
        (actualSource - actualTarget)) _
      (sub_eqv_both_local hreference hactual) ?_
    exact cross_sub_cross_eqv_loss_difference
      referenceSource referenceTarget actualSource actualTarget
  have hsourceLoss0 : (0 : Q') ≤ sourceLoss :=
    Q'.sub_nonneg_of_le
      (pushedFourCellSourceRawMass_le_fineUnitCoupling
        K hfineCoupling_le_one root target)
  have htargetLoss0 : (0 : Q') ≤ targetLoss :=
    Q'.sub_nonneg_of_le
      (pushedFourCellTargetRawMass_le_fineUnitCoupling
        K hfineCoupling_le_one root target)
  have hsourceLoss :=
    fineUnitCouplingPushedFourCellSourceRawMass_sub_actual_le
      K hfineCoupling_le_one root target
  have htargetLoss :=
    fineUnitCouplingPushedFourCellTargetRawMass_sub_actual_le
      K hfineCoupling_le_one root target
  have hsum := Q'.add_le_add hsourceLoss htargetLoss
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdiff))
    (Q'.le_trans' _ _ _
      (abs_sub_nonnegative_le_add hsourceLoss0 htargetLoss0)
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_)))
  exact Q'.eqv_symm
    (Q'.mul_add_eqv (1 + -S.fine.coupling)
      (fineUnitCouplingPushedFourCellSourceCasimirMoment K root target)
      (fineUnitCouplingPushedFourCellTargetCasimirMoment K root target))

/-- On a matched AF fine coupling the localized signed-cross perturbation has
the explicit quadratic scalar prefactor `2*g^2`. -/
theorem fineUnitCouplingPushedRawColumnCross_sub_actual_abs_le_two_square_mul_moment
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (root target : Nat) :
    Q'.abs
        (fineUnitCouplingPushedRawColumnCross K root target -
          pushedFaceRawFourCellCross K root target) ≤
      (Q'.ofNat 2 * (g * g)) *
        (fineUnitCouplingPushedFourCellSourceCasimirMoment K root target +
          fineUnitCouplingPushedFourCellTargetCasimirMoment
            K root target) := by
  have hbase :=
    fineUnitCouplingPushedRawColumnCross_sub_actual_abs_le_margin_mul_moment
      K hfineCoupling_le_one root target
  have hmargin :
      1 + -S.fine.coupling ≤ Q'.ofNat 2 * (g * g) := by
    rw [hcoupling]
    exact blockedMargin_le_two_square family law g hg hgle
  have hmoment0 :
      (0 : Q') ≤
        fineUnitCouplingPushedFourCellSourceCasimirMoment K root target +
          fineUnitCouplingPushedFourCellTargetCasimirMoment K root target :=
    Q'.zero_le_add _ _
      (fineUnitCouplingPushedFourCellSourceCasimirMoment_nonnegative
        K root target)
      (fineUnitCouplingPushedFourCellTargetCasimirMoment_nonnegative
        K root target)
  exact Q'.le_trans' _ _ _ hbase
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hmargin hmoment0)

/-- The same matched-AF estimate, stated directly at the
assignment-saturated receiver raw-column cross used by the current finite
covariance seam. -/
theorem fineUnitCouplingPhysicalRawColumnCross_sub_receiver_abs_le_two_square_mul_moment
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (root target : Nat) :
    Q'.abs
        (fineUnitCouplingPushedRawColumnCross
            (physicalKernel S hfineCutoff hcoarseCoupling) root target -
          positiveExpandedAssignmentSaturatedReceiverRawColumnCross
            S hfineCutoff hcoarseCoupling root target) ≤
      (Q'.ofNat 2 * (g * g)) *
        (fineUnitCouplingPushedFourCellSourceCasimirMoment
            (physicalKernel S hfineCutoff hcoarseCoupling) root target +
          fineUnitCouplingPushedFourCellTargetCasimirMoment
            (physicalKernel S hfineCutoff hcoarseCoupling)
            root target) := by
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  have hreceiver :
      positiveExpandedAssignmentSaturatedReceiverRawColumnCross
          S hfineCutoff hcoarseCoupling root target ≈
        pushedFaceRawFourCellCross K root target :=
    Q'.eqv_trans _ _ _
      (positiveExpandedAssignmentSaturatedReceiverRawColumnCross_eqv_actualPushed
        S hfineCutoff hcoarseCoupling root target)
      (Q'.eqv_symm
        (pushedFaceRawFourCellCross_physicalKernel_eqv_actualRaw
          S hfineCutoff hcoarseCoupling root target))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (sub_eqv_both_local (Q'.eqv_refl _) hreceiver))) ?_
  simpa only [K] using
    (fineUnitCouplingPushedRawColumnCross_sub_actual_abs_le_two_square_mul_moment
      K hfineCoupling_le_one family law g hg hgle hcoupling root target)

#print axioms slabParametricKPhysicalTerm_le_atOne
#print axioms pushedPhysicalTargetRawMass_nonnegative
#print axioms fineUnitCouplingPushedTargetRawMass_nonnegative
#print axioms pushedPhysicalTargetRawMass_le_fineUnitCoupling
#print axioms fineUnitCouplingPushedTargetPairCasimirMoment_nonnegative
#print axioms fineUnitCouplingPushedTargetPairRawMass_sub_actual_le_margin_mul_moment
#print axioms fineUnitCouplingPushedFourCellSourceCasimirMoment_nonnegative
#print axioms fineUnitCouplingPushedFourCellTargetCasimirMoment_nonnegative
#print axioms fineUnitCouplingPushedRawColumnCross_sub_actual_abs_le_margin_mul_moment
#print axioms fineUnitCouplingPushedRawColumnCross_sub_actual_abs_le_two_square_mul_moment
#print axioms fineUnitCouplingPhysicalRawColumnCross_sub_receiver_abs_le_two_square_mul_moment

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceCross
