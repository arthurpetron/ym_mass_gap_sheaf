/-
# Vacuum-sector row distance gives the cofinal BF4 limit gap

The full positive BF4 carrier is reducible, so a strict centered contraction
must be stated on the canonical communicating component containing the
vacuum.  This module supplies that corrected analytic seam.

At one cutoff, compare the physical reflected joint only on the canonical
vacuum-sector index list with the rank-one product of the restricted physical
weights.  Exact sector centering annihilates the product quadratic, and the
weighted Young estimate gives a strict form bound.  A constructively cofinal
family of such sector-local row bounds then feeds the existing moving
same-object cutoff-limit theorem directly, without asserting a false gap on
the other superselection sectors.

No inhabitant of the cofinal certificate is asserted.  No thermodynamic or
continuum limit is constructed here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
import YMGap.Continuum.BF4WeightedJointPerronPerturbation

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCofinalRowGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero,
               Int.zero_add];
             try ac_rfl))

/-! ## 1. Arbitrary finite-carrier stationary-product comparison -/

/-- The stationary rank-one reference on an arbitrary finite index list.
The restricted weights need not sum to one: exact centering is enough to
annihilate its quadratic. -/
def finiteCarrierStationaryProductJoint
    (weight : Nat → Q') (left right : Nat) : Q' :=
  weight left * weight right

/-- On any finite list, the stationary-product quadratic is the square of
the exact restricted weighted mean. -/
theorem finiteCarrierStationaryProductJoint_quadratic_eqv_mean_square
    (states : List Nat) (weight coefficient : Nat → Q') :
    finiteJointQuadratic states coefficient
        (finiteCarrierStationaryProductJoint weight) ≈
      listQSum (fun state => coefficient state * weight state) states *
        listQSum (fun state => coefficient state * weight state) states := by
  let value : Nat → Q' := fun state => coefficient state * weight state
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum (fun right => value left * value right) states)
      states) _ ?_ ?_
  · unfold finiteJointQuadratic finiteCarrierStationaryProductJoint value
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    q_ring
  · exact listQSum_product value value states states

/-- Exact restricted weighted centering kills the stationary-product
quadratic, regardless of the total mass of the selected component. -/
theorem finiteCarrierStationaryProductJoint_quadratic_centered_eqv_zero
    {states : List Nat} {weight coefficient : Nat → Q'}
    (hcenter :
      listQSum (fun state => coefficient state * weight state) states ≈ 0) :
    finiteJointQuadratic states coefficient
        (finiteCarrierStationaryProductJoint weight) ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum (fun state => coefficient state * weight state) states *
      listQSum (fun state => coefficient state * weight state) states) _
    (finiteCarrierStationaryProductJoint_quadratic_eqv_mean_square
      states weight coefficient) ?_
  exact Q'.eqv_trans _
    (0 * listQSum
      (fun state => coefficient state * weight state) states) _
    (Q'.mul_eqv_congr_right _ _ _ hcenter)
    (Q'.zero_mul_eqv _)

/-- A symmetric joint is rowwise close to the stationary product on one
arbitrary finite carrier. -/
structure FiniteCarrierStationaryProductRowDistanceCertificate
    (states : List Nat) (rate : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q') : Type 1 where
  kernelSymmetric : ∀ left right,
    left ∈ states → right ∈ states →
      kernel left right ≈ kernel right left
  rowDistance : ∀ source, source ∈ states →
    finiteJointDifferenceAbsRowMass
        states kernel (finiteCarrierStationaryProductJoint weight) source ≤
      rate * weight source

namespace FiniteCarrierStationaryProductRowDistanceCertificate

/-- Sector-local row distance proves the absolute centered quadratic bound
on exactly that sector. -/
theorem absContraction
    {states : List Nat} {rate : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    (certificate :
      FiniteCarrierStationaryProductRowDistanceCertificate
        states rate weight kernel)
    (coefficient : Nat → Q')
    (hcenter :
      listQSum (fun state => coefficient state * weight state) states ≈ 0) :
    Q'.abs (finiteJointQuadratic states coefficient kernel) ≤
      rate * finiteWeightedSquare states weight coefficient := by
  have hproductSymmetric : ∀ left right,
      left ∈ states → right ∈ states →
        finiteCarrierStationaryProductJoint weight left right ≈
          finiteCarrierStationaryProductJoint weight right left := by
    intro left right _ _
    unfold finiteCarrierStationaryProductJoint
    exact Q'.mul_comm_eqv _ _
  have hperturb := finiteJointQuadratic_abs_sub_le_weightedSquare
    states coefficient weight kernel
    (finiteCarrierStationaryProductJoint weight) rate
    certificate.kernelSymmetric hproductSymmetric certificate.rowDistance
  have hproduct :=
    finiteCarrierStationaryProductJoint_quadratic_centered_eqv_zero hcenter
  have hdiff :
      finiteJointQuadratic states coefficient kernel +
          (-finiteJointQuadratic states coefficient
            (finiteCarrierStationaryProductJoint weight)) ≈
        finiteJointQuadratic states coefficient kernel := by
    refine Q'.eqv_trans _
      (finiteJointQuadratic states coefficient kernel + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ (-0) _
          (Q'.neg_eqv_congr _ _ hproduct) (by decide))
    · exact Q'.eqv_of_eq (Q'.add_zero' _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm hdiff))) hperturb

end FiniteCarrierStationaryProductRowDistanceCertificate

/-! ## 2. Physical vacuum-sector specialization -/

/-- The generic weighted square on the canonical component is exactly the
repository's sector diagonal quadratic. -/
theorem finiteWeightedSquare_vacuumSector_eqv_diagonal
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    finiteWeightedSquare
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteWeight w hw cutoff half) coefficient ≈
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
  unfold finiteWeightedSquare
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic
  apply listQSum_congr
  intro index
  exact Q'.mul_comm_eqv _ _

/-- One strict rate and one constructively cofinal sector-local row-distance
certificate for every requested base cutoff and Cauchy threshold. -/
structure FixedNomeCofinalVacuumSectorRowDistance
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  rowDistance : ∀ base threshold source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w hw (anchor base threshold) half →
      finiteJointDifferenceAbsRowMass
          (centralPhysicalFiniteVacuumSectorIndices
            w hw (anchor base threshold) half)
          (centralPhysicalFiniteKernel
            w hw (anchor base threshold) half)
          (finiteCarrierStationaryProductJoint
            (centralPhysicalFiniteWeight
              w hw (anchor base threshold) half))
          source ≤
        rate * centralPhysicalFiniteWeight
          w hw (anchor base threshold) half source

namespace FixedNomeCofinalVacuumSectorRowDistance

/-- Package the physical row estimate at one selected cutoff as the generic
finite-carrier certificate.  Kernel symmetry uses only that both indices lie
in the genuine positive physical carrier. -/
def finiteCertificate
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorRowDistance w hw half rate)
    (base threshold : Nat) :
    FiniteCarrierStationaryProductRowDistanceCertificate
      (centralPhysicalFiniteVacuumSectorIndices
        w hw (family.anchor base threshold) half)
      rate
      (centralPhysicalFiniteWeight
        w hw (family.anchor base threshold) half)
      (centralPhysicalFiniteKernel
        w hw (family.anchor base threshold) half) where
  kernelSymmetric := by
    intro left right hleft hright
    unfold centralPhysicalFiniteKernel
    exact centralNormalizedPhysicalReflectedKernel_symm
      ((mem_centralPositiveHalfStates_iff).1
        (centralPhysicalFiniteStateAt_mem_positive
          w hw (family.anchor base threshold) half
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w hw (family.anchor base threshold) half hleft))).1
      ((mem_centralPositiveHalfStates_iff).1
        (centralPhysicalFiniteStateAt_mem_positive
          w hw (family.anchor base threshold) half
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w hw (family.anchor base threshold) half hright))).1
  rowDistance := family.rowDistance base threshold

/-- Sector-local row distance supplies the exact cofinal same-object gap
certificate consumed by the already constructed cutoff limits. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorRowDistance w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  centeredGap := by
    intro base threshold coefficient
    let later := family.anchor base threshold
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    let extended :=
      centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half moving
    have hbaseLater : base ≤ later :=
      Nat.le_trans (Nat.le_max_left base threshold)
        (family.anchor_ge base threshold)
    have hcenter :
        centralPhysicalFiniteVacuumSectorWeightedMean
            w hw later half extended ≈ 0 :=
      centralPhysicalFiniteVacuumSectorHeadCenteredExtension_meanZero
        hbaseLater coefficient
    have hfinite :=
      (family.finiteCertificate base threshold).absContraction
        extended hcenter
    have hmatrix :
        centralPhysicalFiniteVacuumSectorMatrixQuadratic
            w hw later half extended ≈
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
        hbaseLater coefficient
    have hdiagonal :
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw later half extended ≈
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteVacuumSectorHeadCenteredExtensionDiagonal_eqv_pulled
        hbaseLater coefficient
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm hmatrix)))
      (Q'.le_trans' _ _ _ hfinite
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left rate _ _
            (Q'.eqv_trans _ _ _
              (finiteWeightedSquare_vacuumSector_eqv_diagonal
                w hw later half extended)
              hdiagonal))))

/-- The corrected sector-local row frontier contracts all the way to the
strict comparison of the two moving centered Bishop-real limits. -/
theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorRowDistance
      w (Q'.le_of_lt hw0) half rate)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' rate)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) :=
  FixedNomeCofinalVacuumSectorCenteredStrictGap.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    hw0 hw1 half family.toVacuumSectorCenteredStrictGap base coefficient

end FixedNomeCofinalVacuumSectorRowDistance

end YMGap.Continuum.BF4PhysicalVacuumSectorCofinalRowGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCofinalRowGap.finiteCarrierStationaryProductJoint_quadratic_eqv_mean_square
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCofinalRowGap.FiniteCarrierStationaryProductRowDistanceCertificate.absContraction
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCofinalRowGap.finiteWeightedSquare_vacuumSector_eqv_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCofinalRowGap.FixedNomeCofinalVacuumSectorRowDistance.finiteCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCofinalRowGap.FixedNomeCofinalVacuumSectorRowDistance.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCofinalRowGap.FixedNomeCofinalVacuumSectorRowDistance.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
