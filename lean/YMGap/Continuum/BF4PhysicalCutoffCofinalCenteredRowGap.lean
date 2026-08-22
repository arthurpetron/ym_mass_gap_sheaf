/-
# Cofinal physical centered rows imply the fixed-nome BF4 gap

The literal physical quantity `physicalCenteredPhysicalRowMass` is already
the rowwise distance between the normalized reflected joint and the full
stationary product joint.  Existing BF4 density, buffer, and local-gluing
interfaces target bounds on exactly this quantity.

This file transports those literal-carrier row bounds through the canonical
finite indexing.  Since exact centering annihilates the stationary product
quadratic, the weighted Young estimate gives the centered form contraction.
A constructively cofinal family therefore feeds both the global physical gap
interface and the moving same-object vacuum-sector cutoff-limit interface.

No cofinal physical row family is constructed here.  This is an exact adapter
from the existing analytic target, not a claimed gap, thermodynamic limit,
continuum theory, or Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4CommonRankOneRowTriangle
import YMGap.Continuum.BF4PhysicalCutoffCofinalRankOneDefectGap

namespace YMGap.Continuum.BF4PhysicalCutoffCofinalCenteredRowGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4PhysicalCutoffCofinalRankOneDefectGap
open YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Full stationary-product comparison -/

/-- The full stationary product joint, with its comparison mass independent
of the requested contraction rate. -/
def finiteStationaryProductJoint
    (weight : Nat → Q') (left right : Nat) : Q' :=
  weight left * weight right

/-- Exact weighted centering annihilates the full stationary-product
quadratic. -/
theorem finiteStationaryProductJoint_quadratic_centered_eqv_zero
    {n : Nat} {weight coefficient : Nat → Q'}
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    finiteJointQuadratic (List.range n) coefficient
        (finiteStationaryProductJoint weight) ≈ 0 := by
  have hreference :
      finiteJointQuadratic (List.range n) coefficient
          (finiteStationaryProductJoint weight) ≈
        finiteJointQuadratic (List.range n) coefficient
          (finiteStationaryRankOneJoint 0 weight) := by
    unfold finiteJointQuadratic
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    unfold finiteStationaryProductJoint finiteStationaryRankOneJoint
    exact Q'.mul_eqv_congr_left
      (coefficient left * coefficient right) _ _
      (Q'.eqv_symm
        (Q'.eqv_trans _
          (1 * (weight left * weight right)) _
          (Q'.mul_eqv_congr_right _ _ _ (by decide))
          (Q'.one_mul_eqv _)))
  exact Q'.eqv_trans _ _ _ hreference
    (finiteStationaryRankOneJoint_quadratic_centered_eqv_zero
      (q := 0) hcenter)

/-- A symmetric finite kernel is within `rate * weight(source)` of the full
stationary product joint in every row. -/
structure FiniteStationaryProductRowDistanceCertificate
    (n : Nat) (rate : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q') : Type 1 where
  kernelSymmetric : ∀ left right,
    left ∈ List.range n → right ∈ List.range n →
      kernel left right ≈ kernel right left
  rowDistance : ∀ source, source ∈ List.range n →
    finiteJointDifferenceAbsRowMass
        (List.range n) kernel
        (finiteStationaryProductJoint weight) source ≤
      rate * weight source

namespace FiniteStationaryProductRowDistanceCertificate

/-- Full stationary-product row distance proves the absolute centered finite
form bound at the same rate. -/
theorem absContraction
    {n : Nat} {rate : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    (certificate :
      FiniteStationaryProductRowDistanceCertificate
        n rate weight kernel)
    (coefficient : Nat → Q')
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    Q'.abs (finiteMatrixQuadratic n kernel coefficient) ≤
      rate * finiteDiagonalQuadratic n weight coefficient := by
  have hproductSymmetric : ∀ left right,
      left ∈ List.range n → right ∈ List.range n →
        finiteStationaryProductJoint weight left right ≈
          finiteStationaryProductJoint weight right left := by
    intro left right _ _
    unfold finiteStationaryProductJoint
    exact Q'.mul_comm_eqv _ _
  have hperturb := finiteJointQuadratic_abs_sub_le_weightedSquare
    (List.range n) coefficient weight kernel
    (finiteStationaryProductJoint weight) rate
    certificate.kernelSymmetric hproductSymmetric certificate.rowDistance
  have hproduct :=
    finiteStationaryProductJoint_quadratic_centered_eqv_zero hcenter
  have hdiff :
      finiteJointQuadratic (List.range n) coefficient kernel +
          (-finiteJointQuadratic (List.range n) coefficient
            (finiteStationaryProductJoint weight)) ≈
        finiteJointQuadratic (List.range n) coefficient kernel := by
    refine Q'.eqv_trans _
      (finiteJointQuadratic (List.range n) coefficient kernel + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ (-0) _
          (Q'.neg_eqv_congr _ _ hproduct) (by decide))
    · exact Q'.eqv_of_eq (Q'.add_zero' _)
  have hleft :
      Q'.abs (finiteMatrixQuadratic n kernel coefficient) ≈
        Q'.abs
          (finiteJointQuadratic (List.range n) coefficient kernel +
            (-finiteJointQuadratic (List.range n) coefficient
              (finiteStationaryProductJoint weight))) := by
    unfold finiteMatrixQuadratic
    exact Q'.abs_eqv_congr (Q'.eqv_symm hdiff)
  have hright :
      rate * finiteWeightedSquare (List.range n) weight coefficient ≈
        rate * finiteDiagonalQuadratic n weight coefficient :=
    Q'.mul_eqv_congr_left rate _ _
      (finiteWeightedSquare_range_eqv_diagonal n weight coefficient)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hperturb (Q'.le_of_eqv hright))

end FiniteStationaryProductRowDistanceCertificate

/-! ## 2. Exact literal-carrier to finite-index row transport -/

/-- Totalized finite indexing preserves a joint-row distance exactly. -/
theorem finiteIndexJointDifferenceAbsRowMass_eqv_list
    {State : Type} (states : List State) (fallback : State)
    (leftJoint rightJoint : State → State → Q') (source : Nat) :
    finiteJointDifferenceAbsRowMass
        (List.range states.length)
        (fun left right => leftJoint
          (finiteListStateAt states fallback left)
          (finiteListStateAt states fallback right))
        (fun left right => rightJoint
          (finiteListStateAt states fallback left)
          (finiteListStateAt states fallback right))
        source ≈
      finiteJointDifferenceAbsRowMass states leftJoint rightJoint
        (finiteListStateAt states fallback source) := by
  unfold finiteJointDifferenceAbsRowMass
  exact Q'.eqv_of_eq
    (finiteIndexSum_eq_listQSum states fallback
      (fun target =>
        Q'.abs
          (leftJoint (finiteListStateAt states fallback source) target +
            (-rightJoint
              (finiteListStateAt states fallback source) target))))

/-- The indexed row distance from the full stationary product is exactly the
literal physical centered row mass at the indexed source. -/
theorem centralPhysicalFiniteStationaryProductRowDistance_eqv
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) :
    finiteJointDifferenceAbsRowMass
        (List.range
          (centralPhysicalFiniteCarrierSize w hw cutoff half))
        (centralPhysicalFiniteKernel w hw cutoff half)
        (finiteStationaryProductJoint
          (centralPhysicalFiniteWeight w hw cutoff half))
        source ≈
      physicalCenteredPhysicalRowMass w hw cutoff half
        (centralPhysicalFiniteStateAt w hw cutoff half source) := by
  let states := centralPositiveHalfStates w hw cutoff half
  let stateAt := finiteListStateAt states zeroEdgeLabelling
  let physical :=
    centralNormalizedPhysicalReflectedKernel w hw cutoff half
  let vacuum := centralPhysicalVacuumJoint w hw cutoff half
  have hindexed :
      finiteJointDifferenceAbsRowMass
          (List.range
            (centralPhysicalFiniteCarrierSize w hw cutoff half))
          (centralPhysicalFiniteKernel w hw cutoff half)
          (finiteStationaryProductJoint
            (centralPhysicalFiniteWeight w hw cutoff half))
          source ≈
        finiteJointDifferenceAbsRowMass
          (List.range states.length)
          (fun left right => physical (stateAt left) (stateAt right))
          (fun left right => vacuum (stateAt left) (stateAt right))
          source := by
    unfold finiteJointDifferenceAbsRowMass
    apply listQSum_congr_on
    intro target _
    apply Q'.abs_eqv_congr
    apply Q'.add_eqv_congr'
    · exact Q'.eqv_refl _
    · exact Q'.neg_eqv_congr _ _ (Q'.eqv_refl _)
  have hpulled := finiteIndexJointDifferenceAbsRowMass_eqv_list
    states zeroEdgeLabelling physical vacuum source
  exact Q'.eqv_trans _ _ _ hindexed hpulled

/-! ## 3. A cofinal family in the repository's physical row language -/

/-- Generic cofinal finite joint-row distance.  Keeping the large physical
specialization out of structure elaboration makes the certificate usable at
the full BF4 carrier without changing its mathematical content. -/
structure CofinalFiniteJointRowDistance
    {State : Type}
    (rate : Q') (states : Nat → List State)
    (weight : Nat → State → Q')
    (leftJoint rightJoint : Nat → State → State → Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat
  anchor_ge : ∀ base, base ≤ anchor base
  rowDistance : ∀ base source,
    source ∈ states (anchor base) →
      finiteJointDifferenceAbsRowMass
          (states (anchor base))
          (leftJoint (anchor base))
          (rightJoint (anchor base)) source ≤
        rate * weight (anchor base) source

/-- One strict rate and a constructively cofinal family of the literal
physical centered-row estimates already targeted by the BF4 analytic
producers. -/
abbrev FixedNomeCofinalPhysicalCenteredRowDistance
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type 1 :=
  CofinalFiniteJointRowDistance rate
    (fun cutoff => centralPositiveHalfStates w hw cutoff half)
    (fun cutoff => centralPhysicalRowMarginal w hw cutoff half)
    (fun cutoff => centralNormalizedPhysicalReflectedKernel
      w hw cutoff half)
    (fun cutoff => centralPhysicalVacuumJoint w hw cutoff half)

namespace FixedNomeCofinalPhysicalCenteredRowDistance

/-- Literal physical row estimates produce the canonically indexed finite
stationary-product certificate at every selected cutoff. -/
def finiteCertificate
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family :
      FixedNomeCofinalPhysicalCenteredRowDistance w hw half rate)
    (base : Nat) :
    FiniteStationaryProductRowDistanceCertificate
      (centralPhysicalFiniteCarrierSize w hw (family.anchor base) half)
      rate
      (centralPhysicalFiniteWeight w hw (family.anchor base) half)
      (centralPhysicalFiniteKernel w hw (family.anchor base) half) where
  kernelSymmetric := by
    intro left right hleft hright
    unfold centralPhysicalFiniteKernel
    exact centralNormalizedPhysicalReflectedKernel_symm
      ((mem_centralPositiveHalfStates_iff).1
        (centralPhysicalFiniteStateAt_mem_positive
          w hw (family.anchor base) half
          (List.mem_range.mp hleft))).1
      ((mem_centralPositiveHalfStates_iff).1
        (centralPhysicalFiniteStateAt_mem_positive
          w hw (family.anchor base) half
          (List.mem_range.mp hright))).1
  rowDistance := by
    intro source hsource
    have hphysical := family.rowDistance base
      (centralPhysicalFiniteStateAt
        w hw (family.anchor base) half source)
      (centralPhysicalFiniteStateAt_mem_positive
        w hw (family.anchor base) half
        (List.mem_range.mp hsource))
    change physicalCenteredPhysicalRowMass
        w hw (family.anchor base) half
          (centralPhysicalFiniteStateAt
            w hw (family.anchor base) half source) ≤
      rate * centralPhysicalRowMarginal
        w hw (family.anchor base) half
          (centralPhysicalFiniteStateAt
            w hw (family.anchor base) half source) at hphysical
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
      (centralPhysicalFiniteStationaryProductRowDistance_eqv
          w hw (family.anchor base) half source))
      hphysical

/-- Cofinal literal physical centered rows supply the global physical
centered-gap interface. -/
def toCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family :
      FixedNomeCofinalPhysicalCenteredRowDistance w hw half rate) :
    FixedNomeCofinalCenteredStrictGap w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  meanZeroGap := by
    intro base observable hcenter
    let cutoff := family.anchor base
    let coefficient :=
      centralPhysicalFiniteCoefficient w hw cutoff half observable
    have hindexed := (family.finiteCertificate base).absContraction
      coefficient (centralPhysicalFiniteCoefficient_centered hcenter)
    have hmatrix :=
      centralPhysicalFiniteMatrixQuadratic_eqv_jointQuadratic
        w hw cutoff half observable
    have hdiagonal :=
      centralPhysicalFiniteDiagonalQuadratic_eqv_weightedInner
        w hw cutoff half observable
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm hmatrix)))
      (Q'.le_trans' _ _ _ hindexed
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left rate _ _ hdiagonal)))

/-- The same cofinal physical rows control the moving, exactly centered
same-object vacuum sector after zero extension to the full carrier. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family :
      FixedNomeCofinalPhysicalCenteredRowDistance w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := fun base threshold => family.anchor (max base threshold)
  anchor_ge := by
    intro base threshold
    exact family.anchor_ge (max base threshold)
  centeredGap := by
    intro base threshold coefficient
    let request := max base threshold
    let later := family.anchor request
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    let extended :=
      centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half moving
    have hrequestLater : request ≤ later := family.anchor_ge request
    have hbaseLater : base ≤ later :=
      Nat.le_trans (Nat.le_max_left base threshold) hrequestLater
    have hcenter :
        finiteWeightedMean
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended ≈ 0 :=
      centralPhysicalFiniteFullCarrierHeadCenteredExtension_meanZero
        hbaseLater coefficient
    have hfinite :
        Q'.abs
            (finiteMatrixQuadratic
              (centralPhysicalFiniteCarrierSize w hw later half)
              (centralPhysicalFiniteKernel w hw later half)
              extended) ≤
          rate * finiteDiagonalQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended :=
      (family.finiteCertificate request).absContraction extended hcenter
    have hmatrix :
        finiteMatrixQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteKernel w hw later half)
            extended ≈
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteFullCarrierCoefficientExtensionMatrix_eqv_pulled
        hbaseLater moving
    have hdiagonal :
        finiteDiagonalQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended ≈
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteFullCarrierCoefficientExtensionDiagonal_eqv_pulled
        hbaseLater moving
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (Q'.eqv_symm hmatrix)))
      (Q'.le_trans' _ _ _ hfinite
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left rate _ _ hdiagonal)))

/-- Cofinal literal physical centered-row control therefore proves the strict
comparison between the moving centered form limits. -/
theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {rate : Q'}
    (family : FixedNomeCofinalPhysicalCenteredRowDistance
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

end FixedNomeCofinalPhysicalCenteredRowDistance

/-! ## Axiom audit -/

#print axioms finiteStationaryProductJoint_quadratic_centered_eqv_zero
#print axioms FiniteStationaryProductRowDistanceCertificate.absContraction
#print axioms centralPhysicalFiniteStationaryProductRowDistance_eqv
#print axioms FixedNomeCofinalPhysicalCenteredRowDistance.finiteCertificate
#print axioms FixedNomeCofinalPhysicalCenteredRowDistance.toCenteredStrictGap
#print axioms FixedNomeCofinalPhysicalCenteredRowDistance.toVacuumSectorCenteredStrictGap
#print axioms FixedNomeCofinalPhysicalCenteredRowDistance.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal

end YMGap.Continuum.BF4PhysicalCutoffCofinalCenteredRowGap
