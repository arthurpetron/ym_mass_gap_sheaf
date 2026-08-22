/-
# Cofinal rank-one row defects imply the fixed-nome physical BF4 gap

The canonical LDL route asks for a positive-semidefinite factorization of a
growing penalized matrix.  The existing weighted joint-law perturbation
theorem exposes a weaker sufficient interface.  At one finite cutoff it is
enough to compare the symmetric physical joint matrix with the stationary
rank-one joint

  (1 - q) d_i d_j

and bound the absolute error in every row by `q d_i`.  Exact centering kills
the rank-one quadratic, so the perturbation theorem gives

  |x^T K x| <= q x^T D x.

This file packages that row-defect condition, then shows that a
constructively cofinal family at one supplied `0 <= q < 1` feeds both the
global physical centered-gap interface and the moving vacuum-sector
cutoff-limit interface.

No cofinal row-defect family is constructed here.  The new certificate is an
alternative analytic target, not a claimed gap, thermodynamic limit,
continuum theory, or Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap

namespace YMGap.Continuum.BF4PhysicalCutoffCofinalRankOneDefectGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
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
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. The finite stationary rank-one comparison -/

/-- The stationary rank-one joint retained with mass `1 - q`. -/
def finiteStationaryRankOneJoint
    (q : Q') (weight : Nat → Q') (left right : Nat) : Q' :=
  ((1 : Q') - q) * (weight left * weight right)

/-- The rank-one quadratic factors as `(1-q)` times the square of the exact
weighted mean. -/
theorem finiteStationaryRankOneJoint_quadratic_eqv_mean_square
    (n : Nat) (q : Q') (weight coefficient : Nat → Q') :
    finiteJointQuadratic (List.range n) coefficient
        (finiteStationaryRankOneJoint q weight) ≈
      ((1 : Q') - q) *
        (finiteWeightedMean n weight coefficient *
          finiteWeightedMean n weight coefficient) := by
  let value : Nat → Q' := fun index => coefficient index * weight index
  have hterm : finiteJointQuadratic (List.range n) coefficient
        (finiteStationaryRankOneJoint q weight) ≈
    (listQSum
      (fun left => listQSum
        (fun right => ((1 : Q') - q) * (value left * value right))
        (List.range n))
      (List.range n)) := by
    unfold finiteJointQuadratic finiteStationaryRankOneJoint value
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    q_ring
  have hinner :
      listQSum
          (fun left => listQSum
            (fun right => ((1 : Q') - q) * (value left * value right))
            (List.range n))
          (List.range n) ≈
      (listQSum
        (fun left => ((1 : Q') - q) *
          listQSum
            (fun right => value left * value right)
            (List.range n))
        (List.range n)) := by
    apply listQSum_congr
    intro left
    exact listQSum_mul_left
      ((1 : Q') - q)
      (fun right => value left * value right)
      (List.range n)
  have houter :
      listQSum
          (fun left => ((1 : Q') - q) *
            listQSum
              (fun right => value left * value right)
              (List.range n))
          (List.range n) ≈
        ((1 : Q') - q) *
        listQSum
          (fun left => listQSum
            (fun right => value left * value right)
            (List.range n))
          (List.range n) :=
    listQSum_mul_left
      ((1 : Q') - q)
      (fun left => listQSum
        (fun right => value left * value right)
        (List.range n))
      (List.range n)
  have hproduct :
      listQSum
          (fun left => listQSum
            (fun right => value left * value right)
            (List.range n))
          (List.range n) ≈
        finiteWeightedMean n weight coefficient *
          finiteWeightedMean n weight coefficient := by
    unfold finiteWeightedMean value
    exact listQSum_product value value (List.range n) (List.range n)
  exact Q'.eqv_trans _ _ _ hterm
    (Q'.eqv_trans _ _ _ hinner
      (Q'.eqv_trans _ _ _ houter
        (Q'.mul_eqv_congr_left _ _ _ hproduct)))

/-- Exact weighted centering annihilates the stationary rank-one quadratic. -/
theorem finiteStationaryRankOneJoint_quadratic_centered_eqv_zero
    {n : Nat} {q : Q'} {weight coefficient : Nat → Q'}
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    finiteJointQuadratic (List.range n) coefficient
        (finiteStationaryRankOneJoint q weight) ≈ 0 := by
  refine Q'.eqv_trans _
    (((1 : Q') - q) *
      (finiteWeightedMean n weight coefficient *
        finiteWeightedMean n weight coefficient)) _
    (finiteStationaryRankOneJoint_quadratic_eqv_mean_square
      n q weight coefficient) ?_
  refine Q'.eqv_trans _ (((1 : Q') - q) * (0 * 0)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _
        (0 * finiteWeightedMean n weight coefficient) _
        (Q'.mul_eqv_congr_right _ _ _ hcenter)
        (Q'.mul_eqv_congr_left 0 _ _ hcenter))
  · exact Q'.eqv_trans _ (((1 : Q') - q) * 0) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv 0))
      (Q'.mul_zero_eqv ((1 : Q') - q))

/-- The generic weighted-square convention agrees with the indexed diagonal
quadratic up to exact rational equivalence. -/
theorem finiteWeightedSquare_range_eqv_diagonal
    (n : Nat) (weight coefficient : Nat → Q') :
    finiteWeightedSquare (List.range n) weight coefficient ≈
      finiteDiagonalQuadratic n weight coefficient := by
  unfold finiteWeightedSquare finiteDiagonalQuadratic
  apply listQSum_congr
  intro index
  exact Q'.mul_comm_eqv _ _

/-- A row-relative comparison with the stationary rank-one joint.  This is
the precise finite input consumed by the weighted Young perturbation theorem;
it asks for no LDL factors or matrix positivity certificate. -/
structure FiniteStationaryRankOneRowDefectCertificate
    (n : Nat) (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q') : Type 1 where
  kernelSymmetric : ∀ left right,
    left ∈ List.range n → right ∈ List.range n →
      kernel left right ≈ kernel right left
  rowDefect : ∀ source, source ∈ List.range n →
    finiteJointDifferenceAbsRowMass
        (List.range n) kernel
        (finiteStationaryRankOneJoint q weight) source ≤
      q * weight source

namespace FiniteStationaryRankOneRowDefectCertificate

/-- The row-defect certificate proves the absolute centered finite form
bound at the same rate. -/
theorem absContraction
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    (certificate :
      FiniteStationaryRankOneRowDefectCertificate n q weight kernel)
    (coefficient : Nat → Q')
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    Q'.abs (finiteMatrixQuadratic n kernel coefficient) ≤
      q * finiteDiagonalQuadratic n weight coefficient := by
  have hrankSymmetric : ∀ left right,
      left ∈ List.range n → right ∈ List.range n →
        finiteStationaryRankOneJoint q weight left right ≈
          finiteStationaryRankOneJoint q weight right left := by
    intro left right _ _
    unfold finiteStationaryRankOneJoint
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv (weight left) (weight right))
  have hperturb := finiteJointQuadratic_abs_sub_le_weightedSquare
    (List.range n) coefficient weight kernel
    (finiteStationaryRankOneJoint q weight) q
    certificate.kernelSymmetric hrankSymmetric certificate.rowDefect
  have hrank :=
    finiteStationaryRankOneJoint_quadratic_centered_eqv_zero
      (q := q) hcenter
  have hdiff :
      finiteJointQuadratic (List.range n) coefficient kernel +
          (-finiteJointQuadratic (List.range n) coefficient
            (finiteStationaryRankOneJoint q weight)) ≈
        finiteJointQuadratic (List.range n) coefficient kernel := by
    refine Q'.eqv_trans _
      (finiteJointQuadratic (List.range n) coefficient kernel + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ (-0) _
          (Q'.neg_eqv_congr _ _ hrank) (by decide))
    · exact Q'.eqv_of_eq (Q'.add_zero' _)
  have hleft :
      Q'.abs (finiteMatrixQuadratic n kernel coefficient) ≈
        Q'.abs
          (finiteJointQuadratic (List.range n) coefficient kernel +
            (-finiteJointQuadratic (List.range n) coefficient
              (finiteStationaryRankOneJoint q weight))) := by
    unfold finiteMatrixQuadratic
    exact Q'.abs_eqv_congr (Q'.eqv_symm hdiff)
  have hright :
      q * finiteWeightedSquare (List.range n) weight coefficient ≈
        q * finiteDiagonalQuadratic n weight coefficient :=
    Q'.mul_eqv_congr_left q _ _
      (finiteWeightedSquare_range_eqv_diagonal n weight coefficient)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hperturb (Q'.le_of_eqv hright))

end FiniteStationaryRankOneRowDefectCertificate

/-! ## 2. A cofinal physical row-defect family -/

/-- One strict rate and a constructively cofinal family of finite physical
rank-one row-defect certificates. -/
structure CofinalFiniteStationaryRankOneRowDefect
    (q : Q') (size : Nat → Nat)
    (weight : Nat → Nat → Q')
    (kernel : Nat → Nat → Nat → Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  anchor : Nat → Nat
  anchor_ge : ∀ base, base ≤ anchor base
  certificate : ∀ base,
    FiniteStationaryRankOneRowDefectCertificate
      (size (anchor base)) q
      (weight (anchor base))
      (kernel (anchor base))

/-- Physical specialization of the generic cofinal row-defect family.  The
abbreviation keeps the large physical proof fields out of structure
elaboration. -/
abbrev FixedNomeCofinalPhysicalRankOneRowDefect
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (q : Q') : Type 1 :=
  CofinalFiniteStationaryRankOneRowDefect q
    (fun cutoff => centralPhysicalFiniteCarrierSize w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteWeight w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteKernel w hw cutoff half)

namespace FixedNomeCofinalPhysicalRankOneRowDefect

/-- The cofinal row-defect family supplies the existing global physical
centered-gap interface. -/
def toCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (family : FixedNomeCofinalPhysicalRankOneRowDefect w hw half q) :
    FixedNomeCofinalCenteredStrictGap w hw half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  meanZeroGap := by
    intro base observable hcenter
    let cutoff := family.anchor base
    let coefficient :=
      centralPhysicalFiniteCoefficient w hw cutoff half observable
    have hindexed := (family.certificate base).absContraction coefficient
      (centralPhysicalFiniteCoefficient_centered hcenter)
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
          (Q'.mul_eqv_congr_left q _ _ hdiagonal)))

/-- The same row-defect family also feeds the moving same-object vacuum-sector
certificate.  Reindexing by `max base threshold` supplies both sector
containment and constructive cofinality. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (family : FixedNomeCofinalPhysicalRankOneRowDefect w hw half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half q where
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
          q * finiteDiagonalQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended :=
      (family.certificate request).absContraction extended hcenter
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
          (Q'.mul_eqv_congr_left q _ _ hdiagonal)))

/-- Cofinal rank-one row control therefore proves the strict comparison
between the literal moving centered form limits. -/
theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (family : FixedNomeCofinalPhysicalRankOneRowDefect
      w (Q'.le_of_lt hw0) half q)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' q)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) :=
  FixedNomeCofinalVacuumSectorCenteredStrictGap.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    hw0 hw1 half family.toVacuumSectorCenteredStrictGap base coefficient

end FixedNomeCofinalPhysicalRankOneRowDefect

/-! ## Axiom audit -/

#print axioms finiteStationaryRankOneJoint_quadratic_eqv_mean_square
#print axioms finiteStationaryRankOneJoint_quadratic_centered_eqv_zero
#print axioms finiteWeightedSquare_range_eqv_diagonal
#print axioms FiniteStationaryRankOneRowDefectCertificate.absContraction
#print axioms FixedNomeCofinalPhysicalRankOneRowDefect.toCenteredStrictGap
#print axioms FixedNomeCofinalPhysicalRankOneRowDefect.toVacuumSectorCenteredStrictGap
#print axioms FixedNomeCofinalPhysicalRankOneRowDefect.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal

end YMGap.Continuum.BF4PhysicalCutoffCofinalRankOneDefectGap
