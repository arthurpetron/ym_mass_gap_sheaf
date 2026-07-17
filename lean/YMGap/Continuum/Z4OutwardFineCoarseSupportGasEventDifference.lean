/-
# Event-disagreement control of the outward geometry drift

At fixed coupling, changing the three outward queries changes only the
Boolean event imposed on each compatible surface family.  This file proves
the exact finite-measure inequality

  |N(E) - N(F)| <= N(E xor F)

for nonnegative compatible-family weights, and specializes it to the
fine/coarse query-geometry term in the physical retune defect.  The remaining
quantitative input is an honest relative bound on the disagreement event; no
event nesting is assumed.
-/

import YMGap.Continuum.Z4OutwardFineCoarseSupportGasErrorSplit
import YMGap.Continuum.Z4FiniteCylinderQuadraticStability

namespace YMGap.Continuum.Z4OutwardFineCoarseSupportGasEventDifference

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.ContinuumYMStack
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasErrorSplit
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

def supportEventDisagreement {A : Type}
    (first second : A -> Bool) (item : A) : Bool :=
  first item ^^ second item

private theorem listQSum_mask_eq_filter_local {A : Type}
    (weight : A -> Q') (event : A -> Bool) :
    forall source : List A,
      listQSum (fun item => if event item then weight item else 0) source ≈
        listQSum weight (source.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hevent : event head with
      | false =>
          simp only [hevent, Bool.false_eq_true, if_false,
            List.filter_cons, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum weight (tail.filter event)) _
            (Q'.add_eqv_congr' (Q'.eqv_refl 0)
              (listQSum_mask_eq_filter_local weight event tail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [hevent, if_true, List.filter_cons, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_mask_eq_filter_local weight event tail)

private theorem add_neg_zero_eqv_local (value : Q') :
    value + (-(0 : Q')) ≈ value := by
  refine Q'.eqv_trans _ (value + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl value)
      (by decide : (-(0 : Q')) ≈ 0)
  · exact Q'.eqv_of_eq (Q'.add_zero' value)

private theorem abs_masked_event_sub_le_disagreement {A : Type}
    (weight : A -> Q') (hweight : forall item, (0 : Q') <= weight item)
    (first second : A -> Bool) (item : A) :
    Q'.abs
        ((if first item then weight item else 0) +
          (-(if second item then weight item else 0))) <=
      (if supportEventDisagreement first second item then
        weight item else 0) := by
  cases hfirst : first item <;> cases hsecond : second item
  · simp [supportEventDisagreement, hfirst, hsecond]
    decide
  · simp [supportEventDisagreement, hfirst, hsecond]
    have hrewrite := Q'.abs_eqv_congr
      (Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv 0 (-(weight item)))
        (Q'.eqv_of_eq (Q'.add_zero' (-(weight item)))))
    have habsNeg := Q'.abs_neg' (weight item)
    rw [abs_of_nonneg (hweight item)] at habsNeg
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ hrewrite habsNeg)
  · simp [supportEventDisagreement, hfirst, hsecond]
    have hrewrite := Q'.abs_eqv_congr (add_neg_zero_eqv_local (weight item))
    rw [abs_of_nonneg (hweight item)] at hrewrite
    exact Q'.le_of_eqv hrewrite
  · simp [supportEventDisagreement, hfirst, hsecond]
    have hzero := Q'.abs_eqv_congr (Q'.add_neg_self_eqv (weight item))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hzero) (by decide)

/-- For a finite nonnegative weighted space, the absolute difference between
two event numerators is bounded by the numerator of their disagreement
event.  List multiplicities are retained exactly. -/
theorem abs_listQSum_filter_sub_le_disagreement {A : Type}
    (weight : A -> Q') (hweight : forall item, (0 : Q') <= weight item)
    (first second : A -> Bool) (source : List A) :
    Q'.abs
        (listQSum weight (source.filter first) +
          (-listQSum weight (source.filter second))) <=
      listQSum weight
        (source.filter (supportEventDisagreement first second)) := by
  let firstMasked : A -> Q' := fun item =>
    if first item then weight item else 0
  let secondMasked : A -> Q' := fun item =>
    if second item then weight item else 0
  let disagreementMasked : A -> Q' := fun item =>
    if supportEventDisagreement first second item then weight item else 0
  have hfirst := listQSum_mask_eq_filter_local weight first source
  have hsecond := listQSum_mask_eq_filter_local weight second source
  have hdisagreement := listQSum_mask_eq_filter_local weight
    (supportEventDisagreement first second) source
  have hleft :
      Q'.abs
          (listQSum weight (source.filter first) +
            (-listQSum weight (source.filter second))) ≈
        Q'.abs
          (listQSum firstMasked source +
            (-listQSum secondMasked source)) := by
    apply Q'.abs_eqv_congr
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm hfirst)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hsecond))
  have htriangle := abs_listQSum_sub_le firstMasked secondMasked source
  have hpointwise :
      listQSum
          (fun item => Q'.abs
            (firstMasked item + (-secondMasked item))) source <=
        listQSum disagreementMasked source := by
    apply listQSum_mono
    intro item _
    exact abs_masked_event_sub_le_disagreement
      weight hweight first second item
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) htriangle)
    (Q'.le_trans' _ _ _ hpointwise (Q'.le_of_eqv hdisagreement))

/-- Compatible-support specialization of the finite disagreement inequality. -/
theorem compatibleSupportEventNumerator_abs_sub_le_disagreement
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (cutoff n : Nat) (first second : List (List Nat) -> Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventNumerator
            coupling cutoff n first +
          (-couplingParametricKCompatibleSupportEventNumerator
            coupling cutoff n second)) <=
      couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff n (supportEventDisagreement first second) := by
  unfold couplingParametricKCompatibleSupportEventNumerator
  exact abs_listQSum_filter_sub_le_disagreement
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff n)
    first second (canonicalCompatibleAmbientFamilies n)

def outwardFineCoarseGeometryDisagreementNumerator
    (fineCoupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  couplingParametricKCompatibleSupportEventNumerator
    fineCoupling 1 6
    (supportEventDisagreement
      (outwardComponentSubsupportFamilyPatternEvent
        outwardCoarseQueries pattern)
      (outwardComponentSubsupportFamilyPatternEvent
        outwardFineQueries pattern))

theorem outwardFineCoarseSupportGeometryCrossDifference_eqv
    (fineCoupling : Q') (pattern : ThreeBlockPattern) :
    outwardFineCoarseSupportGeometryCrossDifference
        fineCoupling pattern ≈
      (outwardFineCouplingCoarseQueryNumerator fineCoupling pattern +
        (-outwardFineCompatibleSupportPatternNumerator
          fineCoupling pattern)) *
        outwardCoarseCompatibleSupportPartition fineCoupling := by
  unfold outwardFineCoarseSupportGeometryCrossDifference
  refine Q'.eqv_trans _
    (outwardFineCouplingCoarseQueryNumerator fineCoupling pattern *
        outwardCoarseCompatibleSupportPartition fineCoupling +
      (-outwardFineCompatibleSupportPatternNumerator fineCoupling pattern) *
        outwardCoarseCompatibleSupportPartition fineCoupling) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_symm (Q'.neg_mul_eqv
        (outwardFineCompatibleSupportPatternNumerator fineCoupling pattern)
        (outwardCoarseCompatibleSupportPartition fineCoupling)))
  · exact Q'.eqv_symm (Q'.add_mul_eqv
      (outwardFineCouplingCoarseQueryNumerator fineCoupling pattern)
      (-outwardFineCompatibleSupportPatternNumerator fineCoupling pattern)
      (outwardCoarseCompatibleSupportPartition fineCoupling))

theorem outwardFineCoarseSupportGeometryCrossDifference_abs_le_disagreement
    (fineCoupling : Q') (hfine : (0 : Q') <= fineCoupling)
    (pattern : ThreeBlockPattern) :
    Q'.abs (outwardFineCoarseSupportGeometryCrossDifference
        fineCoupling pattern) <=
      outwardFineCoarseGeometryDisagreementNumerator
          fineCoupling pattern *
        outwardCoarseCompatibleSupportPartition fineCoupling := by
  have hrewrite := Q'.abs_eqv_congr
    (outwardFineCoarseSupportGeometryCrossDifference_eqv
      fineCoupling pattern)
  have hproduct := abs_mul_le
    (outwardFineCouplingCoarseQueryNumerator fineCoupling pattern +
      (-outwardFineCompatibleSupportPatternNumerator fineCoupling pattern))
    (outwardCoarseCompatibleSupportPartition fineCoupling)
  have hnumerator := compatibleSupportEventNumerator_abs_sub_le_disagreement
    hfine 1 6
    (outwardComponentSubsupportFamilyPatternEvent
      outwardCoarseQueries pattern)
    (outwardComponentSubsupportFamilyPatternEvent
      outwardFineQueries pattern)
  have hpartition : (0 : Q') <=
      outwardCoarseCompatibleSupportPartition fineCoupling :=
    listQSum_nonnegative_generic _
      (couplingParametricKSupportFamilyActivity_nonnegative
        (unitCubeBlockCoupling_nonnegative hfine) 1 6) _
  have habsPartition : Q'.abs
      (outwardCoarseCompatibleSupportPartition fineCoupling) =
        outwardCoarseCompatibleSupportPartition fineCoupling :=
    abs_of_nonneg hpartition
  rw [habsPartition] at hproduct
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hrewrite) hproduct)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hnumerator hpartition)

def OutwardFineCoarseGeometryDisagreementBound
    (fineCoupling bound : Q') : Prop :=
  forall pattern,
    outwardFineCoarseGeometryDisagreementNumerator
        fineCoupling pattern <=
      bound * outwardFineCompatibleSupportPatternNumerator
        fineCoupling pattern

/-- Multiplying a relative numerator estimate by a nonnegative common
partition preserves the bound, with the denominator associated exactly. -/
theorem abs_le_relative_scaled
    (value disagreement bound numerator partition : Q')
    (hvalue : Q'.abs value <= disagreement * partition)
    (hdisagreement : disagreement <= bound * numerator)
    (hpartition : (0 : Q') <= partition) :
    Q'.abs value <= bound * (numerator * partition) := by
  have hscaled : disagreement * partition <=
      (bound * numerator) * partition :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdisagreement hpartition
  have hchain : Q'.abs value <= (bound * numerator) * partition :=
    Q'.le_trans' _ _ _ hvalue hscaled
  exact Q'.le_trans' _ _ _ hchain
    (Q'.le_of_eqv (Q'.mul_assoc_eqv bound numerator partition))

def OutwardFineCoarseScaledGeometryDisagreementBound
    (fineCoupling bound : Q') : Prop :=
  forall pattern,
    outwardFineCoarseGeometryDisagreementNumerator fineCoupling pattern *
        outwardCoarseCompatibleSupportPartition fineCoupling <=
      bound * outwardFineCoarseCompatibleSupportDenominator
        fineCoupling pattern

/-- A scaled disagreement-event estimate supplies exactly the geometry
component bound consumed by the support-error split.  The generic
`abs_le_relative_scaled` lemma above converts a numerator-relative estimate
to this form once a chosen application exposes its denominator factorization. -/
theorem outwardFineCoarseSupportGeometryBound_of_scaledDisagreement
    (fineCoupling : Q') (hfine : (0 : Q') <= fineCoupling)
    (bound : Q')
    (hdisagreement : OutwardFineCoarseScaledGeometryDisagreementBound
      fineCoupling bound) :
    OutwardFineCoarseSupportGeometryCrossDifferenceBound
      fineCoupling bound := by
  intro pattern
  let value : Q' :=
    outwardFineCoarseSupportGeometryCrossDifference fineCoupling pattern
  let left : Q' := absQ value
  let absolute : Q' := Q'.abs value
  let middle : Q' :=
    outwardFineCoarseGeometryDisagreementNumerator fineCoupling pattern *
      outwardCoarseCompatibleSupportPartition fineCoupling
  let right : Q' := bound *
    outwardFineCoarseCompatibleSupportDenominator fineCoupling pattern
  have hraw :=
    outwardFineCoarseSupportGeometryCrossDifference_abs_le_disagreement
      fineCoupling hfine pattern
  have habsolute : absolute <= middle := hraw
  have hbridge : left <= absolute :=
    Q'.le_of_eqv (absQ_eqv_abs value)
  have hright : middle <= right := hdisagreement pattern
  change left <= right
  exact Q'.le_trans' left absolute right hbridge
    (Q'.le_trans' absolute middle right habsolute hright)

theorem outwardFineCoarseCompatibleSupportDenominator_eqv_factorized
    (fineCoupling : Q') (pattern : ThreeBlockPattern) :
    outwardFineCoarseCompatibleSupportDenominator fineCoupling pattern ≈
      outwardFineCompatibleSupportPatternNumerator fineCoupling pattern *
        outwardCoarseCompatibleSupportPartition fineCoupling := by
  unfold outwardFineCoarseCompatibleSupportDenominator
  exact Q'.eqv_refl _

/-- The clean quantitative interface: it is enough to inject the fine/coarse
query-disagreement event into the fine pattern event with a relative activity
cost.  Positivity of all eight fine pattern masses is proved by the outward
fine-carrier development; it is not assumed or reconstructed here. -/
theorem outwardFineCoarseSupportGeometryBound_of_disagreement
    (fineCoupling : Q') (hfine : (0 : Q') <= fineCoupling)
    (bound : Q')
    (hdisagreement : OutwardFineCoarseGeometryDisagreementBound
      fineCoupling bound) :
    OutwardFineCoarseSupportGeometryCrossDifferenceBound
      fineCoupling bound := by
  apply outwardFineCoarseSupportGeometryBound_of_scaledDisagreement
    fineCoupling hfine bound
  intro pattern
  let partition := outwardCoarseCompatibleSupportPartition fineCoupling
  let fineNumerator :=
    outwardFineCompatibleSupportPatternNumerator fineCoupling pattern
  let disagreement :=
    outwardFineCoarseGeometryDisagreementNumerator fineCoupling pattern
  let denominator :=
    outwardFineCoarseCompatibleSupportDenominator fineCoupling pattern
  have hpartition : (0 : Q') <= partition :=
    listQSum_nonnegative_generic _
      (couplingParametricKSupportFamilyActivity_nonnegative
        (unitCubeBlockCoupling_nonnegative hfine) 1 6) _
  have hrelative : disagreement <= bound * fineNumerator :=
    hdisagreement pattern
  have hscaled : disagreement * partition <=
      (bound * fineNumerator) * partition :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hrelative hpartition
  have hfactor : denominator ≈ fineNumerator * partition :=
    outwardFineCoarseCompatibleSupportDenominator_eqv_factorized
      fineCoupling pattern
  have hright :
      (bound * fineNumerator) * partition ≈ bound * denominator :=
    Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv bound fineNumerator partition)
      (Q'.mul_eqv_congr_left bound _ _ (Q'.eqv_symm hfactor))
  change disagreement * partition <= bound * denominator
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright)

#print axioms abs_listQSum_filter_sub_le_disagreement
#print axioms compatibleSupportEventNumerator_abs_sub_le_disagreement
#print axioms outwardFineCoarseSupportGeometryCrossDifference_eqv
#print axioms outwardFineCoarseSupportGeometryCrossDifference_abs_le_disagreement
#print axioms abs_le_relative_scaled
#print axioms outwardFineCoarseSupportGeometryBound_of_scaledDisagreement
#print axioms outwardFineCoarseCompatibleSupportDenominator_eqv_factorized
#print axioms outwardFineCoarseSupportGeometryBound_of_disagreement

end YMGap.Continuum.Z4OutwardFineCoarseSupportGasEventDifference
