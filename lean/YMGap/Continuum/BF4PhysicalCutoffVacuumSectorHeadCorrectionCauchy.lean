/-
# Cauchy limit of the moving vacuum-sector head correction

The exact same-sector centering coefficient changes its root coordinate by
the pulled weighted mean divided by the pulled root weight.  This file proves
that signed rational quotient is cutoff-Cauchy.  The proof is quantitative:
the numerator and denominator already have cutoff moduli, every pulled weight
is a probability, and the vacuum root has one fixed positive rational floor
at all sufficiently large cutoffs.

This closes convergence of the moving centering correction for every fixed
base coefficient.  The centered diagonal and reflected quadratic sequences
still require finite polynomial stability using this new quotient modulus;
no cutoff-uniform strict contraction or continuum claim is made here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
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

/-! ## 1. Generic signed quotient stability -/

private theorem divPos_eqv_of_eqv_mul_local
    {value numerator denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hmul : value * denominator ≈ numerator) :
    value ≈ Q'.divPos numerator denominator hdenominator := by
  apply Int.le_antisymm
  · exact Q'.le_divPos_of_mul_le numerator denominator hdenominator
      (Q'.le_of_eqv hmul)
  · exact Q'.divPos_le_of_le_mul numerator denominator hdenominator
      (Q'.ge_of_eqv hmul)

private theorem divPos_sub_divPos_eq_crossDifference_local
    (a b d e : Q')
    (hd : (0 : Q') < d) (he : (0 : Q') < e) :
    Q'.divPos a d hd + -(Q'.divPos b e he) ≈
      Q'.divPos
        (a * e + -(b * d))
        (d * e) (Q'.mul_pos hd he) := by
  apply divPos_eqv_of_eqv_mul_local
  refine Q'.eqv_trans _
    ((Q'.divPos a d hd * d) * e +
      -((Q'.divPos b e he * e) * d)) _ ?_ ?_
  · q_ring
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ e
        (Q'.divPos_mul_eqv a d hd))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ d
          (Q'.divPos_mul_eqv b e he)))

private theorem abs_divPos_le_of_abs_le_mul_local
    {numerator denominator budget : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hcross : Q'.abs numerator ≤ budget * denominator) :
    Q'.abs (Q'.divPos numerator denominator hdenominator) ≤ budget := by
  apply Q'.abs_le
  · apply Q'.le_divPos_of_mul_le
    have hnegCross :
        -(budget * denominator) ≤ -(Q'.abs numerator) :=
      Q'.neg_le_neg hcross
    have hnegAbs : -(Q'.abs numerator) ≤ numerator := by
      have h := Q'.neg_le_neg (Q'.neg_le_abs numerator)
      exact Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.neg_neg_eqv numerator))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_mul_eqv budget denominator))
      (Q'.le_trans' _ _ _ hnegCross hnegAbs)
  · apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self numerator) hcross

private theorem abs_mul_sub_mul_le_local
    {a b c d aBound dBound bError aError : Q'}
    (haBound : (0 : Q') ≤ aBound) (hdBound : (0 : Q') ≤ dBound)
    (ha : Q'.abs a ≤ aBound) (hd : Q'.abs d ≤ dBound)
    (hb : Q'.abs (b + (-d)) ≤ bError)
    (hc : Q'.abs (a + (-c)) ≤ aError) :
    Q'.abs (a * b + -(c * d)) ≤
      aBound * bError + dBound * aError := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr
      (CReal.mul_sub_decomp a b c d))) ?_
  refine Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) ?_
  apply Q'.add_le_add
  · refine Q'.le_trans' _ _ _
      (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le _ _) ?_
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right
        (Q'.abs a) aBound (Q'.abs (b + -d))
        ha (Q'.abs_nonneg _))
      (Q'.mul_le_mul_of_nonneg_left
        (Q'.abs (b + -d)) bError aBound hb haBound)
  · refine Q'.le_trans' _ _ _
      (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le _ _) ?_
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right
        (Q'.abs d) dBound (Q'.abs (a + -c))
        hd (Q'.abs_nonneg _))
      (Q'.mul_le_mul_of_nonneg_left
        (Q'.abs (a + -c)) aError dBound hc hdBound)

/-- Two signed quotients are stable when their numerators and denominators
are close, the numerators are uniformly bounded, the denominators are at
most one in absolute value, and both denominators share a positive floor. -/
theorem signedDivPos_abs_sub_le
    (a b d e error bound floor : Q')
    (hd : (0 : Q') < d) (he : (0 : Q') < e)
    (hfloor : (0 : Q') < floor)
    (hbound0 : (0 : Q') ≤ bound)
    (herror0 : (0 : Q') ≤ error)
    (ha : Q'.abs a ≤ bound)
    (hdOne : Q'.abs d ≤ 1)
    (hnumerator : Q'.abs (a + (-b)) ≤ error)
    (hdenominator : Q'.abs (d + (-e)) ≤ error)
    (hfloorD : floor ≤ d) (hfloorE : floor ≤ e) :
    Q'.abs
        (Q'.divPos a d hd + -(Q'.divPos b e he)) ≤
      Q'.divPos
        ((bound + 1) * error)
        (floor * floor) (Q'.mul_pos hfloor hfloor) := by
  let numeratorBound := (bound + 1) * error
  let floorSquare := floor * floor
  let quotientBound := Q'.divPos numeratorBound floorSquare
    (Q'.mul_pos hfloor hfloor)
  have hone0 : (0 : Q') ≤ (1 : Q') := by decide
  have hboundPlus0 : (0 : Q') ≤ bound + 1 :=
    Q'.zero_le_add _ _ hbound0 hone0
  have hnumeratorBound0 : (0 : Q') ≤ numeratorBound :=
    Q'.mul_nonneg _ _ hboundPlus0 herror0
  have hcross :
      Q'.abs (a * e + -(b * d)) ≤ numeratorBound := by
    have hdenominatorReverse :
        Q'.abs (e + (-d)) ≤ error :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm e d))
        hdenominator
    have hraw :
        Q'.abs (a * e + -(b * d)) ≤
          bound * error + 1 * error :=
      abs_mul_sub_mul_le_local
        (a := a) (b := e) (c := b) (d := d)
        (aBound := bound) (dBound := 1)
        (bError := error) (aError := error)
        hbound0 hone0 ha hdOne hdenominatorReverse hnumerator
    refine Q'.le_trans' _ _ _ hraw ?_
    unfold numeratorBound
    exact Q'.le_of_eqv
      (Q'.eqv_symm (Q'.add_mul_eqv bound 1 error))
  have hfloor0 : (0 : Q') ≤ floor := Q'.le_of_lt hfloor
  have hd0 : (0 : Q') ≤ d := Q'.le_of_lt hd
  have hfloorProduct : floorSquare ≤ d * e := by
    have hfirst : floor * floor ≤ d * floor :=
      Q'.mul_le_mul_of_nonneg_right floor d floor hfloorD hfloor0
    have hsecond : d * floor ≤ d * e :=
      Q'.mul_le_mul_of_nonneg_left floor e d hfloorE hd0
    exact Q'.le_trans' _ _ _ hfirst hsecond
  have hquotientBound0 : (0 : Q') ≤ quotientBound := by
    unfold quotientBound Q'.divPos
    exact Q'.mul_nonneg _ _ hnumeratorBound0
      (Q'.le_of_lt (Q'.recipPos_pos floorSquare
        (Q'.mul_pos hfloor hfloor)))
  have hcrossScaled :
      Q'.abs (a * e + -(b * d)) ≤ quotientBound * (d * e) := by
    refine Q'.le_trans' _ numeratorBound _ hcross ?_
    refine Q'.le_trans' _ (quotientBound * floorSquare) _ ?_ ?_
    · exact Q'.ge_of_eqv
        (Q'.divPos_mul_eqv numeratorBound floorSquare
          (Q'.mul_pos hfloor hfloor))
    · exact Q'.mul_le_mul_of_nonneg_left
        floorSquare (d * e) quotientBound
        hfloorProduct hquotientBound0
  refine Q'.le_trans' _
    (Q'.abs
      (Q'.divPos (a * e + -(b * d))
        (d * e) (Q'.mul_pos hd he))) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (divPos_sub_divPos_eq_crossDifference_local a b d e hd he))
  · exact abs_divPos_le_of_abs_le_mul_local
      (Q'.mul_pos hd he) hcrossScaled

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

/-! ## 2. Bounds on the physical pulled mean and root -/

theorem centralPhysicalFinitePulledWeight_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half index : Nat) :
    (0 : Q') ≤
      centralPhysicalFinitePulledWeight w hw base later half index := by
  unfold centralPhysicalFinitePulledWeight centralPhysicalFiniteWeight
  exact centralPhysicalRowMarginal_nonnegative hw later half _

theorem centralPhysicalFinitePulledWeight_le_one
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hcutoff : base ≤ later)
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half) :
    centralPhysicalFinitePulledWeight w hw base later half index ≤ 1 := by
  unfold centralPhysicalFinitePulledWeight centralPhysicalFiniteWeight
  apply centralPhysicalRowMarginal_le_one_on_carrier
  exact centralPhysicalFiniteStateAt_mem_positive w hw later half
    (centralPhysicalFiniteCutoffIndexMap_lt hcutoff
      (centralPhysicalFiniteVacuumSectorIndex_lt
        w hw base half hindex))

/-- The pulled mean of a fixed base-sector coefficient is uniformly bounded
by its finite coefficient `l1` envelope. -/
theorem centralPhysicalFinitePulledVacuumSectorWeightedMean_abs_le_l1
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (coefficient : Nat → Q') :
    Q'.abs
        (centralPhysicalFinitePulledVacuumSectorWeightedMean
          w hw base later half coefficient) ≤
      coefficientL1
        (centralPhysicalFiniteVacuumSectorIndices w hw base half)
        coefficient := by
  let states := centralPhysicalFiniteVacuumSectorIndices w hw base half
  unfold centralPhysicalFinitePulledVacuumSectorWeightedMean
  refine Q'.le_trans' _ _ _
    (abs_listQSum_le_sum_abs
      (fun index => coefficient index *
        centralPhysicalFinitePulledWeight w hw base later half index)
      states) ?_
  unfold coefficientL1
  apply listQSum_mono
  intro index hindex
  have hweight0 := centralPhysicalFinitePulledWeight_nonnegative
    w hw base later half index
  have hweight1 := centralPhysicalFinitePulledWeight_le_one
    hcutoff hindex
  refine Q'.le_trans' _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le _ _) ?_
  rw [ExpNeg.abs_of_nonneg hweight0]
  refine Q'.le_trans' _ (Q'.abs (coefficient index) * 1) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _ hweight1
      (Q'.abs_nonneg _)
  · exact Q'.le_of_eqv (Q'.mul_one_eqv _)

/-- The fixed uniform positive-row floor lies below the pulled vacuum root at
every cutoff beyond its executable threshold. -/
theorem centralPhysicalUniformPositiveRowFloor_le_pulledWeight_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) {later : Nat}
    (hlater : centralPhysicalUniformRowFloorCutoff w half ≤ later) :
    centralPhysicalUniformPositiveRowFloor
        w (Q'.le_of_lt hw0) half ≤
      centralPhysicalFinitePulledWeight
        w (Q'.le_of_lt hw0) base later half 0 := by
  have hvacuum : zeroEdgeLabelling ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw0)
        (centralPhysicalUniformRowFloorCutoff w half) half := by
    obtain ⟨tail, hstates⟩ := centralPositiveHalfStates_starts_vacuum
      w (Q'.le_of_lt hw0)
        (centralPhysicalUniformRowFloorCutoff w half) half
    rw [hstates]
    exact List.mem_cons_self
  have hfloor := centralPhysicalUniformPositiveRowFloor_le
    hw0 hw1 half hlater hvacuum
  unfold centralPhysicalFinitePulledWeight centralPhysicalFiniteWeight
  rw [centralPhysicalFiniteCutoffIndexMap_zero,
    centralPhysicalFiniteStateAt_zero_eq_vacuum]
  exact hfloor

/-! ## 3. The actual cutoff-Cauchy head-correction limit -/

/-- The rational head correction at one later cutoff. -/
def centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
    {w : Q'} (hw0 : (0 : Q') < w)
    (base half : Nat) (coefficient : Nat → Q') (later : Nat) : Q' :=
  Q'.divPos
      (centralPhysicalFinitePulledVacuumSectorWeightedMean
        w (Q'.le_of_lt hw0) base later half coefficient)
      (centralPhysicalFinitePulledWeight
        w (Q'.le_of_lt hw0) base later half 0)
      (centralPhysicalFinitePulledWeight_zero_pos
        w (Q'.le_of_lt hw0) base later half)

/-- The rational head-correction sequence is cutoff-Cauchy.  Naming this
modulus separately keeps the final Bishop-real constructor transparent to the
elaborator and makes the quantitative estimate reusable by centered forms. -/
theorem centralPhysicalFinitePulledVacuumSectorHeadCorrection_cauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') :
    ∀ epsilon : Q', (0 : Q') < epsilon →
      ∃ cutoff : Nat, ∀ first second : Nat,
        cutoff ≤ first → cutoff ≤ second →
          centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
              hw0 base half coefficient first ≤
            centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
                hw0 base half coefficient second + epsilon ∧
          centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
              hw0 base half coefficient second ≤
            centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
                hw0 base half coefficient first + epsilon := by
    intro epsilon hepsilon
    unfold centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
    let states := centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half
    let bound := coefficientL1 states coefficient
    have hbound0 : (0 : Q') ≤ bound :=
      coefficientL1_nonnegative_local states coefficient
    let floor := centralPhysicalUniformPositiveRowFloor
      w (Q'.le_of_lt hw0) half
    have hfloor : (0 : Q') < floor :=
      centralPhysicalUniformPositiveRowFloor_pos
        w (Q'.le_of_lt hw0) half
    let floorSquare := floor * floor
    have hfloorSquare : (0 : Q') < floorSquare :=
      Q'.mul_pos hfloor hfloor
    let scale := (bound + 1) + 1
    have hboundPlus0 : (0 : Q') ≤ bound + 1 :=
      Q'.zero_le_add _ _ hbound0 (by decide)
    have hscale : (0 : Q') < scale := positive_scale hboundPlus0
    let tolerance := Q'.divPos (epsilon * floorSquare) scale hscale
    have htolerance : (0 : Q') < tolerance :=
      Q'.divPos_pos _ _ hscale (Q'.mul_pos hepsilon hfloorSquare)
    let meanLimit :=
      centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
        hw0 hw1 base half coefficient
    let rootLimit :=
      centralPhysicalFinitePulledWeightCutoffLimit
        hw0 hw1 base half 0
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w (Q'.le_of_lt hw0) base half
          (zero_mem_centralPhysicalFiniteVacuumSectorIndices
            w (Q'.le_of_lt hw0) base half))
    obtain ⟨meanCutoff, hmean⟩ := meanLimit.cauchy tolerance htolerance
    obtain ⟨rootCutoff, hroot⟩ := rootLimit.cauchy tolerance htolerance
    refine ⟨max
      (max base (centralPhysicalUniformRowFloorCutoff w half))
      (max meanCutoff rootCutoff), ?_⟩
    intro first second hfirst hsecond
    have hbaseFirst : base ≤ first :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_max_left _ _)) hfirst
    have hbaseSecond : base ≤ second :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_max_left _ _)) hsecond
    have hfloorFirst :
        centralPhysicalUniformRowFloorCutoff w half ≤ first :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_max_left _ _)) hfirst
    have hfloorSecond :
        centralPhysicalUniformRowFloorCutoff w half ≤ second :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_max_left _ _)) hsecond
    have hmeanFirst : meanCutoff ≤ first :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_max_right _ _)) hfirst
    have hmeanSecond : meanCutoff ≤ second :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_max_right _ _)) hsecond
    have hrootFirst : rootCutoff ≤ first :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_max_right _ _)) hfirst
    have hrootSecond : rootCutoff ≤ second :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_max_right _ _)) hsecond
    have hmeanAbs :
        Q'.abs
          (centralPhysicalFinitePulledVacuumSectorWeightedMean
              w (Q'.le_of_lt hw0) base first half coefficient +
            -centralPhysicalFinitePulledVacuumSectorWeightedMean
              w (Q'.le_of_lt hw0) base second half coefficient) ≤
          tolerance :=
      CReal.abs_sub_le_of_bounds
        (hmean first second hmeanFirst hmeanSecond).1
        (hmean first second hmeanFirst hmeanSecond).2
    have hrootAbs :
        Q'.abs
          (centralPhysicalFinitePulledWeight
              w (Q'.le_of_lt hw0) base first half 0 +
            -centralPhysicalFinitePulledWeight
              w (Q'.le_of_lt hw0) base second half 0) ≤
          tolerance :=
      CReal.abs_sub_le_of_bounds
        (hroot first second hrootFirst hrootSecond).1
        (hroot first second hrootFirst hrootSecond).2
    have hmeanBound :=
      centralPhysicalFinitePulledVacuumSectorWeightedMean_abs_le_l1
        (w := w) (hw := Q'.le_of_lt hw0)
        (base := base) (later := first) (half := half)
        hbaseFirst coefficient
    have hroot0 := centralPhysicalFinitePulledWeight_nonnegative
      w (Q'.le_of_lt hw0) base first half 0
    have hroot1 := centralPhysicalFinitePulledWeight_le_one
      hbaseFirst
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) base half)
    have hrootAbsOne : Q'.abs
        (centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base first half 0) ≤ 1 := by
      rw [ExpNeg.abs_of_nonneg hroot0]
      exact hroot1
    have hfloorPulledFirst :=
      centralPhysicalUniformPositiveRowFloor_le_pulledWeight_zero
        hw0 hw1 base half hfloorFirst
    have hfloorPulledSecond :=
      centralPhysicalUniformPositiveRowFloor_le_pulledWeight_zero
        hw0 hw1 base half hfloorSecond
    have hratio := signedDivPos_abs_sub_le
      (centralPhysicalFinitePulledVacuumSectorWeightedMean
        w (Q'.le_of_lt hw0) base first half coefficient)
      (centralPhysicalFinitePulledVacuumSectorWeightedMean
        w (Q'.le_of_lt hw0) base second half coefficient)
      (centralPhysicalFinitePulledWeight
        w (Q'.le_of_lt hw0) base first half 0)
      (centralPhysicalFinitePulledWeight
        w (Q'.le_of_lt hw0) base second half 0)
      tolerance bound floor
      (centralPhysicalFinitePulledWeight_zero_pos
        w (Q'.le_of_lt hw0) base first half)
      (centralPhysicalFinitePulledWeight_zero_pos
        w (Q'.le_of_lt hw0) base second half)
      hfloor hbound0 (Q'.le_of_lt htolerance)
      hmeanBound hrootAbsOne hmeanAbs hrootAbs
      hfloorPulledFirst hfloorPulledSecond
    have hscaled : (bound + 1) * tolerance ≤ epsilon * floorSquare := by
      have hfactor : bound + 1 ≤ scale := by
        exact Q'.add_le_self_of_nonneg _ _ (by decide)
      have htol0 : (0 : Q') ≤ tolerance := Q'.le_of_lt htolerance
      refine Q'.le_trans' _ (scale * tolerance) _ ?_ ?_
      · exact Q'.mul_le_mul_of_nonneg_right _ _ _ hfactor htol0
      · refine Q'.le_trans' _ (tolerance * scale) _ ?_ ?_
        · exact Q'.le_of_eqv (Q'.mul_comm_eqv _ _)
        · exact Q'.le_of_eqv
            (Q'.divPos_mul_eqv
              (epsilon * floorSquare) scale hscale)
    have hquotient :
        Q'.divPos ((bound + 1) * tolerance)
            floorSquare hfloorSquare ≤ epsilon := by
      apply Q'.divPos_le_of_le_mul
      exact hscaled
    exact two_sided_add_of_abs_sub_le_local
      (Q'.le_trans' _ _ _ hratio hquotient)

/-- The positive root correction `pulledMean / pulledRootWeight` is a Bishop
real.  The centering coefficient uses its negative. -/
def centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') : CReal where
  approx later :=
    centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
      hw0 base half coefficient later
  cauchy :=
    centralPhysicalFinitePulledVacuumSectorHeadCorrection_cauchy
      hw0 hw1 base half coefficient

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy.signedDivPos_abs_sub_le
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy.centralPhysicalFinitePulledVacuumSectorWeightedMean_abs_le_l1
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy.centralPhysicalUniformPositiveRowFloor_le_pulledWeight_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy.centralPhysicalFinitePulledVacuumSectorHeadCorrection_cauchy
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy.centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
