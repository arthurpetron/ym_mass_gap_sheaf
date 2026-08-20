/-
# Relative rank-one producer for boundary-message quarter contraction

The terminal-independent refresh theorem consumes a raw cross-ratio witness.
This file gives a smaller analytic producer.  If a finite positive physical
kernel is within relative error `1/16` of positive source and target profiles,
then its cross-ratio spread is at most `17/15`.  Since

  `(17/15)^2 = 289/225 < 4/3`,

the terminal-normalized boundary-message kernel contracts exact finite `L1`
distance by at most one quarter.

This is a proof-carrying numerical interface.  Exact enumeration or interval
arithmetic in Rust, C, or another external program may propose the profile and
entrywise bounds, but Lean checks the literal rational inequalities and this
certificate-to-contraction theorem.  Statistical sampling alone does not
inhabit the witness.

The implementation uses no forbidden proof shortcuts, choice principles, or
opaque declarations.
-/

import YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh
import YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation

namespace YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation
open YMGap.Continuum.RationalCrossRatioDiameter

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

/-- Cancellation-free rational-semantic polynomial normalization. -/
local macro "ac_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Exact rational profile window -/

/-- The relative entry tolerance used by the quarter-rate producer. -/
def relativeRankOneTolerance : Q' := Q'.mkPos 1 16 (by decide)

/-- The exact lower factor `1 - 1/16`. -/
def relativeRankOneLower : Q' := Q'.mkPos 15 16 (by decide)

/-- The exact upper factor `1 + 1/16`. -/
def relativeRankOneUpper : Q' := Q'.mkPos 17 16 (by decide)

/-- The upper/lower profile ratio `(17/16)/(15/16)`. -/
def relativeRankOneSpread : Q' := Q'.mkPos 17 15 (by decide)

theorem relativeRankOneSpread_square_le_fourThirds :
    relativeRankOneSpread * relativeRankOneSpread ≤
      fourThirdsSpreadSquare := by
  decide

/-- A positive-denominator quotient is strictly below one when its numerator
is strictly smaller than its denominator. -/
private theorem divPos_lt_one_of_lt
    (numerator denominator : Q')
    (denominator_pos : (0 : Q') < denominator)
    (numerator_lt : numerator < denominator) :
    Q'.divPos numerator denominator denominator_pos < (1 : Q') := by
  unfold Q'.divPos
  have hreciprocal :
      (0 : Q') < Q'.recipPos denominator denominator_pos :=
    Q'.recipPos_pos denominator denominator_pos
  have hscaled :
      Q'.recipPos denominator denominator_pos * numerator <
        Q'.recipPos denominator denominator_pos * denominator :=
    Q'.mul_lt_mul_of_pos_left hreciprocal numerator_lt
  have hleft :
      numerator * Q'.recipPos denominator denominator_pos ≈
        Q'.recipPos denominator denominator_pos * numerator :=
    Q'.mul_comm_eqv _ _
  have hright :
      Q'.recipPos denominator denominator_pos * denominator ≈
        (1 : Q') :=
    Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv _ _)
      (Q'.mul_recipPos_eqv denominator denominator_pos)
  exact ContinuumClosureProgram.q'_lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv hleft) hscaled)
    (Q'.le_of_eqv hright)

/-! ## 2. One finite proof-carrying profile enclosure -/

/-- Literal entrywise witness that a finite physical raw kernel is uniformly
close, relative to positive source/target profiles, to rank one. -/
structure FiniteRelativeRankOneQuarterWitness
    {Source Target : Type}
    (physical : Source → Target → Q')
    (sources : List Source) (targets : List Target) : Type where
  sourceProfile : Source → Q'
  targetProfile : Target → Q'
  sourceProfile_pos :
    ∀ source, source ∈ sources →
      (0 : Q') < sourceProfile source
  targetProfile_pos :
    ∀ target, target ∈ targets →
      (0 : Q') < targetProfile target
  relative_error :
    ∀ source, source ∈ sources →
      ∀ target, target ∈ targets →
        Q'.abs
            (physical source target +
              -(sourceProfile source * targetProfile target)) ≤
          relativeRankOneTolerance *
            (sourceProfile source * targetProfile target)

namespace FiniteRelativeRankOneQuarterWitness

/-- The positive rank-one comparison kernel. -/
def ideal
    {Source Target : Type}
    {physical : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (witness :
      FiniteRelativeRankOneQuarterWitness physical sources targets)
    (source : Source) (target : Target) : Q' :=
  witness.sourceProfile source * witness.targetProfile target

theorem ideal_pos
    {Source Target : Type}
    {physical : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (witness :
      FiniteRelativeRankOneQuarterWitness physical sources targets)
    (source : Source) (hsource : source ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    (0 : Q') < witness.ideal source target :=
  Q'.mul_pos
    (witness.sourceProfile_pos source hsource)
    (witness.targetProfile_pos target htarget)

/-- The relative error window makes every selected physical entry strictly
positive; strict positivity is derived, not separately trusted. -/
theorem physical_pos
    {Source Target : Type}
    {physical : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (witness :
      FiniteRelativeRankOneQuarterWitness physical sources targets)
    (source : Source) (hsource : source ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    (0 : Q') < physical source target := by
  have henvelope :=
    multiplicative_envelope_of_relative_abs_error
      (physical source target)
      (witness.ideal source target)
      relativeRankOneTolerance
      (witness.relative_error source hsource target htarget)
  have hlower :
      (0 : Q') <
        ((1 : Q') + -relativeRankOneTolerance) *
          witness.ideal source target :=
    Q'.mul_pos (by decide)
      (witness.ideal_pos source hsource target htarget)
  exact Q'.pos_of_lt_of_le hlower henvelope.1

/-- The relative rank-one witness constructs the exact finite cross-ratio
certificate consumed by the boundary-message refresh theorem. -/
def toCrossRatioCertificate
    {Source Target : Type}
    {physical : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (witness :
      FiniteRelativeRankOneQuarterWitness physical sources targets) :
    FiniteCrossRatioDiameterCertificate physical sources targets where
  spread := relativeRankOneSpread
  one_le_spread := by decide
  strictlyPositive := witness.physical_pos
  crossRatioBound := by
    have hbound :=
      crossRatio_of_relative_kernel_envelope
        physical witness.ideal sources targets
        (1 : Q')
        ((1 : Q') + -relativeRankOneTolerance)
        ((1 : Q') + relativeRankOneTolerance)
        relativeRankOneSpread
        (fun source hsource target htarget =>
          Q'.le_of_lt
            (witness.physical_pos source hsource target htarget))
        (fun source hsource target htarget =>
          Q'.le_of_lt
            (witness.ideal_pos source hsource target htarget))
        (by decide) (by decide) (by decide) (by decide)
        (by decide)
        (fun source hsource target htarget =>
          (multiplicative_envelope_of_relative_abs_error
            (physical source target)
            (witness.ideal source target)
            relativeRankOneTolerance
            (witness.relative_error
              source hsource target htarget)).1)
        (fun source hsource target htarget =>
          (multiplicative_envelope_of_relative_abs_error
            (physical source target)
            (witness.ideal source target)
            relativeRankOneTolerance
            (witness.relative_error
              source hsource target htarget)).2)
        (by
          intro first hfirst second hsecond
            left hleft right hright
          exact Q'.le_of_eqv (by
            unfold ideal
            ac_qeqv))
    intro first hfirst second hsecond left hleft right hright
    exact Q'.le_trans' _ _ _
      (hbound first hfirst second hsecond left hleft right hright)
      (Q'.le_of_eqv (by ac_qeqv))

theorem commonMass_lt_one
    {Source Target : Type}
    {physical : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (witness :
      FiniteRelativeRankOneQuarterWitness physical sources targets) :
    commonMass witness.toCrossRatioCertificate < (1 : Q') := by
  unfold commonMass
  apply divPos_lt_one_of_lt
  change (1 : Q') < relativeRankOneSpread * relativeRankOneSpread
  decide

end FiniteRelativeRankOneQuarterWitness

/-! ## 3. Uniform all-regulator producer -/

/-- Uniform relative rank-one witness for the literal regulator-indexed raw
physical kernels.  The only analytic field is the exact entrywise enclosure;
the cross-ratio and terminal-message contraction fields are derived. -/
structure UniformRelativeRankOneQuarterWitness
    (Index : Type)
    (Source Target : Index → Type)
    (physical : ∀ index, Source index → Target index → Q')
    (sources : ∀ index, List (Source index))
    (targets : ∀ index, List (Target index)) : Type where
  sourceProfile : ∀ index, Source index → Q'
  targetProfile : ∀ index, Target index → Q'
  sourceProfile_pos :
    ∀ index source, source ∈ sources index →
      (0 : Q') < sourceProfile index source
  targetProfile_pos :
    ∀ index target, target ∈ targets index →
      (0 : Q') < targetProfile index target
  relative_error :
    ∀ index source, source ∈ sources index →
      ∀ target, target ∈ targets index →
        Q'.abs
            (physical index source target +
              -(sourceProfile index source *
                targetProfile index target)) ≤
          relativeRankOneTolerance *
            (sourceProfile index source *
              targetProfile index target)
  reference : ∀ index, Source index
  reference_mem : ∀ index, reference index ∈ sources index

namespace UniformRelativeRankOneQuarterWitness

def atIndex
    {Index : Type}
    {Source Target : Index → Type}
    {physical : ∀ index, Source index → Target index → Q'}
    {sources : ∀ index, List (Source index)}
    {targets : ∀ index, List (Target index)}
    (witness :
      UniformRelativeRankOneQuarterWitness
        Index Source Target physical sources targets)
    (index : Index) :
    FiniteRelativeRankOneQuarterWitness
      (physical index) (sources index) (targets index) where
  sourceProfile := witness.sourceProfile index
  targetProfile := witness.targetProfile index
  sourceProfile_pos := witness.sourceProfile_pos index
  targetProfile_pos := witness.targetProfile_pos index
  relative_error := witness.relative_error index

/-- The uniform relative enclosure inhabits the complete proof-carrying
boundary-message quarter certificate. -/
def toUniformBoundaryMessageQuarterCertificate
    {Index : Type}
    {Source Target : Index → Type}
    {physical : ∀ index, Source index → Target index → Q'}
    {sources : ∀ index, List (Source index)}
    {targets : ∀ index, List (Target index)}
    (witness :
      UniformRelativeRankOneQuarterWitness
        Index Source Target physical sources targets) :
    UniformBoundaryMessageQuarterCertificate
      Index Source Target physical sources targets where
  crossRatio :=
    { spread := relativeRankOneSpread
      one_le_spread := by decide
      strictlyPositive := fun index =>
        (witness.atIndex index).physical_pos
      crossRatioBound := fun index =>
        (witness.atIndex index).toCrossRatioCertificate.crossRatioBound }
  spreadSquare_le := relativeRankOneSpread_square_le_fourThirds
  commonMass_lt_one := by
    intro index
    unfold commonMass
    apply divPos_lt_one_of_lt
    change (1 : Q') < relativeRankOneSpread * relativeRankOneSpread
    decide
  reference := witness.reference
  reference_mem := witness.reference_mem

end UniformRelativeRankOneQuarterWitness

end YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter

#print axioms YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter.FiniteRelativeRankOneQuarterWitness.physical_pos
#print axioms YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter.FiniteRelativeRankOneQuarterWitness.toCrossRatioCertificate
#print axioms YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter.FiniteRelativeRankOneQuarterWitness.commonMass_lt_one
#print axioms YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter.UniformRelativeRankOneQuarterWitness.toUniformBoundaryMessageQuarterCertificate
