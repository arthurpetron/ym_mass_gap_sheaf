/-
# A positive finite kernel for the coupling-shifted unit-cube observable

At finite cutoff and volume the coarse six-face occurrence and the refined
24-face occurrence are honest Bernoulli observables of two different exact
physical spin-foam laws.  This module packages two constructive couplings of
those observable laws.

* `activityMatchedUnitCubeResamplingKernel` is a genuine positive normalized
  Markov kernel on `Bool`.  It sends the shifted coarse Bernoulli law exactly
  to the fine refined Bernoulli law.  Its rows agree: this is independent
  resampling from the target physical cylinder law.
* `activityMatchedUnitCubeMaximalJoint` is the diagonal-maximizing two-point
  joint law.  Its two marginals are exactly the shifted coarse and fine
  refined laws, and its off-diagonal mass is exactly the already-defined
  activity-matched block defect.

All entries are exact rationals derived from the finite physical partition
and event numerator.  No defect estimate is assumed.

The locality claim is deliberately limited to *observable/cylinder locality*:
the two Bernoulli parameters use the fixed unit-cube cylinder roots.  The
resampling kernel is source-independent and therefore is not a spatially
local configuration-level block-spin map.  Constructing such a map remains
the typed RG residual; the present result shows that positivity and
normalization themselves are not the obstruction at the finite observable
level.
-/

import YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw

namespace YMGap.Continuum.Z4FiniteObservableBlockKernel

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4DyadicUnitCubeBlockCylinderIntertwining
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

private theorem difference_add_right_eqv (a b : Q') :
    (a + -b) + b ≈ a := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_comm_eqv (a + -b) b)
    (Q'.eqv_symm (Q'.add_sub_cancel_eqv a b))

private theorem chained_difference_eqv (a b c : Q') :
    (a + -b) + (b + -c) ≈ a + -c := by
  have hsecond : b + -c ≈ -c + b :=
    Q'.add_comm_eqv b (-c)
  have hfirst :
      (a + -b) + (b + -c) ≈
        (a + -b) + (-c + b) :=
    Q'.add_eqv_congr_left (a + -b) _ _ hsecond
  have hswap :
      (a + -b) + (-c + b) ≈
        (a + -c) + (-b + b) :=
    Q'.add_swap_inner a (-b) (-c) b
  have hcancel :
      (a + -c) + (-b + b) ≈ (a + -c) + (0 : Q') :=
    Q'.add_eqv_congr_left (a + -c) _ _
      (Q'.neg_add_self_eqv b)
  rw [Q'.add_zero'] at hcancel
  exact Q'.eqv_trans _ _ _ hfirst
    (Q'.eqv_trans _ _ _ hswap hcancel)

/-! ## 1. Constructive two-point laws and kernels -/

/-- The Bernoulli mass with true-parameter `p`, in additive rational form. -/
def bernoulliMass (p : Q') : Bool → Q'
  | false => (1 : Q') + -p
  | true => p

/-- A finite positive normalized law on the two-point space. -/
structure PositiveBoolLaw (mass : Bool → Q') : Prop where
  nonnegative : ∀ outcome, (0 : Q') ≤ mass outcome
  normalized : mass false + mass true ≈ (1 : Q')

theorem bernoulliMass_nonnegative
    {p : Q'} (hp0 : (0 : Q') ≤ p) (hp1 : p ≤ (1 : Q'))
    (outcome : Bool) :
    (0 : Q') ≤ bernoulliMass p outcome := by
  cases outcome
  · exact Q'.sub_nonneg_of_le hp1
  · exact hp0

theorem bernoulliMass_normalized (p : Q') :
    bernoulliMass p false + bernoulliMass p true ≈ (1 : Q') := by
  unfold bernoulliMass
  exact Q'.eqv_trans _ _ _
    (Q'.add_comm_eqv ((1 : Q') + -p) p)
    (Q'.eqv_symm (Q'.add_sub_cancel_eqv 1 p))

def bernoulliPositiveBoolLaw
    (p : Q') (hp0 : (0 : Q') ≤ p) (hp1 : p ≤ (1 : Q')) :
    PositiveBoolLaw (bernoulliMass p) where
  nonnegative := bernoulliMass_nonnegative hp0 hp1
  normalized := bernoulliMass_normalized p

/-- A positive row-stochastic kernel on the two-point space. -/
structure PositiveBoolKernel (kernel : Bool → Bool → Q') : Prop where
  nonnegative : ∀ source target, (0 : Q') ≤ kernel source target
  row_normalized : ∀ source,
    kernel source false + kernel source true ≈ (1 : Q')

/-- Explicit pushforward of a two-point law through a two-point kernel. -/
def boolPushforward
    (sourceMass : Bool → Q') (kernel : Bool → Bool → Q')
    (target : Bool) : Q' :=
  sourceMass false * kernel false target +
    sourceMass true * kernel true target

/-- Independent resampling from the Bernoulli target law. -/
def bernoulliResamplingKernel (targetParameter : Q') : Bool → Bool → Q' :=
  fun _ target => bernoulliMass targetParameter target

theorem bernoulliResamplingKernel_nonnegative
    {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q'))
    (source target : Bool) :
    (0 : Q') ≤ bernoulliResamplingKernel q source target :=
  bernoulliMass_nonnegative hq0 hq1 target

theorem bernoulliResamplingKernel_row_normalized
    (q : Q') (source : Bool) :
    bernoulliResamplingKernel q source false +
        bernoulliResamplingKernel q source true ≈ (1 : Q') :=
  bernoulliMass_normalized q

def bernoulliPositiveResamplingKernel
    (q : Q') (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q')) :
    PositiveBoolKernel (bernoulliResamplingKernel q) where
  nonnegative := bernoulliResamplingKernel_nonnegative hq0 hq1
  row_normalized := bernoulliResamplingKernel_row_normalized q

/-- Independent resampling pushes every normalized Bernoulli source exactly
to the requested Bernoulli target. -/
theorem bernoulliResamplingKernel_pushforward
    (p q : Q') (target : Bool) :
    boolPushforward (bernoulliMass p)
        (bernoulliResamplingKernel q) target ≈
      bernoulliMass q target := by
  let targetMass := bernoulliMass q target
  have hfactor :
      bernoulliMass p false * targetMass +
          bernoulliMass p true * targetMass ≈
        (bernoulliMass p false + bernoulliMass p true) * targetMass :=
    Q'.eqv_symm
      (Q'.add_mul_eqv
        (bernoulliMass p false) (bernoulliMass p true) targetMass)
  have hnormalize :
      (bernoulliMass p false + bernoulliMass p true) * targetMass ≈
        (1 : Q') * targetMass :=
    Q'.mul_eqv_congr_right _ _ targetMass
      (bernoulliMass_normalized p)
  unfold boolPushforward bernoulliResamplingKernel
  exact Q'.eqv_trans _ _ _ hfactor
    (Q'.eqv_trans _ _ _ hnormalize
      (Q'.one_mul_eqv (bernoulliMass q target)))

/-! ## 2. A diagonal two-point joint law -/

/-- The canonical diagonal coupling of Bernoulli parameters `p` and `q`.
If `p ≥ q`, the only off-diagonal mass is `p-q`; otherwise it is `q-p`. -/
def bernoulliMaximalJoint (p q : Q') : Bool → Bool → Q'
  | false, false =>
      if (0 : Q') ≤ p + -q then (1 : Q') + -p else (1 : Q') + -q
  | false, true =>
      if (0 : Q') ≤ p + -q then (0 : Q') else q + -p
  | true, false =>
      if (0 : Q') ≤ p + -q then p + -q else (0 : Q')
  | true, true =>
      if (0 : Q') ≤ p + -q then q else p

/-- The off-diagonal (disagreement) mass of a two-point joint law. -/
def boolJointMismatch (joint : Bool → Bool → Q') : Q' :=
  joint false true + joint true false

private theorem reversed_difference_eqv_neg (p q : Q') :
    q + -p ≈ -(p + -q) := by
  have hneg : -(p + -q) ≈ -p + -(-q) :=
    Q'.neg_add_eqv p (-q)
  have hcancel : -p + -(-q) ≈ -p + q :=
    Q'.add_eqv_congr_left (-p) _ _ (Q'.neg_neg_eqv q)
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _ hneg
      (Q'.eqv_trans _ _ _ hcancel
        (Q'.add_comm_eqv (-p) q)))

private theorem reversed_difference_nonnegative
    {p q : Q'} (h : ¬ (0 : Q') ≤ p + -q) :
    (0 : Q') ≤ q + -p := by
  exact Q'.le_trans' _ _ _
    (Q'.neg_nonneg_of_not_nonneg h)
    (Q'.le_of_eqv (Q'.eqv_symm
      (reversed_difference_eqv_neg p q)))

theorem bernoulliMaximalJoint_nonnegative
    {p q : Q'} (hp0 : (0 : Q') ≤ p) (hp1 : p ≤ (1 : Q'))
    (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q'))
    (source target : Bool) :
    (0 : Q') ≤ bernoulliMaximalJoint p q source target := by
  by_cases h : (0 : Q') ≤ p + -q
  · cases source with
    | false =>
        cases target with
        | false =>
            simp only [bernoulliMaximalJoint]
            rw [if_pos h]
            exact Q'.sub_nonneg_of_le hp1
        | true =>
            simp only [bernoulliMaximalJoint]
            rw [if_pos h]
            exact Q'.le_refl' 0
    | true =>
        cases target with
        | false =>
            simp only [bernoulliMaximalJoint]
            rw [if_pos h]
            exact h
        | true =>
            simp only [bernoulliMaximalJoint]
            rw [if_pos h]
            exact hq0
  · cases source with
    | false =>
        cases target with
        | false =>
            simp only [bernoulliMaximalJoint]
            rw [if_neg h]
            exact Q'.sub_nonneg_of_le hq1
        | true =>
            simp only [bernoulliMaximalJoint]
            rw [if_neg h]
            exact reversed_difference_nonnegative h
    | true =>
        cases target with
        | false =>
            simp only [bernoulliMaximalJoint]
            rw [if_neg h]
            exact Q'.le_refl' 0
        | true =>
            simp only [bernoulliMaximalJoint]
            rw [if_neg h]
            exact hp0

theorem bernoulliMaximalJoint_sourceMarginal
    (p q : Q') (source : Bool) :
    bernoulliMaximalJoint p q source false +
        bernoulliMaximalJoint p q source true ≈
      bernoulliMass p source := by
  by_cases h : (0 : Q') ≤ p + -q
  · cases source with
    | false =>
        simp only [bernoulliMaximalJoint, bernoulliMass]
        rw [if_pos h, if_pos h, Q'.add_zero']
        exact Q'.eqv_refl _
    | true =>
        simp only [bernoulliMaximalJoint, bernoulliMass]
        rw [if_pos h, if_pos h]
        exact difference_add_right_eqv p q
  · cases source with
    | false =>
        simp only [bernoulliMaximalJoint, bernoulliMass]
        rw [if_neg h, if_neg h]
        exact chained_difference_eqv 1 q p
    | true =>
        simp only [bernoulliMaximalJoint, bernoulliMass]
        rw [if_neg h, if_neg h, Q'.zero_add']
        exact Q'.eqv_refl _

theorem bernoulliMaximalJoint_targetMarginal
    (p q : Q') (target : Bool) :
    bernoulliMaximalJoint p q false target +
        bernoulliMaximalJoint p q true target ≈
      bernoulliMass q target := by
  by_cases h : (0 : Q') ≤ p + -q
  · cases target with
    | false =>
        simp only [bernoulliMaximalJoint, bernoulliMass]
        rw [if_pos h, if_pos h]
        exact chained_difference_eqv 1 p q
    | true =>
        simp only [bernoulliMaximalJoint, bernoulliMass]
        rw [if_pos h, if_pos h, Q'.zero_add']
        exact Q'.eqv_refl _
  · cases target with
    | false =>
        simp only [bernoulliMaximalJoint, bernoulliMass]
        rw [if_neg h, if_neg h, Q'.add_zero']
        exact Q'.eqv_refl _
    | true =>
        simp only [bernoulliMaximalJoint, bernoulliMass]
        rw [if_neg h, if_neg h]
        exact difference_add_right_eqv q p

theorem bernoulliMaximalJoint_normalized (p q : Q') :
    (bernoulliMaximalJoint p q false false +
        bernoulliMaximalJoint p q false true) +
      (bernoulliMaximalJoint p q true false +
        bernoulliMaximalJoint p q true true) ≈ (1 : Q') := by
  have hfalse := bernoulliMaximalJoint_sourceMarginal p q false
  have htrue := bernoulliMaximalJoint_sourceMarginal p q true
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hfalse htrue)
    (bernoulliMass_normalized p)

/-- The diagonal joint law pays exactly the absolute Bernoulli discrepancy
and no additional off-diagonal mass. -/
theorem bernoulliMaximalJoint_mismatch
    (p q : Q') :
    boolJointMismatch (bernoulliMaximalJoint p q) ≈
      Q'.abs (p + -q) := by
  unfold boolJointMismatch
  by_cases h : (0 : Q') ≤ p + -q
  · simp only [bernoulliMaximalJoint]
    rw [if_pos h, if_pos h, Q'.zero_add']
    unfold Q'.abs
    rw [if_pos h]
    exact Q'.eqv_refl _
  · simp only [bernoulliMaximalJoint]
    rw [if_neg h, if_neg h, Q'.add_zero']
    unfold Q'.abs
    rw [if_neg h]
    exact reversed_difference_eqv_neg p q

/-- A positive normalized joint coupling with specified two-point marginals. -/
structure PositiveBoolCoupling
    (sourceMass targetMass : Bool → Q')
    (joint : Bool → Bool → Q') : Prop where
  nonnegative : ∀ source target, (0 : Q') ≤ joint source target
  source_marginal : ∀ source,
    joint source false + joint source true ≈ sourceMass source
  target_marginal : ∀ target,
    joint false target + joint true target ≈ targetMass target
  normalized :
    (joint false false + joint false true) +
      (joint true false + joint true true) ≈ (1 : Q')

def bernoulliPositiveMaximalCoupling
    (p q : Q')
    (hp0 : (0 : Q') ≤ p) (hp1 : p ≤ (1 : Q'))
    (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q')) :
    PositiveBoolCoupling (bernoulliMass p) (bernoulliMass q)
      (bernoulliMaximalJoint p q) where
  nonnegative := bernoulliMaximalJoint_nonnegative hp0 hp1 hq0 hq1
  source_marginal := bernoulliMaximalJoint_sourceMarginal p q
  target_marginal := bernoulliMaximalJoint_targetMarginal p q
  normalized := bernoulliMaximalJoint_normalized p q

/-! ## 3. The exact activity-matched finite block kernel -/

def activityMatchedCoarseParameter
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) : Q' :=
  couplingKUnitCubeBlockCoarseProbability
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine) cutoff volume

def activityMatchedRefinedParameter
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) : Q' :=
  couplingKUnitCubeBlockRefinedProbability
    fineCoupling hfine cutoff volume

theorem activityMatchedCoarseParameter_nonnegative
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    (0 : Q') ≤ activityMatchedCoarseParameter
      fineCoupling hfine cutoff volume :=
  couplingKUnitCubeBlockCoarseProbability_nonnegative _ _ _ _

theorem activityMatchedCoarseParameter_le_one
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    activityMatchedCoarseParameter fineCoupling hfine cutoff volume ≤
      (1 : Q') :=
  couplingKUnitCubeBlockCoarseProbability_le_one _ _ _ _

theorem activityMatchedRefinedParameter_nonnegative
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    (0 : Q') ≤ activityMatchedRefinedParameter
      fineCoupling hfine cutoff volume :=
  couplingKUnitCubeBlockRefinedProbability_nonnegative _ _ _ _

theorem activityMatchedRefinedParameter_le_one
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    activityMatchedRefinedParameter fineCoupling hfine cutoff volume ≤
      (1 : Q') :=
  couplingKUnitCubeBlockRefinedProbability_le_one _ _ _ _

def activityMatchedCoarseObservableLaw
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) : Bool → Q' :=
  bernoulliMass
    (activityMatchedCoarseParameter fineCoupling hfine cutoff volume)

def activityMatchedRefinedObservableLaw
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) : Bool → Q' :=
  bernoulliMass
    (activityMatchedRefinedParameter fineCoupling hfine cutoff volume)

/-- A positive normalized finite Markov kernel taking the shifted coarse
observable law to the fine refined observable law. -/
def activityMatchedUnitCubeResamplingKernel
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) : Bool → Bool → Q' :=
  bernoulliResamplingKernel
    (activityMatchedRefinedParameter fineCoupling hfine cutoff volume)

def activityMatchedUnitCubeResamplingKernel_positive
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    PositiveBoolKernel
      (activityMatchedUnitCubeResamplingKernel
        fineCoupling hfine cutoff volume) :=
  bernoulliPositiveResamplingKernel _
    (activityMatchedRefinedParameter_nonnegative
      fineCoupling hfine cutoff volume)
    (activityMatchedRefinedParameter_le_one
      fineCoupling hfine cutoff volume)

theorem activityMatchedUnitCubeResamplingKernel_pushforward
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (target : Bool) :
    boolPushforward
        (activityMatchedCoarseObservableLaw
          fineCoupling hfine cutoff volume)
        (activityMatchedUnitCubeResamplingKernel
          fineCoupling hfine cutoff volume) target ≈
      activityMatchedRefinedObservableLaw
        fineCoupling hfine cutoff volume target := by
  unfold activityMatchedCoarseObservableLaw
    activityMatchedRefinedObservableLaw
    activityMatchedUnitCubeResamplingKernel
  exact bernoulliResamplingKernel_pushforward _ _ target

/-- Observable-level locality fence: every row is the same exact target
cylinder law.  Thus this is normalized and positive, but it deliberately
contains no configuration-level dependence on the source. -/
theorem activityMatchedUnitCubeResamplingKernel_source_independent
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (first second target : Bool) :
    activityMatchedUnitCubeResamplingKernel
        fineCoupling hfine cutoff volume first target =
      activityMatchedUnitCubeResamplingKernel
        fineCoupling hfine cutoff volume second target := rfl

/-- The true entry is literally the normalized refined physical cylinder
event numerator over the physical finite partition. -/
theorem activityMatchedUnitCubeResamplingKernel_true_eq_physicalRatio
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source : Bool) :
    activityMatchedUnitCubeResamplingKernel
        fineCoupling hfine cutoff volume source true =
      couplingKFamilyEventProbability fineCoupling hfine cutoff volume
        (targetCylinderEvent 4 volume unitCubeBlockCylinderRoots
          unitCubeBlockRefinedOccurrencePredicate) := rfl

/-! ## 4. Exact diagonal coupling and the block defect -/

def activityMatchedUnitCubeMaximalJoint
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) : Bool → Bool → Q' :=
  bernoulliMaximalJoint
    (activityMatchedCoarseParameter fineCoupling hfine cutoff volume)
    (activityMatchedRefinedParameter fineCoupling hfine cutoff volume)

theorem activityMatchedUnitCubeMaximalJoint_nonnegative
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source target : Bool) :
    (0 : Q') ≤ activityMatchedUnitCubeMaximalJoint
      fineCoupling hfine cutoff volume source target := by
  exact bernoulliMaximalJoint_nonnegative
    (activityMatchedCoarseParameter_nonnegative
      fineCoupling hfine cutoff volume)
    (activityMatchedCoarseParameter_le_one
      fineCoupling hfine cutoff volume)
    (activityMatchedRefinedParameter_nonnegative
      fineCoupling hfine cutoff volume)
    (activityMatchedRefinedParameter_le_one
      fineCoupling hfine cutoff volume)
    source target

theorem activityMatchedUnitCubeMaximalJoint_sourceMarginal
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source : Bool) :
    activityMatchedUnitCubeMaximalJoint
          fineCoupling hfine cutoff volume source false +
        activityMatchedUnitCubeMaximalJoint
          fineCoupling hfine cutoff volume source true ≈
      activityMatchedCoarseObservableLaw
        fineCoupling hfine cutoff volume source := by
  unfold activityMatchedUnitCubeMaximalJoint
    activityMatchedCoarseObservableLaw
  exact bernoulliMaximalJoint_sourceMarginal _ _ source

theorem activityMatchedUnitCubeMaximalJoint_targetMarginal
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (target : Bool) :
    activityMatchedUnitCubeMaximalJoint
          fineCoupling hfine cutoff volume false target +
        activityMatchedUnitCubeMaximalJoint
          fineCoupling hfine cutoff volume true target ≈
      activityMatchedRefinedObservableLaw
        fineCoupling hfine cutoff volume target := by
  unfold activityMatchedUnitCubeMaximalJoint
    activityMatchedRefinedObservableLaw
  exact bernoulliMaximalJoint_targetMarginal _ _ target

theorem activityMatchedUnitCubeMaximalJoint_normalized
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    (activityMatchedUnitCubeMaximalJoint
          fineCoupling hfine cutoff volume false false +
        activityMatchedUnitCubeMaximalJoint
          fineCoupling hfine cutoff volume false true) +
      (activityMatchedUnitCubeMaximalJoint
          fineCoupling hfine cutoff volume true false +
        activityMatchedUnitCubeMaximalJoint
          fineCoupling hfine cutoff volume true true) ≈
      (1 : Q') := by
  unfold activityMatchedUnitCubeMaximalJoint
  exact bernoulliMaximalJoint_normalized _ _

def activityMatchedUnitCubeMaximalCoupling
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    PositiveBoolCoupling
      (activityMatchedCoarseObservableLaw
        fineCoupling hfine cutoff volume)
      (activityMatchedRefinedObservableLaw
        fineCoupling hfine cutoff volume)
      (activityMatchedUnitCubeMaximalJoint
        fineCoupling hfine cutoff volume) :=
  bernoulliPositiveMaximalCoupling _ _
    (activityMatchedCoarseParameter_nonnegative
      fineCoupling hfine cutoff volume)
    (activityMatchedCoarseParameter_le_one
      fineCoupling hfine cutoff volume)
    (activityMatchedRefinedParameter_nonnegative
      fineCoupling hfine cutoff volume)
    (activityMatchedRefinedParameter_le_one
      fineCoupling hfine cutoff volume)

/-- The off-diagonal mass of the explicit positive joint law is exactly the
finite activity-matched block defect.  This is an identity, not a bound. -/
theorem activityMatchedUnitCubeMaximalJoint_mismatch_eqv_defect
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    boolJointMismatch
        (activityMatchedUnitCubeMaximalJoint
          fineCoupling hfine cutoff volume) ≈
      activityMatchedUnitCubeBlockDefect
        fineCoupling hfine cutoff volume := by
  unfold activityMatchedUnitCubeMaximalJoint
    activityMatchedUnitCubeBlockDefect
    couplingKUnitCubeBlockDefect
    activityMatchedCoarseParameter
    activityMatchedRefinedParameter
  exact bernoulliMaximalJoint_mismatch _ _

#print axioms bernoulliMass_nonnegative
#print axioms bernoulliMass_normalized
#print axioms bernoulliResamplingKernel_pushforward
#print axioms bernoulliMaximalJoint_nonnegative
#print axioms bernoulliMaximalJoint_sourceMarginal
#print axioms bernoulliMaximalJoint_targetMarginal
#print axioms bernoulliMaximalJoint_normalized
#print axioms bernoulliMaximalJoint_mismatch
#print axioms bernoulliPositiveMaximalCoupling
#print axioms activityMatchedUnitCubeResamplingKernel_positive
#print axioms activityMatchedUnitCubeResamplingKernel_pushforward
#print axioms activityMatchedUnitCubeResamplingKernel_source_independent
#print axioms activityMatchedUnitCubeResamplingKernel_true_eq_physicalRatio
#print axioms activityMatchedUnitCubeMaximalJoint_nonnegative
#print axioms activityMatchedUnitCubeMaximalJoint_sourceMarginal
#print axioms activityMatchedUnitCubeMaximalJoint_targetMarginal
#print axioms activityMatchedUnitCubeMaximalJoint_normalized
#print axioms activityMatchedUnitCubeMaximalCoupling
#print axioms activityMatchedUnitCubeMaximalJoint_mismatch_eqv_defect

end YMGap.Continuum.Z4FiniteObservableBlockKernel
