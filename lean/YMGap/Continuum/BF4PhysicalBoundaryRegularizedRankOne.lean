/-
# Canonical regularized rank-one smoothing of the physical boundary carrier

The direct physical reduction needs a strictly positive boundary kernel
`P` for which `A P` approximates the genuine half-amplitude `A`.  This file
constructs `P` rather than accepting it as arbitrary data.

At one finite regulator, sum every physical amplitude column over the
retained positive source rows, add a positive rational pseudocount, and
normalize the resulting finite boundary profile.  The kernel with every row
equal to that profile is:

* strictly positive;
* exactly row normalized;
* exactly rank one, hence of projective spread one; and
* completely determined by the literal physical amplitude and one positive
  rational regularization parameter.

Its action has the exact closed form

  (A P)(source,boundary)
    = rowMass(A,source) * regularizedProfile(boundary).

Thus the remaining analytic statement becomes an explicit finite rank-one
defect.  Exact enumeration in Rust, C, or Python may evaluate the displayed
quantities, while Lean rechecks every emitted rational inequality.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingCrossTail

namespace YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingCrossTail
open YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4TerminalSmoothingProjective
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive normalized boundary profile -/

/-- Aggregate one physical boundary column over every retained positive
half-state. -/
def centralBoundaryColumnMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling) : Q' :=
  listQSum
    (fun source =>
      centralHalfAmplitude w K half source boundary)
    (centralPositiveHalfStates w hw K half)

theorem centralBoundaryColumnMass_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling) :
    (0 : Q') ≤
      centralBoundaryColumnMass w hw K half boundary := by
  unfold centralBoundaryColumnMass
  apply listQSum_nonnegative_on
  intro source _
  exact centralHalfAmplitude_nonnegative
    hw K half source boundary

/-- Add a strictly positive pseudocount before normalization. -/
def centralRegularizedBoundaryNumerator
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (boundary : EdgeLabelling) : Q' :=
  pseudocount +
    centralBoundaryColumnMass w hw K half boundary

theorem centralRegularizedBoundaryNumerator_pos
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount)
    (boundary : EdgeLabelling) :
    (0 : Q') <
      centralRegularizedBoundaryNumerator
        w hw K half pseudocount boundary := by
  unfold centralRegularizedBoundaryNumerator
  exact Q'.pos_add_nonneg pseudocount_pos
    (centralBoundaryColumnMass_nonnegative
      hw K half boundary)

/-- Total regularized column mass on the literal finite boundary carrier. -/
def centralRegularizedBoundaryDenominator
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q') : Q' :=
  listQSum
    (centralRegularizedBoundaryNumerator
      w hw K half pseudocount)
    (centralBoundaryChannels K half)

private theorem listQSum_member_le_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {selected : A},
      selected ∈ items →
        value selected ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail
            (fun item _ => hvalue item))
      · have ih :=
          listQSum_member_le_nonnegative
            value hvalue tail htail
        have htailLe :
            listQSum value tail ≤
              value head + listQSum value tail := by
          have hle :=
            Q'.add_le_add_right
              (0 : Q') (value head)
              (listQSum value tail)
              (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih htailLe

theorem centralRegularizedBoundaryDenominator_pos
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount) :
    (0 : Q') <
      centralRegularizedBoundaryDenominator
        w hw K half pseudocount := by
  let numerator :=
    centralRegularizedBoundaryNumerator
      w hw K half pseudocount
  have hmember :
      numerator zeroEdgeLabelling ≤
        listQSum numerator
          (centralBoundaryChannels K half) :=
    listQSum_member_le_nonnegative
      numerator
      (fun boundary =>
        Q'.le_of_lt
          (centralRegularizedBoundaryNumerator_pos
            hw K half pseudocount_pos boundary))
      (centralBoundaryChannels K half)
      (zeroEdgeLabelling_mem_centralBoundaryChannels
        K half)
  exact Q'.pos_of_lt_of_le
    (centralRegularizedBoundaryNumerator_pos
      hw K half pseudocount_pos zeroEdgeLabelling)
    hmember

/-- The canonical normalized, pseudocount-regularized boundary profile. -/
def centralRegularizedBoundaryProfile
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (pseudocount_pos : (0 : Q') < pseudocount)
    (boundary : EdgeLabelling) : Q' :=
  Q'.divPos
    (centralRegularizedBoundaryNumerator
      w hw K half pseudocount boundary)
    (centralRegularizedBoundaryDenominator
      w hw K half pseudocount)
    (centralRegularizedBoundaryDenominator_pos
      hw K half pseudocount_pos)

theorem centralRegularizedBoundaryProfile_pos
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount)
    (boundary : EdgeLabelling) :
    (0 : Q') <
      centralRegularizedBoundaryProfile
        w hw K half pseudocount pseudocount_pos boundary := by
  exact Q'.divPos_pos _ _ _
    (centralRegularizedBoundaryNumerator_pos
      hw K half pseudocount_pos boundary)

/-- The constructed boundary profile has exact finite mass one. -/
theorem centralRegularizedBoundaryProfile_normalized
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount) :
    listQSum
        (centralRegularizedBoundaryProfile
          w hw K half pseudocount pseudocount_pos)
        (centralBoundaryChannels K half) ≈
      1 := by
  let numerator :=
    centralRegularizedBoundaryNumerator
      w hw K half pseudocount
  let denominator :=
    centralRegularizedBoundaryDenominator
      w hw K half pseudocount
  let denominator_pos :=
    centralRegularizedBoundaryDenominator_pos
      hw K half pseudocount_pos
  let reciprocal := Q'.recipPos denominator denominator_pos
  unfold centralRegularizedBoundaryProfile Q'.divPos
  change
    listQSum
        (fun boundary => numerator boundary * reciprocal)
        (centralBoundaryChannels K half) ≈
      1
  refine Q'.eqv_trans _
    (listQSum numerator
        (centralBoundaryChannels K half) * reciprocal) _ ?_ ?_
  · exact listQSum_mul_right
      numerator reciprocal
      (centralBoundaryChannels K half)
  change denominator * reciprocal ≈ 1
  exact Q'.mul_recipPos_eqv denominator denominator_pos

/-! ## 2. The canonical rank-one smoothing kernel -/

/-- Every boundary source is sent to the same normalized physical column
profile. -/
def centralRegularizedBoundaryRankOneKernel
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (pseudocount_pos : (0 : Q') < pseudocount)
    (_source target : EdgeLabelling) : Q' :=
  centralRegularizedBoundaryProfile
    w hw K half pseudocount pseudocount_pos target

theorem centralRegularizedBoundaryRankOneKernel_row_normalized
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount)
    (source : EdgeLabelling) :
    listQSum
        (centralRegularizedBoundaryRankOneKernel
          w hw K half pseudocount pseudocount_pos source)
        (centralBoundaryChannels K half) ≈
      1 := by
  exact centralRegularizedBoundaryProfile_normalized
    hw K half pseudocount_pos

/-- A row-independent positive kernel has exact projective spread one. -/
def centralRegularizedBoundaryRankOneCertificate
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount) :
    FiniteCrossRatioDiameterCertificate
      (centralRegularizedBoundaryRankOneKernel
        w hw K half pseudocount pseudocount_pos)
      (centralBoundaryChannels K half)
      (centralBoundaryChannels K half) where
  spread := 1
  one_le_spread := Q'.le_refl' 1
  strictlyPositive := by
    intro _source _source_mem target _target_mem
    exact centralRegularizedBoundaryProfile_pos
      hw K half pseudocount_pos target
  crossRatioBound := by
    intro _first _hfirst _second _hsecond
      left _hleft right _hright
    unfold centralRegularizedBoundaryRankOneKernel
    refine Q'.le_of_eqv ?_
    calc
      centralRegularizedBoundaryProfile
            w hw K half pseudocount pseudocount_pos left *
          centralRegularizedBoundaryProfile
            w hw K half pseudocount pseudocount_pos right ≈
        centralRegularizedBoundaryProfile
            w hw K half pseudocount pseudocount_pos right *
          centralRegularizedBoundaryProfile
            w hw K half pseudocount pseudocount_pos left :=
        Q'.mul_comm_eqv _ _
      _ ≈
          1 *
            (centralRegularizedBoundaryProfile
                w hw K half pseudocount pseudocount_pos right *
              centralRegularizedBoundaryProfile
                w hw K half pseudocount pseudocount_pos left) :=
        Q'.eqv_symm (Q'.one_mul_eqv _)
      _ ≈
          ((1 : Q') * 1) *
            (centralRegularizedBoundaryProfile
                w hw K half pseudocount pseudocount_pos right *
              centralRegularizedBoundaryProfile
                w hw K half pseudocount pseudocount_pos left) :=
        Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_symm (Q'.one_mul_eqv 1))

theorem centralRegularizedBoundaryRankOneCertificate_spread_square_le_split
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount) :
    let certificate :=
      centralRegularizedBoundaryRankOneCertificate
        hw K half pseudocount_pos
    certificate.spread * certificate.spread ≤
      splitProjectiveCeiling := by
  dsimp only [centralRegularizedBoundaryRankOneCertificate]
  decide

/-! ## 3. Exact action and explicit rank-one defect -/

/-- Total mass of one physical amplitude row on the boundary carrier. -/
def centralHalfAmplitudeBoundaryRowMass
    (w : Q') (K half : Nat) (source : EdgeLabelling) : Q' :=
  listQSum
    (centralHalfAmplitude w K half source)
    (centralBoundaryChannels K half)

/-- Acting by the constructed rank-one kernel is exactly projection onto
the normalized aggregate column profile. -/
theorem centralHalfAmplitude_regularizedRankOneAction_eqv
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount)
    (source boundary : EdgeLabelling) :
    centralHalfAmplitudeBoundaryAction
        w K half
        (centralRegularizedBoundaryRankOneKernel
          w hw K half pseudocount pseudocount_pos)
        source boundary ≈
      centralHalfAmplitudeBoundaryRowMass
          w K half source *
        centralRegularizedBoundaryProfile
          w hw K half pseudocount pseudocount_pos boundary := by
  unfold centralHalfAmplitudeBoundaryAction
    terminalSmoothedKernel
    FiniteCrossRatioDiameterCertificate.finiteKernelAction
    centralRegularizedBoundaryRankOneKernel
    centralHalfAmplitudeBoundaryRowMass
  refine Q'.eqv_trans _
    (centralRegularizedBoundaryProfile
        w hw K half pseudocount pseudocount_pos boundary *
      listQSum
        (centralHalfAmplitude w K half source)
        (centralBoundaryChannels K half)) _ ?_ ?_
  · exact
      listQSum_mul_left
        (centralRegularizedBoundaryProfile
          w hw K half pseudocount pseudocount_pos boundary)
        (centralHalfAmplitude w K half source)
        (centralBoundaryChannels K half)
  · exact Q'.mul_comm_eqv _ _

/-- Fully explicit physical rank-one defect left by the canonical smoother. -/
def centralHalfAmplitudeRegularizedRankOneDefect
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (pseudocount_pos : (0 : Q') < pseudocount)
    (source boundary : EdgeLabelling) : Q' :=
  Q'.abs
    (centralHalfAmplitude w K half source boundary +
      -(centralHalfAmplitudeBoundaryRowMass w K half source *
        centralRegularizedBoundaryProfile
          w hw K half pseudocount pseudocount_pos boundary))

theorem centralHalfAmplitudeBoundaryActionDefect_eqv_regularizedRankOne
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount)
    (source boundary : EdgeLabelling) :
    centralHalfAmplitudeBoundaryActionDefect
        w K half
        (centralRegularizedBoundaryRankOneKernel
          w hw K half pseudocount pseudocount_pos)
        source boundary ≈
      centralHalfAmplitudeRegularizedRankOneDefect
        w hw K half pseudocount pseudocount_pos
        source boundary := by
  unfold centralHalfAmplitudeBoundaryActionDefect
    centralHalfAmplitudeRegularizedRankOneDefect
  apply Q'.abs_eqv_congr
  apply Q'.add_eqv_congr_left
  apply Q'.neg_eqv_congr
  exact centralHalfAmplitude_regularizedRankOneAction_eqv
    hw K half pseudocount_pos source boundary

end YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne.centralRegularizedBoundaryDenominator_pos
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne.centralRegularizedBoundaryProfile_normalized
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne.centralRegularizedBoundaryRankOneCertificate
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne.centralHalfAmplitude_regularizedRankOneAction_eqv
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne.centralHalfAmplitudeBoundaryActionDefect_eqv_regularizedRankOne
