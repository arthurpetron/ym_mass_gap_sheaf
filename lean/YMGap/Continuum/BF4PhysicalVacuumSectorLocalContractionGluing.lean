/-
# Sector-normalized local contraction and gluing for the BF4 vacuum component

The full-carrier local-slice interface compares against the full stationary
law and therefore pays the component-mass defect after restriction.  This file
uses the already-proved generic signed-`L1` tensorization directly on the
canonical component-conditioned probability weight and density.

A single sector-local one-step density must have exact row and column laws,
glue by an exact finite density power to the physical conditioned density,
and contract every centered row by `qS <= 1/4`.  The two endpoint steps and
the middle power then give the conditioned row bound `1/16`, with no
vacuum-mass-concentration assumption.  A constructively cofinal family of
such slices compiles to the corrected mass-normalized row certificate and the
existing completed same-object vacuum-sector gap.

No sector-local slice family is constructed here.  Its gluing identity and
quarter contraction are the remaining analytic producer obligations.  No
thermodynamic or continuum limit is constructed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
import YMGap.Continuum.BF4LocalContractionGluing

namespace YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4LocalContractionGluing
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CasimirMoment
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic finite stationary local-slice tensorization -/

/-- A source row of a stationary density presented as two endpoint steps and
a middle power of one common locally contracting density. -/
structure FiniteWeightedLocalContractionGluingRow
    {State : Type}
    (states : List State) (weight : State → Q')
    (density : State → State → Q') (source : State)
    (depth : Nat) (oneStep : State → State → Q') (qS : Q') : Type 1 where
  source_mem : source ∈ states
  depth_at_least_three : 3 ≤ depth
  weight_total : listQSum weight states ≈ 1
  qS_nonnegative : (0 : Q') ≤ qS
  oneStep_row : ∀ row,
    listQSum (fun state => weight state * oneStep row state) states ≈ 1
  oneStep_column : ∀ column,
    listQSum (fun state => weight state * oneStep state column) states ≈ 1
  density_gluing : ∀ target, target ∈ states →
    density source target ≈
      finiteWeightedDensityCompose states weight oneStep
        (finiteWeightedDensityCompose states weight
          (finiteWeightedDensityPower states weight oneStep (depth - 3))
          oneStep) source target
  one_step_centered_bound : ∀ first, first ∈ states →
    finiteWeightedCenteredRowMass states weight oneStep first ≤ qS

namespace FiniteWeightedLocalContractionGluingRow

/-- The middle power has centered-row norm at most `qS^(depth-2)`. -/
theorem middlePower_centered_row_le
    {State : Type} {states : List State} {weight : State → Q'}
    {density : State → State → Q'} {source : State}
    {depth : Nat} {oneStep : State → State → Q'} {qS : Q'}
    (data : FiniteWeightedLocalContractionGluingRow
      states weight density source depth oneStep qS)
    (first : State) (hfirst : first ∈ states) :
    finiteWeightedCenteredRowMass states weight
        (finiteWeightedDensityPower states weight oneStep (depth - 3))
        first ≤
      qS ^ (depth - 2) := by
  have hpower := finiteWeightedDensityPower_centered_row_le_pow
    states weight oneStep data.weight_total data.oneStep_row
    data.oneStep_column qS data.qS_nonnegative
    data.one_step_centered_bound (depth - 3) first hfirst
  have hexponent : depth - 3 + 1 = depth - 2 := by
    have hdepth := data.depth_at_least_three
    omega
  rw [hexponent] at hpower
  exact hpower

/-- Appending the right endpoint step costs one further factor `qS`. -/
theorem middleRight_centered_row_le
    {State : Type} {states : List State} {weight : State → Q'}
    {density : State → State → Q'} {source : State}
    {depth : Nat} {oneStep : State → State → Q'} {qS : Q'}
    (data : FiniteWeightedLocalContractionGluingRow
      states weight density source depth oneStep qS)
    (first : State) (hfirst : first ∈ states) :
    finiteWeightedCenteredRowMass states weight
        (finiteWeightedDensityCompose states weight
          (finiteWeightedDensityPower states weight oneStep (depth - 3))
          oneStep)
        first ≤
      qS * (qS ^ (depth - 2)) := by
  have hcompose := finiteWeightedCenteredRowMass_compose_le
    states weight
    (finiteWeightedDensityPower states weight oneStep (depth - 3))
    oneStep data.weight_total
    (finiteWeightedDensityPower_row_normalized
      states weight oneStep data.oneStep_row (depth - 3))
    data.oneStep_column first qS data.one_step_centered_bound
  exact Q'.le_trans' _ _ _ hcompose
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (data.middlePower_centered_row_le first hfirst)
      data.qS_nonnegative)

/-- Exact density gluing and local contraction give the carrier-free
two-endpoint/middle-power coefficient. -/
theorem density_centered_row_le_local_power
    {State : Type} {states : List State} {weight : State → Q'}
    {density : State → State → Q'} {source : State}
    {depth : Nat} {oneStep : State → State → Q'} {qS : Q'}
    (data : FiniteWeightedLocalContractionGluingRow
      states weight density source depth oneStep qS) :
    finiteWeightedCenteredRowMass states weight density source ≤
      ((qS * qS) * (qS ^ (depth - 2))) := by
  let middleRight :=
    finiteWeightedDensityCompose states weight
      (finiteWeightedDensityPower states weight oneStep (depth - 3))
      oneStep
  let glued :=
    finiteWeightedDensityCompose states weight oneStep middleRight
  have hgluing :
      finiteWeightedCenteredRowMass states weight density source ≈
        finiteWeightedCenteredRowMass states weight glued source := by
    unfold finiteWeightedCenteredRowMass finiteL1Norm
      finiteWeightedCenteredTransition finiteCenteredDensity glued middleRight
    apply listQSum_congr_on
    intro target htarget
    apply Q'.abs_eqv_congr
    apply Q'.mul_eqv_congr_left
    apply Q'.add_eqv_congr_right
    exact data.density_gluing target htarget
  have hmiddleColumn : ∀ target,
      listQSum
          (fun first => weight first * middleRight first target)
          states ≈ 1 := by
    intro target
    unfold middleRight
    exact compose_column_normalized
      states weight
      (finiteWeightedDensityPower states weight oneStep (depth - 3))
      oneStep
      (finiteWeightedDensityPower_column_normalized
        states weight oneStep data.oneStep_column (depth - 3))
      data.oneStep_column target
  have houter := finiteWeightedCenteredRowMass_compose_le
    states weight oneStep middleRight data.weight_total
    data.oneStep_row hmiddleColumn source
    (qS * (qS ^ (depth - 2)))
    (fun first hfirst => data.middleRight_centered_row_le first hfirst)
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ _
    (data.one_step_centered_bound source data.source_mem)
    (Q'.mul_nonneg _ _ data.qS_nonnegative
      (Q'.pow_nonneg qS data.qS_nonnegative (depth - 2)))
  have hreorder :
      (qS * (qS ^ (depth - 2))) * qS ≈
        (qS * qS) * (qS ^ (depth - 2)) := by
    refine Q'.eqv_trans _
      (qS * ((qS ^ (depth - 2)) * qS)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (qS * (qS * (qS ^ (depth - 2)))) _ ?_
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv (qS ^ (depth - 2)) qS)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hgluing)
    (Q'.le_trans' _ _ _ houter
      (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hreorder)))

/-- A local quarter contraction makes the two endpoint factors at most
`1/16`; the remaining middle power is at most one. -/
theorem density_centered_row_le_sixteenth
    {State : Type} {states : List State} {weight : State → Q'}
    {density : State → State → Q'} {source : State}
    {depth : Nat} {oneStep : State → State → Q'} {qS : Q'}
    (data : FiniteWeightedLocalContractionGluingRow
      states weight density source depth oneStep qS)
    (qS_le_quarter : qS ≤ quarter) :
    finiteWeightedCenteredRowMass states weight density source ≤
      Q'.mkPos 1 16 (by decide) := by
  have hqOne : qS ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ qS_le_quarter (by decide)
  have hpow : qS ^ (depth - 2) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (pow_base_mono qS 1 data.qS_nonnegative hqOne (depth - 2))
      (Q'.le_of_eqv (one_pow_eqv (depth - 2)))
  have hquarterNonnegative : (0 : Q') ≤ quarter := by decide
  have hsq : qS * qS ≤ Q'.mkPos 1 16 (by decide) := by
    have hmul : qS * qS ≤ quarter * quarter :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right
          qS quarter qS qS_le_quarter data.qS_nonnegative)
        (Q'.mul_le_mul_of_nonneg_left
          qS quarter quarter qS_le_quarter hquarterNonnegative)
    exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (by decide))
  have hcoefficient :
      (qS * qS) * (qS ^ (depth - 2)) ≤
        Q'.mkPos 1 16 (by decide) := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hpow
        (Q'.mul_nonneg _ _ data.qS_nonnegative data.qS_nonnegative)) ?_
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_one_eqv (qS * qS))) hsq
  exact Q'.le_trans' _ _ _ data.density_centered_row_le_local_power
    hcoefficient

end FiniteWeightedLocalContractionGluingRow

/-! ## 2. Canonical BF4 vacuum-sector local slice -/

/-- One explicit density slice on the canonical vacuum component.  All laws
are stated with the component-conditioned probability weight and density. -/
structure PhysicalBF4VacuumSectorLocalSliceGluing
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half depth : Nat)
    (oneStep : Nat → Nat → Q') (qS : Q') : Type 1 where
  depth_at_least_three : 3 ≤ depth
  qS_nonnegative : (0 : Q') ≤ qS
  oneStep_row : ∀ row,
    listQSum
        (fun state =>
          centralPhysicalFiniteVacuumSectorMassNormalizedWeight
              w hw cutoff half state *
            oneStep row state)
        (centralPhysicalFiniteVacuumSectorIndices
          w hw cutoff half) ≈ 1
  oneStep_column : ∀ column,
    listQSum
        (fun state =>
          centralPhysicalFiniteVacuumSectorMassNormalizedWeight
              w hw cutoff half state *
            oneStep state column)
        (centralPhysicalFiniteVacuumSectorIndices
          w hw cutoff half) ≈ 1
  density_gluing : ∀ source target,
    source ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
    target ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      centralPhysicalFiniteVacuumSectorMassNormalizedDensity
          w hw cutoff half source target ≈
        finiteWeightedDensityCompose
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
            w hw cutoff half)
          oneStep
          (finiteWeightedDensityCompose
            (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
            (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
              w hw cutoff half)
            (finiteWeightedDensityPower
              (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
              (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
                w hw cutoff half)
              oneStep (depth - 3))
            oneStep)
          source target
  one_step_centered_bound : ∀ source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      finiteWeightedCenteredRowMass
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
            w hw cutoff half)
          oneStep source ≤ qS

namespace PhysicalBF4VacuumSectorLocalSliceGluing

/-- Restrict one shared sector-local slice to a specified source row. -/
def toRow
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half depth : Nat}
    {oneStep : Nat → Nat → Q'} {qS : Q'}
    (slice : PhysicalBF4VacuumSectorLocalSliceGluing
      w hw cutoff half depth oneStep qS)
    (source : Nat)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    FiniteWeightedLocalContractionGluingRow
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
        w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorMassNormalizedDensity
        w hw cutoff half)
      source depth oneStep qS where
  source_mem := hsource
  depth_at_least_three := slice.depth_at_least_three
  weight_total :=
    centralPhysicalFiniteVacuumSectorMassNormalizedWeight_total_one
      w hw cutoff half
  qS_nonnegative := slice.qS_nonnegative
  oneStep_row := slice.oneStep_row
  oneStep_column := slice.oneStep_column
  density_gluing := fun target htarget =>
    slice.density_gluing source target hsource htarget
  one_step_centered_bound := slice.one_step_centered_bound

/-- A sector-local quarter contraction gives the conditioned density row
bound `1/16` without a component-mass defect. -/
theorem conditionedDensityCenteredRow_le_sixteenth
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half depth : Nat}
    {oneStep : Nat → Nat → Q'} {qS : Q'}
    (slice : PhysicalBF4VacuumSectorLocalSliceGluing
      w hw cutoff half depth oneStep qS)
    (qS_le_quarter : qS ≤ quarter)
    (source : Nat)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    finiteWeightedCenteredRowMass
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedDensity
          w hw cutoff half)
        source ≤
      Q'.mkPos 1 16 (by decide) :=
  (slice.toRow source hsource).density_centered_row_le_sixteenth
    qS_le_quarter

end PhysicalBF4VacuumSectorLocalSliceGluing

/-! ## 3. Cofinal sector-local compiler -/

/-- One shared conditioned local slice on every constructively selected
cofinal cutoff. -/
structure FixedNomeCofinalVacuumSectorLocalSliceGluing
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 where
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  depth : Nat → Nat → Nat
  localRate : Nat → Nat → Q'
  localRate_le_quarter : ∀ base threshold,
    localRate base threshold ≤ quarter
  oneStep : Nat → Nat → Nat → Nat → Q'
  localSlice : ∀ base threshold,
    PhysicalBF4VacuumSectorLocalSliceGluing
      w hw (anchor base threshold) half
      (depth base threshold) (oneStep base threshold)
      (localRate base threshold)

namespace FixedNomeCofinalVacuumSectorLocalSliceGluing

/-- Compile a cofinal family of genuine sector-local slices to the corrected
mass-normalized row-distance interface at rate `1/16`. -/
def toMassNormalizedRowDistance
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (family : FixedNomeCofinalVacuumSectorLocalSliceGluing w hw half) :
    FixedNomeCofinalVacuumSectorMassNormalizedRowDistance
      w hw half (Q'.mkPos 1 16 (by decide)) where
  rate_nonnegative := by decide
  rate_lt_one := by decide
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  rowDistance := by
    intro base threshold source hsource
    let cutoff := family.anchor base threshold
    have hsourcePos : (0 : Q') <
        centralPhysicalFiniteWeight w hw cutoff half source :=
      centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
    have hdensity :=
      (family.localSlice base threshold).conditionedDensityCenteredRow_le_sixteenth
        (family.localRate_le_quarter base threshold) source hsource
    have hidentity :=
      finiteCarrierMassNormalizedRowDistance_eqv_densityCenteredRowMass
        (states := centralPhysicalFiniteVacuumSectorIndices
          w hw cutoff half)
        (mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
        (mass_pos := centralPhysicalFiniteVacuumSectorWeightSum_pos
          w hw cutoff half)
        (weight := centralPhysicalFiniteWeight w hw cutoff half)
        (joint := centralPhysicalFiniteKernel w hw cutoff half)
        hsourcePos
        (fun target htarget =>
          centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex htarget)
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hdensity
      (Q'.le_of_lt hsourcePos)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hidentity) ?_
    refine Q'.le_trans' _ _ _ hscaled ?_
    exact Q'.le_of_eqv
      (Q'.mul_comm_eqv
        (centralPhysicalFiniteWeight w hw cutoff half source)
        (Q'.mkPos 1 16 (by decide)))

/-- Compile the same sector-local slices all the way to the existing
same-object completed vacuum-sector strict gap. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (family : FixedNomeCofinalVacuumSectorLocalSliceGluing w hw half) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w hw half (Q'.mkPos 1 16 (by decide)) :=
  family.toMassNormalizedRowDistance.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorLocalSliceGluing

end YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing.FiniteWeightedLocalContractionGluingRow.middlePower_centered_row_le
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing.FiniteWeightedLocalContractionGluingRow.middleRight_centered_row_le
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing.FiniteWeightedLocalContractionGluingRow.density_centered_row_le_local_power
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing.FiniteWeightedLocalContractionGluingRow.density_centered_row_le_sixteenth
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing.PhysicalBF4VacuumSectorLocalSliceGluing.toRow
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing.PhysicalBF4VacuumSectorLocalSliceGluing.conditionedDensityCenteredRow_le_sixteenth
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing.FixedNomeCofinalVacuumSectorLocalSliceGluing.toMassNormalizedRowDistance
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing.FixedNomeCofinalVacuumSectorLocalSliceGluing.toVacuumSectorCenteredStrictGap
