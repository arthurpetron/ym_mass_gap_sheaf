/-
# The exact component-centered boundary Gram for the BF4 vacuum sector

The physical BF4 joint has a genuine heterogeneous time cut: lower-half
states couple through complete fixed-time boundary channels.  On the
canonical vacuum component, center the indexed physical half-amplitude
against the component-conditioned stationary weight.  Exact sector closure
then gives the two moment identities and the square-mass identity needed for

    J(x,y) - pi(x) pi(y) / mass(component)

to be exactly the resulting centered weighted Gram.

This is an actual physical factorization, not a same-carrier matrix-root
certificate.  Its Tonelli row majorant is explicit and compiles cofinally to
the corrected mass-normalized row certificate and completed same-object gap.
Only the uniform analytic bound on that explicit majorant remains open.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
import YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
import YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero,
               Int.zero_add];
             try ac_rfl))

/-! ## 1. The actual component-centered half-amplitude -/

/-- Total indexed half-amplitude over the canonical vacuum component at one
fixed-time boundary channel. -/
def centralPhysicalFiniteVacuumSectorChannelTotal
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (boundary : EdgeLabelling) : Q' :=
  finiteChannelTotalAmplitude
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude
      w hw cutoff half)
    boundary

/-- The actual indexed half-amplitude centered against the stationary law
conditioned on the canonical vacuum component. -/
def centralPhysicalFiniteVacuumSectorCenteredGramAmplitude
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (index : Nat) (boundary : EdgeLabelling) : Q' :=
  finiteMarginalCenteredAmplitude
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half)
    index boundary

/-- Literal boundary-channel Tonelli majorant for one component-centered
physical row. -/
def centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) : Q' :=
  finiteWeightedGramCenteredRowMajorant
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralBoundaryChannels cutoff half)
    (centralPhysicalFiniteVacuumSectorGramWeight
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorCenteredGramAmplitude
      w hw cutoff half)
    source

/-! ## 2. Exact component moments and square mass -/

/-- The boundary-channel first moment of one sector row is exactly the
component mass times its conditioned stationary weight. -/
theorem centralPhysicalFiniteVacuumSector_boundaryMoment_eqv_mass_mul_weight
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    listQSum
        (fun boundary =>
          centralPhysicalFiniteVacuumSectorGramWeight
              w hw cutoff half boundary *
            (centralPhysicalFiniteVacuumSectorGramAmplitude
                w hw cutoff half source boundary *
              centralPhysicalFiniteVacuumSectorChannelTotal
                w hw cutoff half boundary))
        (centralBoundaryChannels cutoff half) ≈
      centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
        centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw cutoff half source := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let channels := centralBoundaryChannels cutoff half
  let gramWeight :=
    centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half
  let amplitude :=
    centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half
  let mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half
  let normalizedWeight :=
    centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half
  have hrow := weightedGram_row_eq_channelTotal
    states channels gramWeight amplitude source
  refine Q'.eqv_trans _
    (listQSum
      (weightedGram channels gramWeight amplitude source)
      states) _ (Q'.eqv_symm hrow) ?_
  refine Q'.eqv_trans _
    (listQSum
      (centralPhysicalFiniteKernel w hw cutoff half source)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htarget
    exact Q'.eqv_symm
      (centralPhysicalFiniteKernel_eqv_vacuumSectorWeightedGram
        hsource htarget)
  refine Q'.eqv_trans _
    (centralPhysicalFiniteWeight w hw cutoff half source) _
    (centralPhysicalFiniteVacuumSectorKernel_rowSum_eqv_weight hsource) ?_
  have hcancel :=
    finiteCarrierMassNormalizedWeight_mul_mass_eqv_weight
      mass
      (centralPhysicalFiniteVacuumSectorWeightSum_pos
        w hw cutoff half)
      (centralPhysicalFiniteWeight w hw cutoff half)
      source
  exact Q'.eqv_symm
    (Q'.eqv_trans _
      (normalizedWeight source * mass) _
      (Q'.mul_comm_eqv mass (normalizedWeight source))
      hcancel)

/-- The channel-weighted square of the sector half-amplitude total is exactly
the stationary mass of the canonical component. -/
theorem centralPhysicalFiniteVacuumSector_boundaryTotalSquare_eqv_mass
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    listQSum
        (fun boundary =>
          centralPhysicalFiniteVacuumSectorGramWeight
              w hw cutoff half boundary *
            (centralPhysicalFiniteVacuumSectorChannelTotal
                w hw cutoff half boundary *
              centralPhysicalFiniteVacuumSectorChannelTotal
                w hw cutoff half boundary))
        (centralBoundaryChannels cutoff half) ≈
      centralPhysicalFiniteVacuumSectorMass w hw cutoff half := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let channels := centralBoundaryChannels cutoff half
  let gramWeight :=
    centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half
  let amplitude :=
    centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half
  have hsquare := weightedGram_total_eq_channelTotalSquare
    states channels gramWeight amplitude
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (weightedGram channels gramWeight amplitude source)
          states)
      states) _ (Q'.eqv_symm hsquare) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (centralPhysicalFiniteKernel w hw cutoff half source)
          states)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro source hsource
    apply listQSum_congr_on
    intro target htarget
    exact Q'.eqv_symm
      (centralPhysicalFiniteKernel_eqv_vacuumSectorWeightedGram
        hsource htarget)
  refine Q'.eqv_trans _
    (listQSum
      (centralPhysicalFiniteWeight w hw cutoff half)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro source hsource
    exact centralPhysicalFiniteVacuumSectorKernel_rowSum_eqv_weight hsource
  exact Q'.eqv_refl _

/-! ## 3. Exact component-centered Gram identity -/

/-- The correctly mass-normalized stationary product is the component mass
times the product of the two conditioned stationary weights. -/
theorem mass_mul_massNormalizedWeights_eqv_stationaryProduct
    {State : Type} (mass : Q') (mass_pos : (0 : Q') < mass)
    (weight : State → Q') (left right : State) :
    mass *
        (finiteCarrierMassNormalizedWeight mass mass_pos weight left *
          finiteCarrierMassNormalizedWeight mass mass_pos weight right) ≈
      finiteCarrierMassNormalizedStationaryProductJoint
        mass mass_pos weight left right := by
  unfold finiteCarrierMassNormalizedWeight Q'.divPos
    finiteCarrierMassNormalizedStationaryProductJoint
    finiteStationaryProductJoint
  refine Q'.eqv_trans _
    ((mass * Q'.recipPos mass mass_pos) *
      ((weight left * weight right) *
        Q'.recipPos mass mass_pos)) _ ?_ ?_
  · q_ring
  refine Q'.eqv_trans _
    (1 * ((weight left * weight right) *
      Q'.recipPos mass mass_pos)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_recipPos_eqv mass mass_pos)
  exact Q'.one_mul_eqv _

/-- **Actual sector-centered physical factorization.**  The centered
mass-normalized physical joint entry is exactly the weighted Gram of the
component-centered physical half-amplitudes. -/
theorem centralPhysicalFiniteVacuumSector_centeredGram_eqv_joint_sub_equilibrium
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    weightedGram
        (centralBoundaryChannels cutoff half)
        (centralPhysicalFiniteVacuumSectorGramWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCenteredGramAmplitude
          w hw cutoff half)
        left right ≈
      centralPhysicalFiniteKernel w hw cutoff half left right +
        (-finiteCarrierMassNormalizedStationaryProductJoint
          (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorWeightSum_pos
            w hw cutoff half)
          (centralPhysicalFiniteWeight w hw cutoff half)
          left right) := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let channels := centralBoundaryChannels cutoff half
  let gramWeight :=
    centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half
  let amplitude :=
    centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half
  let normalizedWeight :=
    centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half
  let mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half
  let mass_pos :=
    centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half
  have hcentered := weightedGram_centered_eq_raw_sub_rankOne
    states channels gramWeight amplitude normalizedWeight mass left right
    (centralPhysicalFiniteVacuumSector_boundaryMoment_eqv_mass_mul_weight
      hleft)
    (centralPhysicalFiniteVacuumSector_boundaryMoment_eqv_mass_mul_weight
      hright)
    (centralPhysicalFiniteVacuumSector_boundaryTotalSquare_eqv_mass
      w hw cutoff half)
  refine Q'.eqv_trans _
    (weightedGram channels gramWeight amplitude left right +
      (-(mass * (normalizedWeight left * normalizedWeight right)))) _
    hcentered ?_
  apply Q'.add_eqv_congr'
  · exact Q'.eqv_symm
      (centralPhysicalFiniteKernel_eqv_vacuumSectorWeightedGram
        hleft hright)
  exact Q'.neg_eqv_congr _ _
    (mass_mul_massNormalizedWeights_eqv_stationaryProduct
      mass mass_pos
      (centralPhysicalFiniteWeight w hw cutoff half)
      left right)

/-! ## 4. The exact finite row majorant and cofinal compiler -/

/-- The corrected component-equilibrium row distance is bounded by the
literal centered boundary-Gram Tonelli majorant. -/
theorem centralPhysicalFiniteVacuumSector_rowDistance_le_centeredGramMajorant
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    finiteJointDifferenceAbsRowMass
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteKernel w hw cutoff half)
        (finiteCarrierMassNormalizedStationaryProductJoint
          (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorWeightSum_pos
            w hw cutoff half)
          (centralPhysicalFiniteWeight w hw cutoff half))
        source ≤
      centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
        w hw cutoff half source := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let channels := centralBoundaryChannels cutoff half
  let gramWeight :=
    centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half
  let centeredAmplitude :=
    centralPhysicalFiniteVacuumSectorCenteredGramAmplitude
      w hw cutoff half
  have hrows :
      finiteJointDifferenceAbsRowMass
          states
          (centralPhysicalFiniteKernel w hw cutoff half)
          (finiteCarrierMassNormalizedStationaryProductJoint
            (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
            (centralPhysicalFiniteVacuumSectorWeightSum_pos
              w hw cutoff half)
            (centralPhysicalFiniteWeight w hw cutoff half))
          source ≈
        listQSum
          (fun target =>
            Q'.abs
              (weightedGram channels gramWeight centeredAmplitude
                source target))
          states := by
    unfold finiteJointDifferenceAbsRowMass
    apply listQSum_congr_on
    intro target htarget
    exact Q'.abs_eqv_congr
      (Q'.eqv_symm
        (centralPhysicalFiniteVacuumSector_centeredGram_eqv_joint_sub_equilibrium
          hsource htarget))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrows)
    (weightedGram_centered_row_abs_le
      states channels gramWeight centeredAmplitude source)

/-- One uniform strict upper bound on the actual component-centered boundary
Gram majorant along a constructively cofinal cutoff family. -/
structure FixedNomeCofinalVacuumSectorCenteredGramMajorant
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  majorantBound : ∀ base threshold source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w hw (anchor base threshold) half →
      centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
          w hw (anchor base threshold) half source ≤
        rate * centralPhysicalFiniteWeight
          w hw (anchor base threshold) half source

namespace FixedNomeCofinalVacuumSectorCenteredGramMajorant

/-- The actual boundary-Gram majorant compiles to the corrected
mass-normalized row-distance certificate. -/
def toMassNormalizedRowDistance
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorCenteredGramMajorant
      w hw half rate) :
    FixedNomeCofinalVacuumSectorMassNormalizedRowDistance
      w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  rowDistance := by
    intro base threshold source hsource
    exact Q'.le_trans' _ _ _
      (centralPhysicalFiniteVacuumSector_rowDistance_le_centeredGramMajorant
        hsource)
      (family.majorantBound base threshold source hsource)

/-- The same actual boundary-Gram estimate reaches the completed same-object
vacuum-sector strict gap. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorCenteredGramMajorant
      w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate :=
  family.toMassNormalizedRowDistance.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorCenteredGramMajorant

end YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram.centralPhysicalFiniteVacuumSector_boundaryMoment_eqv_mass_mul_weight
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram.centralPhysicalFiniteVacuumSector_boundaryTotalSquare_eqv_mass
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram.centralPhysicalFiniteVacuumSector_centeredGram_eqv_joint_sub_equilibrium
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram.centralPhysicalFiniteVacuumSector_rowDistance_le_centeredGramMajorant
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram.FixedNomeCofinalVacuumSectorCenteredGramMajorant.toVacuumSectorCenteredStrictGap
