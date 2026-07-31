/-
# Exact common-kernel action for the physical BF4 profile

The complete fixed-interface labelling is the natural source carrier after
the eighteen non-transmitted BF4 chords have been integrated.  On that
carrier define

  a_phys(b) = W(b) B(b) / Z,

where `W` is the genuine interface weight, `B(b)` is the sum of the genuine
lower-half amplitude over every positive retained state, and `Z` is the
physical slab partition.  Acting on this activity with the transposed
physical half-amplitude gives

  sum_b A(x,b) a_phys(b) = pi(x)

exactly.  Thus the physical action-identification field needed by a future
common positive-kernel/Perron certificate is computed rather than assumed.

The activity is a constructive nonzero point of the positive cone.  Its
chosen positive coordinate is the literal vacuum interface channel.  The
proof uses the exact vacuum physical summand `1`, its reflected Gram
factorization, and the fact that the total half-amplitude contains the
vacuum lower state.

The raw half-amplitude can have fusion zeros, so this module deliberately
does not manufacture a strict projective-diameter certificate for it.
Strict positivity must come from a genuine grouped primitive/terminal
smoothing factor before this exact action is transported to that common
kernel.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
import YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
import YMGap.Continuum.BF4TerminalSmoothingProjective
import YMGap.Continuum.RationalCrossRatioDiameter

namespace YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4TerminalSmoothingProjective
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero];
             try ac_rfl))

private theorem q_left_pos_of_mul_pos
    {left right : Q'}
    (hright : (0 : Q') ≤ right)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < left := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hrightNum :
      (0 : Int) ≤ right.num :=
    (Q'.zero_le_iff_num_nonneg right).mp hright
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hleftNonpos
  have hmulNonpos :
      left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg
      hleftNonpos hrightNum
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

private theorem q_right_pos_of_mul_pos
    {left right : Q'}
    (hleft : (0 : Q') ≤ left)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < right := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hleftNum :
      (0 : Int) ≤ left.num :=
    (Q'.zero_le_iff_num_nonneg left).mp hleft
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hrightNonpos
  have hmulNonpos :
      left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos
      hleftNum hrightNonpos
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

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

/-! ## 1. Literal carrier, kernel, and physical activity -/

/-- The common kernel is the genuine physical half-amplitude, transposed so
complete fixed-interface labellings are sources and positive lower-half
states are targets. -/
def centralPhysicalBoundaryKernel
    (w : Q') (K half : Nat)
    (boundary state : EdgeLabelling) : Q' :=
  centralHalfAmplitude w K half state boundary

/-- The exact physical source activity on the complete boundary carrier. -/
def centralPhysicalBoundaryActivity
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling) : Q' :=
  Q'.divPos
    (centralBoundaryWeight w K half boundary *
      centralPositiveBoundaryTotalHalfAmplitude
        w hw K half boundary)
    (slabParametricKPhysicalPartition
      w K (centralExtent half))
    (slabParametricKPhysicalPartition_pos
      hw K (centralExtent half))

private theorem centralPositiveBoundaryTotalHalfAmplitude_nonnegative_local
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling) :
    (0 : Q') ≤
      centralPositiveBoundaryTotalHalfAmplitude
        w hw K half boundary := by
  unfold centralPositiveBoundaryTotalHalfAmplitude
    finiteChannelTotalAmplitude
  apply listQSum_nonnegative_on
  intro state _
  exact centralHalfAmplitude_nonnegative
    hw K half state boundary

theorem centralPhysicalBoundaryActivity_nonnegative_on
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K half : Nat} {boundary : EdgeLabelling}
    (boundary_mem :
      boundary ∈ centralBoundaryChannels K half) :
    (0 : Q') ≤
      centralPhysicalBoundaryActivity
        w hw K half boundary := by
  unfold centralPhysicalBoundaryActivity Q'.divPos
  apply Q'.mul_nonneg
  · exact Q'.mul_nonneg _ _
      (centralBoundaryWeight_nonnegative_on
        hw boundary boundary_mem)
      (centralPositiveBoundaryTotalHalfAmplitude_nonnegative_local
        hw K half boundary)
  · exact Q'.le_of_lt
      (Q'.recipPos_pos _ _)

/-! ## 2. A literal positive vacuum coordinate -/

theorem centralVacuumBoundaryGramIntegrand_pos
    {w : Q'}
    (K half : Nat) :
    (0 : Q') <
      centralBoundaryWeight w K half zeroEdgeLabelling *
        (centralHalfAmplitude
            w K half zeroEdgeLabelling zeroEdgeLabelling *
          centralHalfAmplitude
            w K half zeroEdgeLabelling zeroEdgeLabelling) := by
  have hgram :=
    centralPhysicalTerm_eq_gram_integrand
      w
      (zeroEdgeLabelling_mem_centralHalfStates K half)
      (zeroEdgeLabelling_mem_centralBoundaryChannels K half)
      (zeroEdgeLabelling_mem_centralHalfStates K half)
  have hassemble :=
    assembleReflectedSlabLabelling_zero half
  have hone :=
    slabParametricKPhysicalTerm_zero_eqv_one
      w K (centralExtent half)
  have hproductEq :
      (1 : Q') ≈
        centralBoundaryWeight w K half zeroEdgeLabelling *
          (centralHalfAmplitude
              w K half zeroEdgeLabelling zeroEdgeLabelling *
            centralHalfAmplitude
              w K half zeroEdgeLabelling zeroEdgeLabelling) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm hone)
      (Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq
          (congrArg
            (slabParametricKPhysicalTerm
              w K (centralExtent half))
            (Eq.symm hassemble)))
        hgram)
  exact Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < 1)
    (Q'.le_of_eqv hproductEq)

theorem centralVacuumHalfAmplitude_pos
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    (0 : Q') <
      centralHalfAmplitude
        w K half zeroEdgeLabelling zeroEdgeLabelling := by
  let boundaryWeight :=
    centralBoundaryWeight w K half zeroEdgeLabelling
  let vacuumAmplitude :=
    centralHalfAmplitude
      w K half zeroEdgeLabelling zeroEdgeLabelling
  have hproduct :
      (0 : Q') <
        boundaryWeight *
          (vacuumAmplitude * vacuumAmplitude) :=
    centralVacuumBoundaryGramIntegrand_pos K half
  have hweightNonnegative :
      (0 : Q') ≤ boundaryWeight :=
    centralBoundaryWeight_nonnegative_on
      hw zeroEdgeLabelling
      (zeroEdgeLabelling_mem_centralBoundaryChannels
        K half)
  have hsquarePos :
      (0 : Q') < vacuumAmplitude * vacuumAmplitude :=
    q_right_pos_of_mul_pos hweightNonnegative hproduct
  exact q_left_pos_of_mul_pos
    (centralHalfAmplitude_nonnegative
      hw K half zeroEdgeLabelling zeroEdgeLabelling)
    hsquarePos

theorem centralPositiveBoundaryTotalHalfAmplitude_vacuum_pos
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    (0 : Q') <
      centralPositiveBoundaryTotalHalfAmplitude
        w hw K half zeroEdgeLabelling := by
  let amplitude := fun state =>
    centralHalfAmplitude
      w K half state zeroEdgeLabelling
  have hmember :
      amplitude zeroEdgeLabelling ≤
        listQSum amplitude
          (centralPositiveHalfStates w hw K half) :=
    listQSum_member_le_nonnegative
      amplitude
      (fun state =>
        centralHalfAmplitude_nonnegative
          hw K half state zeroEdgeLabelling)
      (centralPositiveHalfStates w hw K half)
      (zeroEdgeLabelling_mem_centralPositiveHalfStates
        hw K half)
  unfold centralPositiveBoundaryTotalHalfAmplitude
    finiteChannelTotalAmplitude
  exact Q'.pos_of_lt_of_le
    (centralVacuumHalfAmplitude_pos hw K half)
    hmember

theorem centralPhysicalBoundaryActivity_vacuum_pos
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    (0 : Q') <
      centralPhysicalBoundaryActivity
        w hw K half zeroEdgeLabelling := by
  unfold centralPhysicalBoundaryActivity Q'.divPos
  apply Q'.mul_pos
  · exact Q'.mul_pos
      (q_left_pos_of_mul_pos
        (Q'.mul_nonneg _ _
          (centralHalfAmplitude_nonnegative
            hw K half zeroEdgeLabelling zeroEdgeLabelling)
          (centralHalfAmplitude_nonnegative
            hw K half zeroEdgeLabelling zeroEdgeLabelling))
        (centralVacuumBoundaryGramIntegrand_pos K half))
      (centralPositiveBoundaryTotalHalfAmplitude_vacuum_pos
        hw K half)
  · exact Q'.recipPos_pos _ _

/-- The physical boundary activity is a literal nonzero point of the
nonnegative activity cone. -/
def centralPhysicalBoundaryActivityCertificate
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
      (centralBoundaryChannels K half)
      (centralPhysicalBoundaryActivity w hw K half) where
  nonnegative := by
    intro boundary boundary_mem
    exact centralPhysicalBoundaryActivity_nonnegative_on
      hw boundary_mem
  positiveSource := zeroEdgeLabelling
  positiveSource_mem :=
    zeroEdgeLabelling_mem_centralBoundaryChannels K half
  positiveSource_value :=
    centralPhysicalBoundaryActivity_vacuum_pos hw K half

/-! ## 3. Exact action identification -/

theorem centralPhysicalBoundaryKernelAction_eqv_marginal
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {state : EdgeLabelling}
    (state_mem :
      state ∈ centralPositiveHalfStates w hw K half) :
    FiniteCrossRatioDiameterCertificate.finiteKernelAction
        (centralPhysicalBoundaryKernel w K half)
        (centralBoundaryChannels K half)
        (centralPhysicalBoundaryActivity w hw K half)
        state ≈
      centralPhysicalRowMarginal w hw K half state := by
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent half)
  let hpartition :=
    slabParametricKPhysicalPartition_pos
      hw K (centralExtent half)
  let reciprocal :=
    Q'.recipPos partition hpartition
  let numerator := fun boundary =>
    centralBoundaryWeight w K half boundary *
      (centralHalfAmplitude w K half state boundary *
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary)
  unfold FiniteCrossRatioDiameterCertificate.finiteKernelAction
    centralPhysicalBoundaryKernel
    centralPhysicalBoundaryActivity
    Q'.divPos
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary => numerator boundary * reciprocal)
      (centralBoundaryChannels K half)) _ ?_ ?_
  · apply listQSum_congr
    intro boundary
    unfold numerator
    q_ring
  refine Q'.eqv_trans _
    (listQSum numerator
        (centralBoundaryChannels K half) *
      reciprocal) _ ?_ ?_
  · exact listQSum_mul_right
      numerator reciprocal
      (centralBoundaryChannels K half)
  refine Q'.eqv_trans _
    ((partition *
        centralPhysicalRowMarginal w hw K half state) *
      reciprocal) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ reciprocal
      (centralBoundaryMoment_eq_partition_mul_marginal
        state_mem)
  refine Q'.eqv_trans _
    (centralPhysicalRowMarginal w hw K half state *
      (partition * reciprocal)) _ ?_ ?_
  · calc
      (partition *
          centralPhysicalRowMarginal w hw K half state) *
            reciprocal ≈
        (centralPhysicalRowMarginal w hw K half state *
          partition) * reciprocal :=
            Q'.mul_eqv_congr_right _ _ reciprocal
              (Q'.mul_comm_eqv _ _)
      _ ≈
        centralPhysicalRowMarginal w hw K half state *
          (partition * reciprocal) :=
            Q'.mul_assoc_eqv _ _ _
  refine Q'.eqv_trans _
    (centralPhysicalRowMarginal w hw K half state * 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_recipPos_eqv partition hpartition)
  exact Q'.mul_one_eqv _

/-! ## 4. Exact transport through a grouped gluing -/

/-- Transpose a finite kernel. -/
def transposeKernel
    {Source Target : Type}
    (kernel : Source → Target → Q')
    (target : Target) (source : Source) : Q' :=
  kernel source target

/-- Strict positivity and the division-free cross-ratio bound are invariant
under transposition. -/
def transposeCertificate
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sources targets) :
    FiniteCrossRatioDiameterCertificate
      (transposeKernel kernel) targets sources where
  spread := certificate.spread
  one_le_spread := certificate.one_le_spread
  strictlyPositive := by
    intro target target_mem source source_mem
    exact certificate.strictlyPositive
      source source_mem target target_mem
  crossRatioBound := by
    intro first first_mem second second_mem
      left left_mem right right_mem
    refine Q'.le_trans' _ _ _
      (certificate.crossRatioBound
        left left_mem right right_mem
        first first_mem second second_mem) ?_
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left
        (certificate.spread * certificate.spread) _ _
        (Q'.mul_comm_eqv
          (kernel left second)
          (kernel right first)))

/-- Push the exact physical boundary activity backward through the grouped
terminal factor. -/
def centralGroupedPhysicalMiddleActivity
    {Middle : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (terminal : Middle → EdgeLabelling → Q')
    (middle : Middle) : Q' :=
  FiniteCrossRatioDiameterCertificate.finiteKernelAction
    (transposeKernel terminal)
    (centralBoundaryChannels K half)
    (centralPhysicalBoundaryActivity w hw K half)
    middle

/-- A positive terminal certificate and one genuine retained prefix row
make the pushed physical activity a constructive nonzero positive activity
on the enlarged middle carrier. -/
def centralGroupedPhysicalMiddleActivityCertificate
    {Middle : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    {prefixWeight : EdgeLabelling → Middle → Q'}
    {terminal : Middle → EdgeLabelling → Q'}
    {middles : List Middle}
    (prefixRows :
      PositivePrefixRows
        prefixWeight
        (centralPositiveHalfStates w hw K half)
        middles)
    (terminalCertificate :
      FiniteCrossRatioDiameterCertificate
        terminal middles
        (centralBoundaryChannels K half)) :
    FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
      middles
      (centralGroupedPhysicalMiddleActivity
        w hw K half terminal) where
  nonnegative := by
    intro middle middle_mem
    unfold centralGroupedPhysicalMiddleActivity
      FiniteCrossRatioDiameterCertificate.finiteKernelAction
      transposeKernel
    apply listQSum_nonnegative_on
    intro boundary boundary_mem
    exact Q'.mul_nonneg _ _
      (Q'.le_of_lt
        (terminalCertificate.strictlyPositive
          middle middle_mem boundary boundary_mem))
      (centralPhysicalBoundaryActivity_nonnegative_on
        hw boundary_mem)
  positiveSource :=
    prefixRows.positiveMiddle zeroEdgeLabelling
  positiveSource_mem :=
    prefixRows.positiveMiddle_mem
      zeroEdgeLabelling
      (zeroEdgeLabelling_mem_centralPositiveHalfStates
        hw K half)
  positiveSource_value := by
    exact
      (transposeCertificate terminalCertificate).finiteKernelAction_pos
        (centralPhysicalBoundaryActivityCertificate
          w hw K half)
        (prefixRows.positiveMiddle_mem
          zeroEdgeLabelling
          (zeroEdgeLabelling_mem_centralPositiveHalfStates
            hw K half))

/-- The common target-state kernel carried by the grouped middle label. -/
def centralGroupedPhysicalCommonKernel
    {State Middle : Type}
    (prefixWeight : State → Middle → Q')
    (middle : Middle) (state : State) : Q' :=
  prefixWeight state middle

/-- The source-target half-amplitude produced by one grouped middle gluing. -/
def groupedHalfAmplitude
    {State Middle Boundary : Type}
    (middles : List Middle)
    (prefixWeight : State → Middle → Q')
    (terminal : Middle → Boundary → Q')
    (state : State) (boundary : Boundary) : Q' :=
  FiniteCrossRatioDiameterCertificate.finiteKernelAction
    terminal middles (prefixWeight state) boundary

/-- The boundary-source common kernel obtained by transposing a grouped
terminal-smoothed half-amplitude.  Unlike the transposed prefix alone, this
kernel inherits strict positivity and projective spread directly from the
primitive terminal certificate. -/
def centralGroupedBoundaryCommonKernel
    {Middle : Type}
    (middles : List Middle)
    (prefixWeight : EdgeLabelling → Middle → Q')
    (terminal : Middle → EdgeLabelling → Q')
    (boundary state : EdgeLabelling) : Q' :=
  terminalSmoothedKernel
    prefixWeight terminal middles state boundary

/-- Finite Fubini for a grouped source-target kernel action. -/
private theorem groupedKernelAction_eqv_boundaryAction
    {State Middle Boundary : Type}
    (middles : List Middle) (boundaries : List Boundary)
    (prefixWeight : State → Middle → Q')
    (terminal : Middle → Boundary → Q')
    (activity : Boundary → Q')
    (state : State) :
    FiniteCrossRatioDiameterCertificate.finiteKernelAction
        (centralGroupedPhysicalCommonKernel prefixWeight)
        middles
        (fun middle =>
          FiniteCrossRatioDiameterCertificate.finiteKernelAction
            (transposeKernel terminal)
            boundaries activity middle)
        state ≈
      FiniteCrossRatioDiameterCertificate.finiteKernelAction
        (fun boundary state =>
          groupedHalfAmplitude
            middles prefixWeight terminal state boundary)
        boundaries activity state := by
  unfold FiniteCrossRatioDiameterCertificate.finiteKernelAction
    centralGroupedPhysicalCommonKernel transposeKernel
    groupedHalfAmplitude
  refine Q'.eqv_trans _
    (listQSum
      (fun middle =>
        listQSum
          (fun boundary =>
            prefixWeight state middle *
              (terminal middle boundary *
                activity boundary))
          boundaries)
      middles) _ ?_ ?_
  · apply listQSum_congr
    intro middle
    exact Q'.eqv_symm
      (listQSum_mul_left
        (prefixWeight state middle)
        (fun boundary =>
          terminal middle boundary *
            activity boundary)
        boundaries)
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        listQSum
          (fun middle =>
            prefixWeight state middle *
              (terminal middle boundary *
                activity boundary))
          middles)
      boundaries) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun middle boundary =>
          prefixWeight state middle *
            (terminal middle boundary *
              activity boundary))
        middles boundaries)
  apply listQSum_congr
  intro boundary
  refine Q'.eqv_trans _
    (listQSum
      (fun middle =>
        (prefixWeight state middle *
          terminal middle boundary) *
            activity boundary)
      middles) _ ?_ ?_
  · apply listQSum_congr
    intro middle
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (prefixWeight state middle)
        (terminal middle boundary)
        (activity boundary))
  refine Q'.eqv_trans _
    (listQSum
        (fun middle =>
          prefixWeight state middle *
            terminal middle boundary)
        middles *
      activity boundary) _ ?_ ?_
  · exact listQSum_mul_right
      (fun middle =>
        prefixWeight state middle *
          terminal middle boundary)
      (activity boundary) middles
  apply Q'.mul_eqv_congr_right
  apply listQSum_congr
  intro middle
  exact Q'.mul_comm_eqv
    (prefixWeight state middle)
    (terminal middle boundary)

/-- **Grouped physical action identification.**  An entrywise exact gluing
of the genuine BF4 half-amplitude transports the already-computed physical
boundary activity to the enlarged middle carrier and identifies its common
kernel action with the exact physical marginal. -/
theorem centralGroupedPhysicalCommonKernelAction_eqv_marginal
    {Middle : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (middles : List Middle)
    (prefixWeight : EdgeLabelling → Middle → Q')
    (terminal : Middle → EdgeLabelling → Q')
    (physical_gluing :
      ∀ state,
        state ∈ centralPositiveHalfStates w hw K half →
          ∀ boundary,
            boundary ∈ centralBoundaryChannels K half →
              centralHalfAmplitude w K half state boundary ≈
                FiniteCrossRatioDiameterCertificate.finiteKernelAction
                  terminal middles (prefixWeight state) boundary)
    {state : EdgeLabelling}
    (state_mem :
      state ∈ centralPositiveHalfStates w hw K half) :
    FiniteCrossRatioDiameterCertificate.finiteKernelAction
        (centralGroupedPhysicalCommonKernel prefixWeight)
        middles
        (centralGroupedPhysicalMiddleActivity
          w hw K half terminal)
        state ≈
      centralPhysicalRowMarginal w hw K half state := by
  let boundaryKernel := fun boundary state =>
      groupedHalfAmplitude
      middles prefixWeight terminal state boundary
  refine Q'.eqv_trans _
    (FiniteCrossRatioDiameterCertificate.finiteKernelAction
      boundaryKernel
      (centralBoundaryChannels K half)
      (centralPhysicalBoundaryActivity w hw K half)
      state) _ ?_ ?_
  · exact groupedKernelAction_eqv_boundaryAction
      middles (centralBoundaryChannels K half)
      prefixWeight terminal
      (centralPhysicalBoundaryActivity w hw K half)
      state
  refine Q'.eqv_trans _
    (FiniteCrossRatioDiameterCertificate.finiteKernelAction
      (centralPhysicalBoundaryKernel w K half)
      (centralBoundaryChannels K half)
      (centralPhysicalBoundaryActivity w hw K half)
      state) _ ?_ ?_
  · unfold FiniteCrossRatioDiameterCertificate.finiteKernelAction
    apply listQSum_congr_on
    intro boundary boundary_mem
    apply Q'.mul_eqv_congr_right
    unfold boundaryKernel centralPhysicalBoundaryKernel
      groupedHalfAmplitude
    exact Q'.eqv_symm
      (physical_gluing state state_mem
        boundary boundary_mem)
  exact centralPhysicalBoundaryKernelAction_eqv_marginal
    state_mem

/-- **Boundary-carrier grouped physical action identification.**  If the
terminal-smoothed grouped amplitude is entrywise the genuine physical BF4
half-amplitude, its transposed boundary-source kernel acts on the literal
physical boundary activity as the exact physical marginal.

This route keeps the common carrier on the fixed interface.  Consequently
the common-kernel certificate can be constructed by transposing
`terminalSmoothedCertificate`; no strict certificate for the generally
zero-containing prefix is required. -/
theorem centralGroupedBoundaryCommonKernelAction_eqv_marginal
    {Middle : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (middles : List Middle)
    (prefixWeight : EdgeLabelling → Middle → Q')
    (terminal : Middle → EdgeLabelling → Q')
    (physical_gluing :
      ∀ state,
        state ∈ centralPositiveHalfStates w hw K half →
          ∀ boundary,
            boundary ∈ centralBoundaryChannels K half →
              centralHalfAmplitude w K half state boundary ≈
                terminalSmoothedKernel
                  prefixWeight terminal middles state boundary)
    {state : EdgeLabelling}
    (state_mem :
      state ∈ centralPositiveHalfStates w hw K half) :
    FiniteCrossRatioDiameterCertificate.finiteKernelAction
        (centralGroupedBoundaryCommonKernel
          middles prefixWeight terminal)
        (centralBoundaryChannels K half)
        (centralPhysicalBoundaryActivity w hw K half)
        state ≈
      centralPhysicalRowMarginal w hw K half state := by
  refine Q'.eqv_trans _
    (FiniteCrossRatioDiameterCertificate.finiteKernelAction
      (centralPhysicalBoundaryKernel w K half)
      (centralBoundaryChannels K half)
      (centralPhysicalBoundaryActivity w hw K half)
      state) _ ?_ ?_
  · unfold FiniteCrossRatioDiameterCertificate.finiteKernelAction
    apply listQSum_congr_on
    intro boundary boundary_mem
    apply Q'.mul_eqv_congr_right
    unfold centralGroupedBoundaryCommonKernel
      centralPhysicalBoundaryKernel
    exact Q'.eqv_symm
      (physical_gluing state state_mem
        boundary boundary_mem)
  exact centralPhysicalBoundaryKernelAction_eqv_marginal
    state_mem

/-- Scale-uniform action identification along the exact AF trajectory.  No
new analytic field is required: the carrier, kernel, activity, positivity,
and physical action are all computed at each scale. -/
def matchedPhysicalBoundaryActivityCertificate
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (scale : Nat) :
    FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
      (centralBoundaryChannels
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale))
      (centralPhysicalBoundaryActivity
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)) :=
  centralPhysicalBoundaryActivityCertificate
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)

theorem matchedPhysicalBoundaryKernelAction_eqv_profile
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (scale : Nat) {state : EdgeLabelling}
    (state_mem :
      state ∈
        centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)) :
    FiniteCrossRatioDiameterCertificate.finiteKernelAction
        (centralPhysicalBoundaryKernel
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (centralPhysicalBoundaryActivity
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        state ≈
      centralPhysicalRowMarginal
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        state :=
  centralPhysicalBoundaryKernelAction_eqv_marginal
    state_mem

end YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction.centralVacuumBoundaryGramIntegrand_pos
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction.centralPhysicalBoundaryActivityCertificate
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction.centralPhysicalBoundaryKernelAction_eqv_marginal
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction.transposeCertificate
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction.centralGroupedPhysicalMiddleActivityCertificate
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction.centralGroupedPhysicalCommonKernelAction_eqv_marginal
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction.centralGroupedBoundaryCommonKernelAction_eqv_marginal
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction.matchedPhysicalBoundaryKernelAction_eqv_profile
