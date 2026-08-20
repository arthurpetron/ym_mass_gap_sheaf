/-
# Physical BF4 boundary self-smoothing reduction

The lower-half amplitude already has a canonical source-independent finite
middle carrier: the literal boundary-channel list.  On that carrier the
faithful mixed-radix Dirac kernel gives the exact factorization

  A(source, boundary)
    = sum_middle delta(middle,boundary) * A(source,middle).

Replacing `delta` by a strictly positive terminal kernel `P` changes the
ideal entry to the completely explicit finite action `A P`.  This file turns
that observation into the computed-floor interface.  Thus the arbitrary
middle carrier, arbitrary prefix, and an unspecified physical gluing are all
removed; the remaining analytic statement is precisely the finite
approximate-invariance defect

  |A(source,boundary) - (A P)(source,boundary)|.

The sparse Dirac factorization itself cannot be used as a positive terminal
certificate when two retained boundary codes differ.  That obstruction is
recorded explicitly below rather than hidden in the construction.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4BoundaryMessageComputedTerminalFloor
import YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
import YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
import YMGap.Continuum.Z4BoundedEdgeLabellingNodup

namespace YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4BoundaryMessageComputedTerminalFloor
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4TerminalSmoothingProjective
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A faithful code on the finite boundary carrier -/

/-- Mixed-radix code on exactly the fixed-interface face coordinates. -/
def centralBoundaryCode
    (K half : Nat) (boundary : EdgeLabelling) : Nat :=
  edgeLabellingCode
    (K + 1) (centralFixedFaceIds half) boundary

private theorem edgeLabellingCode_eq_implies_agree_local
    {base : Nat} (hbase : 0 < base) :
    ∀ {ids : List Nat} {left right : EdgeLabelling},
      (∀ id, id ∈ ids → left id < base) →
      (∀ id, id ∈ ids → right id < base) →
      edgeLabellingCode base ids left =
        edgeLabellingCode base ids right →
      ∀ id, id ∈ ids → left id = right id
  | [], left, right, _, _, _, id, hmem =>
      False.elim (List.not_mem_nil hmem)
  | head :: rest, left, right, hleft, hright, hcode, id, hmem => by
      have hleftHead : left head < base :=
        hleft head List.mem_cons_self
      have hrightHead : right head < base :=
        hright head List.mem_cons_self
      have hmod :=
        congrArg (fun value => value % base) hcode
      have hhead : left head = right head := by
        simpa [edgeLabellingCode,
          Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hleftHead,
          Nat.mod_eq_of_lt hrightHead] using hmod
      rcases List.mem_cons.mp hmem with hid | hrest
      · subst id
        exact hhead
      · have hdiv :=
          congrArg (fun value => value / base) hcode
        have htailCode :
            edgeLabellingCode base rest left =
              edgeLabellingCode base rest right := by
          simpa [edgeLabellingCode,
            Nat.add_mul_div_left,
            Nat.div_eq_of_lt hleftHead,
            Nat.div_eq_of_lt hrightHead,
            hbase] using hdiv
        exact edgeLabellingCode_eq_implies_agree_local hbase
          (fun position hposition =>
            hleft position
              (List.mem_cons_of_mem head hposition))
          (fun position hposition =>
            hright position
              (List.mem_cons_of_mem head hposition))
          htailCode id hrest

private theorem edgeLabellingCode_injective_on_bounded_local
    {base : Nat} (hbase : 0 < base)
    {ids : List Nat} {left right : EdgeLabelling}
    (hleftBound : ∀ id, id ∈ ids → left id < base)
    (hrightBound : ∀ id, id ∈ ids → right id < base)
    (hleftZero : ∀ id, id ∉ ids → left id = 0)
    (hrightZero : ∀ id, id ∉ ids → right id = 0)
    (hcode :
      edgeLabellingCode base ids left =
        edgeLabellingCode base ids right) :
    left = right := by
  funext id
  by_cases hid : id ∈ ids
  · exact edgeLabellingCode_eq_implies_agree_local hbase
      hleftBound hrightBound hcode id hid
  · rw [hleftZero id hid, hrightZero id hid]

/-- The boundary code is injective on the literal bounded boundary list. -/
theorem centralBoundaryCode_injective_on_channels
    {K half : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ centralBoundaryChannels K half)
    (hright : right ∈ centralBoundaryChannels K half)
    (hcode :
      centralBoundaryCode K half left =
        centralBoundaryCode K half right) :
    left = right := by
  have hleftData :=
    boundedEdgeLabellings_sound
      K (centralFixedFaceIds half) left hleft
  have hrightData :=
    boundedEdgeLabellings_sound
      K (centralFixedFaceIds half) right hright
  exact edgeLabellingCode_injective_on_bounded_local
    (Nat.zero_lt_succ K)
    hleftData.1 hrightData.1
    hleftData.2 hrightData.2 hcode

/-! ## 2. Exact identity-terminal factorization -/

/-- Faithful zero-one identity kernel on bounded boundary channels. -/
def centralBoundaryCodeDelta
    (K half : Nat)
    (middle boundary : EdgeLabelling) : Q' :=
  if centralBoundaryCode K half middle =
      centralBoundaryCode K half boundary then 1 else 0

theorem centralBoundaryCodeDelta_nonnegative
    (K half : Nat) (middle boundary : EdgeLabelling) :
    (0 : Q') ≤
      centralBoundaryCodeDelta K half middle boundary := by
  unfold centralBoundaryCodeDelta
  by_cases hcode :
      centralBoundaryCode K half middle =
        centralBoundaryCode K half boundary
  · rw [if_pos hcode]
    exact Q'.zero_le_one
  · rw [if_neg hcode]
    exact Q'.le_refl' 0

private theorem listQSum_boundaryCodeDelta_zero_of_not_mem
    (K half : Nat) (selected : EdgeLabelling)
    (hselected : selected ∈ centralBoundaryChannels K half)
    (value : EdgeLabelling → Q') :
    ∀ items : List EdgeLabelling,
      (∀ item, item ∈ items →
        item ∈ centralBoundaryChannels K half) →
      selected ∉ items →
      listQSum
          (fun item =>
            centralBoundaryCodeDelta K half item selected *
              value item)
          items ≈
        0
  | [], _, _ => Q'.eqv_refl 0
  | head :: tail, hcarrier, hnot => by
      have hhead := hcarrier head List.mem_cons_self
      have htail :
          ∀ item, item ∈ tail →
            item ∈ centralBoundaryChannels K half :=
        fun item hitem =>
          hcarrier item (List.mem_cons_of_mem head hitem)
      have hselectedTail : selected ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      have hcode :
          centralBoundaryCode K half head ≠
            centralBoundaryCode K half selected := by
        intro heq
        have hsame :=
          centralBoundaryCode_injective_on_channels
            hhead hselected heq
        subst head
        exact hnot List.mem_cons_self
      simp only [listQSum, centralBoundaryCodeDelta, if_neg hcode]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.zero_mul_eqv (value head))
          (listQSum_boundaryCodeDelta_zero_of_not_mem
            K half selected hselected value tail
            htail hselectedTail))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_boundaryCodeDelta_of_mem_nodup
    (K half : Nat) (selected : EdgeLabelling)
    (hselected : selected ∈ centralBoundaryChannels K half)
    (value : EdgeLabelling → Q') :
    ∀ items : List EdgeLabelling,
      (∀ item, item ∈ items →
        item ∈ centralBoundaryChannels K half) →
      items.Nodup →
      selected ∈ items →
      listQSum
          (fun item =>
            centralBoundaryCodeDelta K half item selected *
              value item)
          items ≈
        value selected
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hcarrier, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum, centralBoundaryCodeDelta, if_true]
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr'
            (Q'.one_mul_eqv (value selected))
            (listQSum_boundaryCodeDelta_zero_of_not_mem
              K half selected hselected value tail
              (fun item hitem =>
                hcarrier item
                  (List.mem_cons_of_mem selected hitem))
              hparts.1))
          (Q'.eqv_of_eq (Q'.add_zero' (value selected)))
      · have hheadCarrier := hcarrier head List.mem_cons_self
        have hcode :
            centralBoundaryCode K half head ≠
              centralBoundaryCode K half selected := by
          intro heq
          have hsame :=
            centralBoundaryCode_injective_on_channels
              hheadCarrier hselected heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, centralBoundaryCodeDelta, if_neg hcode]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.zero_mul_eqv (value head))
            (listQSum_boundaryCodeDelta_of_mem_nodup
              K half selected hselected value tail
              (fun item hitem =>
                hcarrier item
                  (List.mem_cons_of_mem head hitem))
              hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' (value selected)))

/-- A faithful boundary Dirac action evaluates any rational boundary row. -/
theorem centralBoundaryCodeDelta_action_eqv
    (K half : Nat) (value : EdgeLabelling → Q')
    (boundary : EdgeLabelling)
    (boundary_mem :
      boundary ∈ centralBoundaryChannels K half) :
    FiniteCrossRatioDiameterCertificate.finiteKernelAction
        (centralBoundaryCodeDelta K half)
        (centralBoundaryChannels K half)
        value boundary ≈
      value boundary := by
  unfold FiniteCrossRatioDiameterCertificate.finiteKernelAction
  exact listQSum_boundaryCodeDelta_of_mem_nodup
    K half boundary boundary_mem value
    (centralBoundaryChannels K half)
    (fun item hitem => hitem)
    (centralBoundaryChannels_nodup K half)
    boundary_mem

/-- The genuine physical half-amplitude factors exactly through the common
boundary carrier and its sparse identity terminal. -/
theorem centralHalfAmplitude_boundaryIdentityFactorization
    (w : Q') (K half : Nat)
    (source boundary : EdgeLabelling)
    (boundary_mem :
      boundary ∈ centralBoundaryChannels K half) :
    centralHalfAmplitude w K half source boundary ≈
      terminalSmoothedKernel
        (centralHalfAmplitude w K half)
        (centralBoundaryCodeDelta K half)
        (centralBoundaryChannels K half)
        source boundary := by
  exact Q'.eqv_symm
    (centralBoundaryCodeDelta_action_eqv
      K half
      (centralHalfAmplitude w K half source)
      boundary boundary_mem)

/-- A differing retained boundary code witnesses the exact reason the
identity terminal is not strictly positive. -/
theorem centralBoundaryCodeDelta_eq_zero_of_code_ne
    {K half : Nat} {middle boundary : EdgeLabelling}
    (hcode :
      centralBoundaryCode K half middle ≠
        centralBoundaryCode K half boundary) :
    centralBoundaryCodeDelta K half middle boundary = 0 := by
  simp [centralBoundaryCodeDelta, hcode]

/-! ## 3. Replace the identity by a positive smoothing kernel -/

/-! ### Constructive positive-coordinate extraction -/

/-- A total finite search: return the first strictly positive entry, or the
supplied fallback if there is none. -/
def firstPositiveOr {A : Type}
    (fallback : A) (value : A → Q') : List A → A
  | [] => fallback
  | head :: tail =>
      if decide ((0 : Q') < value head) then head
      else firstPositiveOr fallback value tail

private theorem q_nonpos_of_not_pos {q : Q'}
    (hnot : ¬ (0 : Q') < q) :
    q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

/-- If a finite sum is strictly positive, the total search returns a member
whose value is strictly positive.  The proof is recursive and computational;
there is no choice operation. -/
theorem firstPositiveOr_mem_and_pos_of_sum_pos
    {A : Type} (fallback : A) (value : A → Q') :
    ∀ items : List A,
      (0 : Q') < listQSum value items →
        firstPositiveOr fallback value items ∈ items ∧
          (0 : Q') <
            value (firstPositiveOr fallback value items)
  | [], hsum => by
      have hnum := Q'.num_pos_of_pos hsum
      simp only [listQSum] at hnum
      exact False.elim (Int.lt_irrefl 0 hnum)
  | head :: tail, hsum => by
      by_cases hhead : (0 : Q') < value head
      · simp [firstPositiveOr, hhead]
      · have hheadLe : value head ≤ 0 :=
          q_nonpos_of_not_pos hhead
        have hsumLe :
            value head + listQSum value tail ≤
              listQSum value tail := by
          have hadd :=
            Q'.add_le_add_right
              (value head) 0 (listQSum value tail) hheadLe
          simpa only [Q'.zero_add'] using hadd
        have htail :
            (0 : Q') < listQSum value tail := by
          change (0 : Q') <
            value head + listQSum value tail at hsum
          exact Q'.pos_of_lt_of_le hsum hsumLe
        have ih :=
          firstPositiveOr_mem_and_pos_of_sum_pos
            fallback value tail htail
        simp only [firstPositiveOr, hhead]
        exact
          ⟨List.mem_cons_of_mem head ih.1, ih.2⟩

private theorem q_left_pos_of_mul_pos_local
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

private theorem q_right_pos_of_mul_pos_local
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

/-- One boundary term in the exact physical first-moment row. -/
def centralBoundaryMomentTerm
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (source boundary : EdgeLabelling) : Q' :=
  centralBoundaryWeight w K half boundary *
    (centralHalfAmplitude w K half source boundary *
      centralPositiveBoundaryTotalHalfAmplitude
        w hw K half boundary)

private theorem centralPositiveBoundaryTotalHalfAmplitude_nonnegative
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

theorem centralBoundaryMomentTerm_nonnegative_on
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K half : Nat} (source boundary : EdgeLabelling)
    (boundary_mem :
      boundary ∈ centralBoundaryChannels K half) :
    (0 : Q') ≤
      centralBoundaryMomentTerm
        w hw K half source boundary := by
  unfold centralBoundaryMomentTerm
  exact Q'.mul_nonneg _ _
    (centralBoundaryWeight_nonnegative_on
      hw boundary boundary_mem)
    (Q'.mul_nonneg _ _
      (centralHalfAmplitude_nonnegative
        hw K half source boundary)
      (centralPositiveBoundaryTotalHalfAmplitude_nonnegative
        hw K half boundary))

/-- Every retained source has a strictly positive total first-moment row. -/
theorem centralBoundaryMomentSum_pos
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half) :
    (0 : Q') <
      listQSum
        (centralBoundaryMomentTerm w hw K half source)
        (centralBoundaryChannels K half) := by
  have hmarginal :
      (0 : Q') <
        centralPhysicalRowMarginal w hw K half source :=
    (mem_centralPositiveHalfStates_iff.mp source_mem).2
  have hproduct :
      (0 : Q') <
        slabParametricKPhysicalPartition
            w K (centralExtent half) *
          centralPhysicalRowMarginal
            w hw K half source :=
    Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent half))
      hmarginal
  have hmoment :=
    centralBoundaryMoment_eq_partition_mul_marginal
      source_mem
  exact Q'.pos_of_lt_of_le hproduct
    (Q'.ge_of_eqv hmoment)

/-- The total finite search selecting a positive boundary coordinate. -/
def centralPositiveBoundaryCoordinate
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (source : EdgeLabelling) :
    EdgeLabelling :=
  firstPositiveOr zeroEdgeLabelling
    (centralBoundaryMomentTerm w hw K half source)
    (centralBoundaryChannels K half)

/-- The selected positive moment term forces the physical half-amplitude
factor itself to be strictly positive. -/
theorem centralPositiveBoundaryCoordinate_mem_and_amplitude_pos
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half) :
    centralPositiveBoundaryCoordinate w hw K half source ∈
        centralBoundaryChannels K half ∧
      (0 : Q') <
        centralHalfAmplitude w K half source
          (centralPositiveBoundaryCoordinate
            w hw K half source) := by
  let selected :=
    centralPositiveBoundaryCoordinate w hw K half source
  have hselected :=
    firstPositiveOr_mem_and_pos_of_sum_pos
      zeroEdgeLabelling
      (centralBoundaryMomentTerm w hw K half source)
      (centralBoundaryChannels K half)
      (centralBoundaryMomentSum_pos source_mem)
  have hweight :
      (0 : Q') ≤
        centralBoundaryWeight w K half selected :=
    centralBoundaryWeight_nonnegative_on
      hw selected hselected.1
  have htotal :
      (0 : Q') ≤
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half selected :=
    centralPositiveBoundaryTotalHalfAmplitude_nonnegative
      hw K half selected
  have hinner :
      (0 : Q') <
        centralHalfAmplitude w K half source selected *
          centralPositiveBoundaryTotalHalfAmplitude
            w hw K half selected := by
    exact q_right_pos_of_mul_pos_local
      hweight hselected.2
  exact ⟨hselected.1,
    q_left_pos_of_mul_pos_local htotal hinner⟩

/-- Concrete witness data saying every selected physical amplitude row has
one strictly positive boundary coordinate.  Entrywise nonnegativity is
already a theorem and is therefore not repeated as a field. -/
structure PhysicalHalfAmplitudePositiveCoordinateRows
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) : Type where
  positiveBoundary : EdgeLabelling → EdgeLabelling
  positiveBoundary_mem :
    ∀ source,
      source ∈ centralPositiveHalfStates w hw K half →
        positiveBoundary source ∈
          centralBoundaryChannels K half
  positiveValue :
    ∀ source,
      source ∈ centralPositiveHalfStates w hw K half →
        (0 : Q') <
          centralHalfAmplitude
            w K half source (positiveBoundary source)

namespace PhysicalHalfAmplitudePositiveCoordinateRows

/-- The concrete positive-coordinate data constructs the generic positive
prefix-row package with the literal amplitude as prefix. -/
def toPositivePrefixRows
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (rows :
      PhysicalHalfAmplitudePositiveCoordinateRows
        w hw K half) :
    PositivePrefixRows
      (centralHalfAmplitude w K half)
      (centralPositiveHalfStates w hw K half)
      (centralBoundaryChannels K half) where
  nonnegative := by
    intro source _ boundary _
    exact centralHalfAmplitude_nonnegative
      hw K half source boundary
  positiveMiddle := rows.positiveBoundary
  positiveMiddle_mem := rows.positiveBoundary_mem
  positiveValue := rows.positiveValue

end PhysicalHalfAmplitudePositiveCoordinateRows

/-- Every retained physical row has a computably selected positive boundary
coordinate.  This discharges the last prefix-row field automatically. -/
def physicalHalfAmplitudePositiveCoordinateRows
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    PhysicalHalfAmplitudePositiveCoordinateRows
      w hw K half where
  positiveBoundary :=
    centralPositiveBoundaryCoordinate w hw K half
  positiveBoundary_mem := by
    intro source source_mem
    exact
      (centralPositiveBoundaryCoordinate_mem_and_amplitude_pos
        source_mem).1
  positiveValue := by
    intro source source_mem
    exact
      (centralPositiveBoundaryCoordinate_mem_and_amplitude_pos
        source_mem).2

/-- The smoothed physical row `A P`, with no abstract prefix or carrier. -/
def centralHalfAmplitudeBoundaryAction
    (w : Q') (K half : Nat)
    (terminal : EdgeLabelling → EdgeLabelling → Q')
    (source boundary : EdgeLabelling) : Q' :=
  terminalSmoothedKernel
    (centralHalfAmplitude w K half)
    terminal
    (centralBoundaryChannels K half)
    source boundary

/-- The exact physical defect left by replacing the sparse identity terminal
by a positive smoothing terminal. -/
def centralHalfAmplitudeBoundaryActionDefect
    (w : Q') (K half : Nat)
    (terminal : EdgeLabelling → EdgeLabelling → Q')
    (source boundary : EdgeLabelling) : Q' :=
  Q'.abs
    (centralHalfAmplitude w K half source boundary +
      -centralHalfAmplitudeBoundaryAction
        w K half terminal source boundary)

/-! ## 4. Scale-family producer for the computed-floor route -/

/-- A physical boundary self-smoothing family.  Compared with the generic
computed-floor interface, the middle type, middle list, and prefix are now
fixed theorem-side.  The final field is exactly an `A - A P` bound. -/
structure MatchedPhysicalBoundarySelfSmoothingRows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) (diagonalOrder scale) 0
  terminal :
    ∀ _scale, EdgeLabelling → EdgeLabelling → Q'
  terminalCertificate :
    ∀ scale,
      FiniteCrossRatioDiameterCertificate
        (terminal scale)
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
  terminal_spread_square_le_split :
    ∀ scale,
      (terminalCertificate scale).spread *
          (terminalCertificate scale).spread ≤
        splitProjectiveCeiling
  action_defect :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ boundary,
          boundary ∈
              centralBoundaryChannels
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) →
            centralHalfAmplitudeBoundaryActionDefect
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale)
                (terminal scale) source boundary ≤
              physicalRelativeErrorTolerance *
                (terminalSmoothedFiniteFloor
                  (matchedAllSpinWeight_nonnegative
                    family coupling scale)
                  (matchedAllSpinCutoff family coupling scale)
                  (halfExtent scale)
                  (centralBoundaryChannels
                    (matchedAllSpinCutoff family coupling scale)
                    (halfExtent scale))
                  (centralHalfAmplitude
                    (matchedAllSpinWeight family coupling scale)
                    (matchedAllSpinCutoff family coupling scale)
                    (halfExtent scale))
                  (terminal scale)
                  ((physicalHalfAmplitudePositiveCoordinateRows
                    (matchedAllSpinWeight family coupling scale)
                    (matchedAllSpinWeight_nonnegative family coupling scale)
                    (matchedAllSpinCutoff family coupling scale)
                    (halfExtent scale)).toPositivePrefixRows)
                  (terminalCertificate scale)).floor

namespace MatchedPhysicalBoundarySelfSmoothingRows

/-- Boundary self-smoothing constructs the generic computed-floor package.
The ideal kernel is definitionally the finite action `A P`. -/
def toComputedFloorErrorRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalBoundarySelfSmoothingRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicalHalfAmplitudeComputedFloorErrorRows
      (fun _ => EdgeLabelling)
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  calibrated_harnack := data.calibrated_harnack
  middles := fun scale =>
    centralBoundaryChannels
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)
  prefixWeight := fun scale =>
    centralHalfAmplitude
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)
  terminal := data.terminal
  prefixRows := fun scale =>
    (physicalHalfAmplitudePositiveCoordinateRows
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)).toPositivePrefixRows
  terminalCertificate := data.terminalCertificate
  terminal_spread_square_le_split :=
    data.terminal_spread_square_le_split
  physical_error := by
    intro scale source source_mem boundary boundary_mem
    exact data.action_defect
      scale source source_mem boundary boundary_mem

end MatchedPhysicalBoundarySelfSmoothingRows

end YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction.centralBoundaryCode_injective_on_channels
#print axioms YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction.centralBoundaryCodeDelta_action_eqv
#print axioms YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction.centralHalfAmplitude_boundaryIdentityFactorization
#print axioms YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction.firstPositiveOr_mem_and_pos_of_sum_pos
#print axioms YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction.centralBoundaryMomentSum_pos
#print axioms YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction.centralPositiveBoundaryCoordinate_mem_and_amplitude_pos
#print axioms YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction.physicalHalfAmplitudePositiveCoordinateRows
#print axioms YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction.PhysicalHalfAmplitudePositiveCoordinateRows.toPositivePrefixRows
#print axioms YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction.MatchedPhysicalBoundarySelfSmoothingRows.toComputedFloorErrorRows
