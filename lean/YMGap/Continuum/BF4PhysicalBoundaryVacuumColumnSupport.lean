/-
# Support of the genuine BF4 vacuum boundary column

The retained lower-half carrier consists of the states whose normalized
physical reflected row has strictly positive marginal.  This file proves
that filtering to that carrier does not change the source-to-vacuum boundary
column: if the vacuum half-amplitude of a bounded source were positive, its
positive vacuum Gram summand would force the normalized row marginal to be
positive.  Therefore every removed source has exactly zero vacuum
half-amplitude.

The argument is finite, constructive, and valid for every cutoff and central
half-extent at nonnegative coupling.  It is a support theorem, not a spectral
or continuum estimate.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction
import YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne

namespace YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv

private theorem q_left_pos_of_mul_pos
    {left right : Q'}
    (hright : (0 : Q') ≤ right)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < left := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hrightNum : (0 : Int) ≤ right.num :=
    (Q'.zero_le_iff_num_nonneg right).mp hright
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hleftNonpos
  have hmulNonpos : left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg hleftNonpos hrightNum
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

private theorem q_nonpositive_of_not_positive
    {q : Q'} (hnot : ¬ (0 : Q') < q) :
    q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  exact Int.not_lt.mp (fun hnum =>
    hnot (CReal.pos_of_num_pos hnum))

private theorem listQSum_member_le_nonnegative_on
    {A : Type} (value : A → Q') : ∀ (items : List A) {item : A},
    (∀ x, x ∈ items → (0 : Q') ≤ value x) →
    item ∈ items →
      value item ≤ listQSum value items
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hnonnegative, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun x hx =>
              hnonnegative x (List.mem_cons_of_mem head hx)))
      · have ih := listQSum_member_le_nonnegative_on
          value tail
          (fun x hx =>
            hnonnegative x (List.mem_cons_of_mem head hx))
          htail
        have htailLe :
            listQSum value tail ≤
              value head + listQSum value tail := by
          exact Q'.le_trans' _
            (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail) (value head)
              (hnonnegative head List.mem_cons_self))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv
                (listQSum value tail) (value head)))
        exact Q'.le_trans' _ _ _ ih htailLe

private theorem listQSum_filter_eq_of_zero
    {A : Type} (value : A → Q') (predicate : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items →
        predicate item = false →
        value item ≈ 0) →
      listQSum value (items.filter predicate) ≈
        listQSum value items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _ _ _
            (listQSum_filter_eq_of_zero value predicate tail
              (fun item hitem =>
                hzero item (List.mem_cons_of_mem head hitem)))
            (Q'.eqv_symm
              (Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr'
                  (hzero head List.mem_cons_self hp)
                  (Q'.eqv_refl _))
                (Q'.eqv_of_eq (Q'.zero_add' _))))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (listQSum_filter_eq_of_zero value predicate tail
              (fun item hitem =>
                hzero item (List.mem_cons_of_mem head hitem)))

private theorem slabFaceFactorOn_zero_eqv_one
    (w : Q') (K : Nat) : ∀ ids : List Nat,
    slabFaceFactorOn w K zeroEdgeLabelling ids ≈ 1
  | [] => Q'.eqv_refl 1
  | _ :: tail => by
      unfold slabFaceFactorOn eliminateLinks
      have hcoefficient :
          coeffAt (heatKernelPacket K w) 0 ≈ 1 := by
        rw [coeffAt_heatKernelPacket (Nat.succ_pos K), coeffW_zero]
        exact Q'.eqv_refl 1
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hcoefficient)
          (Q'.mul_eqv_congr_left _ _ _
            (slabFaceFactorOn_zero_eqv_one w K tail)))
        (Q'.one_mul_eqv 1)

private theorem slabLinkMultiplicityProductOn_zero_eq_one
    (K extent : Nat) : ∀ links : List Z4Link,
    slabLinkMultiplicityProductOn K extent zeroEdgeLabelling links = 1
  | [] => rfl
  | head :: tail => by
      change
        slabExplicitLinkMultiplicity K extent zeroEdgeLabelling head *
            slabLinkMultiplicityProductOn K extent zeroEdgeLabelling tail = 1
      rw [slabExplicitLinkMultiplicity_zero_eq_one,
        slabLinkMultiplicityProductOn_zero_eq_one K extent tail,
        Nat.one_mul]

/-! ## 1. Positive vacuum amplitude forces a retained physical row -/

/-- The all-vacuum lower state and vacuum boundary have exact half-amplitude
one at every cutoff and central half-extent. -/
theorem centralHalfAmplitude_vacuum_eqv_one
    (w : Q') (K half : Nat) :
    centralHalfAmplitude
        w K half zeroEdgeLabelling zeroEdgeLabelling ≈ 1 := by
  unfold centralHalfAmplitude
  rw [assembleReflectedSlabLabelling_zero]
  unfold centralLowerFactor
  rw [slabLinkMultiplicityProductOn_zero_eq_one]
  exact Q'.eqv_trans _ (1 * Q'.ofNat 1) _
    (Q'.mul_eqv_congr_right _ _ _
      (slabFaceFactorOn_zero_eqv_one
        w K (centralLowerFaceIds half)))
    (by decide)

/-- A positive source-to-vacuum half-amplitude forces the source row to have
strictly positive normalized physical marginal. -/
theorem centralHalfAmplitude_vacuum_pos_implies_mem_positive
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates K half)
    (hamplitude :
      (0 : Q') <
        centralHalfAmplitude w K half source zeroEdgeLabelling) :
    source ∈ centralPositiveHalfStates w hw K half := by
  let vacuumAmplitude :=
    centralHalfAmplitude
      w K half zeroEdgeLabelling zeroEdgeLabelling
  have hvacuumAmplitudeNonnegative :
      (0 : Q') ≤ vacuumAmplitude :=
    centralHalfAmplitude_nonnegative
      hw K half zeroEdgeLabelling zeroEdgeLabelling
  have hvacuumWeightPos :
      (0 : Q') <
        centralBoundaryWeight w K half zeroEdgeLabelling := by
    apply q_left_pos_of_mul_pos
    · exact Q'.mul_nonneg _ _
        hvacuumAmplitudeNonnegative
        hvacuumAmplitudeNonnegative
    · exact centralVacuumBoundaryGramIntegrand_pos K half
  let gramTerm : EdgeLabelling → Q' := fun boundary =>
    centralBoundaryWeight w K half boundary *
      (centralHalfAmplitude w K half source boundary *
        centralHalfAmplitude
          w K half zeroEdgeLabelling boundary)
  have hselectedPos :
      (0 : Q') < gramTerm zeroEdgeLabelling := by
    unfold gramTerm vacuumAmplitude at *
    exact Q'.mul_pos hvacuumWeightPos
      (Q'.mul_pos hamplitude
        (centralVacuumHalfAmplitude_pos hw K half))
  have hselectedLe :
      gramTerm zeroEdgeLabelling ≤
        weightedGram
          (centralBoundaryChannels K half)
          (centralBoundaryWeight w K half)
          (centralHalfAmplitude w K half)
          source zeroEdgeLabelling := by
    unfold weightedGram
    apply listQSum_member_le_nonnegative_on gramTerm
    · intro boundary hboundary
      exact Q'.mul_nonneg _ _
        (centralBoundaryWeight_nonnegative_on
          hw boundary hboundary)
        (Q'.mul_nonneg _ _
          (centralHalfAmplitude_nonnegative
            hw K half source boundary)
          (centralHalfAmplitude_nonnegative
            hw K half zeroEdgeLabelling boundary))
    · exact zeroEdgeLabelling_mem_centralBoundaryChannels K half
  have hgramPos :
      (0 : Q') <
        weightedGram
          (centralBoundaryChannels K half)
          (centralBoundaryWeight w K half)
          (centralHalfAmplitude w K half)
          source zeroEdgeLabelling :=
    Q'.pos_of_lt_of_le hselectedPos hselectedLe
  have hrawEq := centralPhysicalReflectedKernel_eq_weightedGram
    w hsource (zeroEdgeLabelling_mem_centralHalfStates K half)
  have hrawPos :
      (0 : Q') <
        centralPhysicalReflectedKernel
          w K half source zeroEdgeLabelling :=
    Q'.pos_of_lt_of_le hgramPos (Q'.ge_of_eqv hrawEq)
  have hnormalizedPos :
      (0 : Q') <
        centralNormalizedPhysicalReflectedKernel
          w hw K half source zeroEdgeLabelling := by
    unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
    exact Q'.mul_pos hrawPos
      (Q'.recipPos_pos _
        (slabParametricKPhysicalPartition_pos
          hw K (centralExtent half)))
  have hentryLe :
      centralNormalizedPhysicalReflectedKernel
          w hw K half source zeroEdgeLabelling ≤
        centralPhysicalRowMarginal
          w hw K half source := by
    unfold centralPhysicalRowMarginal
    apply listQSum_member_le_nonnegative_on
      (centralNormalizedPhysicalReflectedKernel
        w hw K half source)
    · intro target _
      exact centralNormalizedPhysicalReflectedKernel_nonnegative
        hw K half source target
    · exact zeroEdgeLabelling_mem_centralHalfStates K half
  exact mem_centralPositiveHalfStates_iff.mpr
    ⟨hsource, Q'.pos_of_lt_of_le hnormalizedPos hentryLe⟩

/-- Every bounded source removed by the positive-row filter has exactly zero
source-to-vacuum half-amplitude. -/
theorem centralHalfAmplitude_vacuum_eqv_zero_of_not_mem_positive
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates K half)
    (hnot : source ∉ centralPositiveHalfStates w hw K half) :
    centralHalfAmplitude w K half source zeroEdgeLabelling ≈ 0 := by
  have hnonnegative := centralHalfAmplitude_nonnegative
    hw K half source zeroEdgeLabelling
  have hnotPositive :
      ¬ (0 : Q') <
        centralHalfAmplitude w K half source zeroEdgeLabelling := by
    intro hpositive
    exact hnot
      (centralHalfAmplitude_vacuum_pos_implies_mem_positive
        hsource hpositive)
  exact Q'.eqv_of_le_le
    (q_nonpositive_of_not_positive hnotPositive)
    hnonnegative

/-! ## 2. Filtering preserves the complete vacuum column -/

/-- The retained positive-source vacuum column is exactly the full bounded
source vacuum column for every finite cutoff and half-extent. -/
theorem centralBoundaryColumnMass_vacuum_eqv_full
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    centralBoundaryColumnMass
        w hw K half zeroEdgeLabelling ≈
      listQSum
        (fun source =>
          centralHalfAmplitude w K half source zeroEdgeLabelling)
        (centralHalfStates K half) := by
  unfold centralBoundaryColumnMass centralPositiveHalfStates
  apply listQSum_filter_eq_of_zero
  intro source hsource hfiltered
  apply centralHalfAmplitude_vacuum_eqv_zero_of_not_mem_positive
    hsource
  intro hpositiveMem
  have hrowPositive :=
    (mem_centralPositiveHalfStates_iff.mp hpositiveMem).2
  have hdecide :
      decide ((0 : Q') <
        centralPhysicalRowMarginal w hw K half source) = true :=
    decide_eq_true hrowPositive
  rw [hfiltered] at hdecide
  contradiction

end YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport.centralHalfAmplitude_vacuum_eqv_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport.centralHalfAmplitude_vacuum_pos_implies_mem_positive
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport.centralHalfAmplitude_vacuum_eqv_zero_of_not_mem_positive
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport.centralBoundaryColumnMass_vacuum_eqv_full
