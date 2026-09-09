/-
# Antisymmetric source-pair form of the cutoff-one centered coupling score

The marked-pair expansion has a mixed source weight: a coupling-one marked
margin mass on the first source and an actual-coupling mass on the second.
This module antisymmetrizes the two sources before any absolute value is
taken.  For source weights `m`, `a` and response `F`, the exact finite identity
is

  sum_xy (m(x)a(y)-a(x)m(y)) (F(x)-F(y))
    = 2 * sum_xy m(x)a(y)(F(x)-F(y)).

The oriented sum is proved equal to the existing centered one-replica moment
and, at cutoff one, to the marked occupied-face sum.

The module then uses binary occupation numbers.  If `n(x)` is the number of
occupied fine faces, the actual source mass is exactly

  a(x) = w^(3*n(x)) u(x),

and the antisymmetric mass determinant factors through the common
coupling-one product `u(x)u(y)` with scalar

  geomSum(w,3*n(x))*w^(3*n(y))
    - w^(3*n(x))*geomSum(w,3*n(y)).

When `n(y) <= n(x)`, that scalar contracts exactly to
`w^(3*n(y))*geomSum(w,3*(n(x)-n(y)))`; the opposite ordering gives its
negative.  Thus the mixed-coupling obstruction is reduced to one explicit
signed occupation-imbalance cofactor.

No support switch or estimate of the resulting cofactor is asserted here.
In particular this proves no cutoff- or volume-uniform covariance estimate,
continuum measure, OS/GNS reconstruction, Hamiltonian gap, or Yang--Mills
mass gap.

Constructive contract: finite sums, natural-number case splits, and exact
rational setoid algebra only; no `Classical`, choice, `native_decide`, proof
hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginMarkedPairDifference

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginBinaryHybrid
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginLocalInsertion
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginMarkedPairDifference
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOneReplica
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedMarginFactorization
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_mul_expand_local (left right factor : Q') :
    (left - right) * factor ≈
      left * factor - right * factor := by
  refine Q'.eqv_trans _
    (left * factor + (-right) * factor) _
    (Q'.add_mul_eqv left (-right) factor) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.neg_mul_eqv right factor)

private theorem reverse_sub_eqv_neg_local (left right : Q') :
    right - left ≈ -(left - right) := by
  change right + (-left) ≈ -(left + (-right))
  refine Q'.eqv_trans _ (-left + right) _
    (Q'.add_comm_eqv right (-left)) ?_
  refine Q'.eqv_trans _ (-left + (-(-right))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (-left) _ _
      (Q'.eqv_symm (Q'.neg_neg_eqv right))
  · exact Q'.eqv_symm (Q'.neg_add_eqv left (-right))

private theorem add_sub_right_cancel_local (left right : Q') :
    (left + right) - right ≈ left := by
  change (left + right) + (-right) ≈ left
  refine Q'.eqv_trans _
    (left + (right + (-right))) _
    (Q'.add_assoc_eqv left right (-right)) ?_
  refine Q'.eqv_trans _ (left + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left left _ _
      (Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv right (-right))
        (Q'.neg_add_self_eqv right))
  · exact Q'.eqv_of_eq (Q'.add_zero' left)

private theorem listQSum_cartesian_eq_nested_local
    {A B : Type} (value : A × B → Q')
    (left : List A) (right : List B) :
    listQSum value (cartesian left right) ≈
      listQSum
        (fun a => listQSum (fun b => value (a, b)) right)
        left := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value
      (fun a => right.map (fun b => (a, b))) left) ?_
  apply listQSum_congr
  intro a
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-! ## 1. Generic finite antisymmetrization -/

/-- Oriented pair term with a response difference. -/
def orientedPairDifferenceTerm {X : Type}
    (margin actual response : X → Q') (pair : X × X) : Q' :=
  margin pair.1 *
    (actual pair.2 * (response pair.1 - response pair.2))

/-- Antisymmetric determinant times the same response difference. -/
def antisymmetricPairDifferenceTerm {X : Type}
    (margin actual response : X → Q') (pair : X × X) : Q' :=
  (margin pair.1 * actual pair.2 -
      actual pair.1 * margin pair.2) *
    (response pair.1 - response pair.2)

/-- One antisymmetric term is the sum of the two opposite orientations. -/
theorem antisymmetricPairDifferenceTerm_eqv_oriented_add_swapped
    {X : Type} (margin actual response : X → Q')
    (pair : X × X) :
    antisymmetricPairDifferenceTerm margin actual response pair ≈
      orientedPairDifferenceTerm margin actual response pair +
        orientedPairDifferenceTerm margin actual response
          (pair.2, pair.1) := by
  let leftWeight := margin pair.1 * actual pair.2
  let rightWeight := actual pair.1 * margin pair.2
  let difference := response pair.1 - response pair.2
  have horiented :
      orientedPairDifferenceTerm margin actual response pair ≈
        leftWeight * difference := by
    unfold orientedPairDifferenceTerm leftWeight difference
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (margin pair.1) (actual pair.2)
        (response pair.1 - response pair.2))
  have hswapped :
      orientedPairDifferenceTerm margin actual response
          (pair.2, pair.1) ≈
        -(rightWeight * difference) := by
    unfold orientedPairDifferenceTerm rightWeight difference
    refine Q'.eqv_trans _
      ((margin pair.2 * actual pair.1) *
        (response pair.2 - response pair.1)) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (margin pair.2) (actual pair.1)
          (response pair.2 - response pair.1))
    refine Q'.eqv_trans _
      ((actual pair.1 * margin pair.2) *
        (response pair.2 - response pair.1)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_comm_eqv (margin pair.2) (actual pair.1))
    refine Q'.eqv_trans _
      ((actual pair.1 * margin pair.2) *
        (-(response pair.1 - response pair.2))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (reverse_sub_eqv_neg_local
          (response pair.1) (response pair.2))
    · exact Q'.mul_neg_eqv _ _
  unfold antisymmetricPairDifferenceTerm
  change (leftWeight - rightWeight) * difference ≈
    orientedPairDifferenceTerm margin actual response pair +
      orientedPairDifferenceTerm margin actual response (pair.2, pair.1)
  refine Q'.eqv_trans _
    (leftWeight * difference - rightWeight * difference) _
    (sub_mul_expand_local leftWeight rightWeight difference) ?_
  change leftWeight * difference + -(rightWeight * difference) ≈ _
  exact Q'.add_eqv_congr'
    (Q'.eqv_symm horiented) (Q'.eqv_symm hswapped)

/-- On a square finite carrier, antisymmetrization doubles the oriented
difference sum.  The second oriented copy is returned to the first by exact
finite Fubini. -/
theorem listQSum_antisymmetricPairDifference_eqv_two_oriented
    {X : Type} (states : List X)
    (margin actual response : X → Q') :
    listQSum
        (antisymmetricPairDifferenceTerm margin actual response)
        (cartesian states states) ≈
      (2 : Q') *
        listQSum
          (orientedPairDifferenceTerm margin actual response)
          (cartesian states states) := by
  let oriented := orientedPairDifferenceTerm margin actual response
  let swapped := fun pair : X × X => oriented (pair.2, pair.1)
  let pairs := cartesian states states
  have hswap : listQSum swapped pairs ≈ listQSum oriented pairs := by
    refine Q'.eqv_trans _
      (listQSum
        (fun x => listQSum (fun y => oriented (y, x)) states)
        states) _ ?_ ?_
    · exact listQSum_cartesian_eq_nested_local swapped states states
    refine Q'.eqv_trans _
      (listQSum
        (fun x => listQSum (fun y => oriented (x, y)) states)
        states) _ ?_ ?_
    · simpa only [oriented] using
        (listQSum_swap
          (fun x y =>
            orientedPairDifferenceTerm margin actual response (x, y))
          states states)
    · exact Q'.eqv_symm
        (listQSum_cartesian_eq_nested_local oriented states states)
  refine Q'.eqv_trans _
    (listQSum (fun pair => oriented pair + swapped pair) pairs) _ ?_ ?_
  · apply listQSum_congr
    intro pair
    exact antisymmetricPairDifferenceTerm_eqv_oriented_add_swapped
      margin actual response pair
  refine Q'.eqv_trans _
    (listQSum oriented pairs + listQSum swapped pairs) _ ?_ ?_
  · exact listQSum_add oriented swapped pairs
  refine Q'.eqv_trans _
    (listQSum oriented pairs + listQSum oriented pairs) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _ hswap
  · change listQSum oriented pairs + listQSum oriented pairs ≈
      (2 : Q') * listQSum oriented pairs
    refine Q'.eqv_trans _
      ((1 : Q') * listQSum oriented pairs +
        (1 : Q') * listQSum oriented pairs) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.eqv_symm (Q'.one_mul_eqv _))
        (Q'.eqv_symm (Q'.one_mul_eqv _))
    refine Q'.eqv_trans _
      (((1 : Q') + 1) * listQSum oriented pairs) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.add_mul_eqv 1 1 (listQSum oriented pairs))
    · exact Q'.mul_eqv_congr_right _ _ _
        (by decide : ((1 : Q') + 1) ≈ 2)

/-! ## 2. Actual source-pair sums and the centered moment -/

/-- A pair of fine physical source labellings. -/
abbrev FineCouplingPhysicalSourcePair := EdgeLabelling × EdgeLabelling

/-- The oriented source-pair term using the geometric margin mass, actual
mass, and one kernel-row event response. -/
def fineCouplingPhysicalOrientedSourcePairDifferenceTerm
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool)
    (pair : FineCouplingPhysicalSourcePair) : Q' :=
  orientedPairDifferenceTerm
    (fineCouplingPhysicalMarginTerm S)
    S.fine.physicalTerm
    (fun source => fineCouplingKernelOutputEventMass K source event)
    pair

/-- The complete oriented source-pair sum. -/
def fineCouplingPhysicalOrientedSourcePairDifferenceSum
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) : Q' :=
  listQSum
    (fineCouplingPhysicalOrientedSourcePairDifferenceTerm K event)
    (cartesian S.fine.physicalLabellings S.fine.physicalLabellings)

/-- The antisymmetric source-mass determinant term. -/
def fineCouplingPhysicalAntisymmetricSourcePairDifferenceTerm
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool)
    (pair : FineCouplingPhysicalSourcePair) : Q' :=
  antisymmetricPairDifferenceTerm
    (fineCouplingPhysicalMarginTerm S)
    S.fine.physicalTerm
    (fun source => fineCouplingKernelOutputEventMass K source event)
    pair

/-- The complete antisymmetric source-pair sum. -/
def fineCouplingPhysicalAntisymmetricSourcePairDifferenceSum
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) : Q' :=
  listQSum
    (fineCouplingPhysicalAntisymmetricSourcePairDifferenceTerm K event)
    (cartesian S.fine.physicalLabellings S.fine.physicalLabellings)

/-- The unmarked local-insertion sum is exactly the sum of the complete
source margin mass times its centered response. -/
theorem fineCouplingPhysicalCenteredMarginLocalInsertionSum_eqv_marginResponseSum
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalCenteredMarginLocalInsertionSum K event ≈
      listQSum
        (fun source =>
          fineCouplingPhysicalMarginTerm S source *
            fineCouplingPhysicalCenteredEventResponse K event source)
        S.fine.physicalLabellings := by
  unfold fineCouplingPhysicalCenteredMarginLocalInsertionSum
    fineCouplingPhysicalSourceFaceContributionCarrier
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fineCouplingPhysicalSourceFaceCenteredEventInsertion K event)
          ((slabPhysicalMarginFaceContributions S.fine.coupling source
            (slabPhysicalFaceEdges S.fine.extent)).map
              (fun contribution => (source, contribution))))
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  apply listQSum_congr
  intro source
  rw [listQSum_map]
  refine Q'.eqv_trans _
    (listQSum
      (fun contribution : PhysicalMarginFaceContribution =>
        (contribution.2 * fineUnitCouplingPhysicalTerm S source) *
          fineCouplingPhysicalCenteredEventResponse K event source)
      (slabPhysicalMarginFaceContributions S.fine.coupling source
        (slabPhysicalFaceEdges S.fine.extent))) _ ?_ ?_
  · apply listQSum_congr
    intro contribution
    unfold fineCouplingPhysicalSourceFaceCenteredEventInsertion
      fineCouplingPhysicalSourceFaceMarginRawMass
      fineCouplingPhysicalCenteredEventResponse
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    (listQSum
      (fun contribution : PhysicalMarginFaceContribution =>
        contribution.2 * fineUnitCouplingPhysicalTerm S source)
      (slabPhysicalMarginFaceContributions S.fine.coupling source
        (slabPhysicalFaceEdges S.fine.extent)) *
      fineCouplingPhysicalCenteredEventResponse K event source) _ ?_ ?_
  · exact listQSum_mul_right _ _ _
  · exact Q'.mul_eqv_congr_right _ _ _
      (fineCouplingPhysicalSourceFaceMarginRawMass_sum_eqv_marginTerm
        S source)

/-- The oriented source-pair difference sum is exactly the centered
one-replica score-event moment. -/
theorem fineCouplingPhysicalOrientedSourcePairDifferenceSum_eqv_centeredMoment
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalOrientedSourcePairDifferenceSum K event ≈
      fineCouplingPhysicalSourceKernelEventMoment K
        (fineCouplingPhysicalSourceCenteredMarginRawDebt S) event := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun other =>
            fineCouplingPhysicalMarginTerm S source *
              (S.fine.physicalTerm other *
                (fineCouplingKernelOutputEventMass K source event -
                  fineCouplingKernelOutputEventMass K other event)))
          S.fine.physicalLabellings)
      S.fine.physicalLabellings) _ ?_ ?_
  · unfold fineCouplingPhysicalOrientedSourcePairDifferenceSum
      fineCouplingPhysicalOrientedSourcePairDifferenceTerm
      orientedPairDifferenceTerm
    exact listQSum_cartesian_eq_nested_local _ _ _
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        fineCouplingPhysicalMarginTerm S source *
          listQSum
            (fun other =>
              S.fine.physicalTerm other *
                (fineCouplingKernelOutputEventMass K source event -
                  fineCouplingKernelOutputEventMass K other event))
            S.fine.physicalLabellings)
      S.fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact listQSum_mul_left
      (fineCouplingPhysicalMarginTerm S source)
      (fun other =>
        S.fine.physicalTerm other *
          (fineCouplingKernelOutputEventMass K source event -
            fineCouplingKernelOutputEventMass K other event))
      S.fine.physicalLabellings
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        fineCouplingPhysicalMarginTerm S source *
          fineCouplingPhysicalCenteredEventResponse K event source)
      S.fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (fineCouplingPhysicalCenteredEventResponse_eqv_sourceDifferenceSum
          K event source))
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (fineCouplingPhysicalCenteredMarginLocalInsertionSum_eqv_marginResponseSum
        K event))
    (Q'.eqv_symm
      (fineCouplingPhysicalSourceCenteredMarginEventMoment_eqv_localInsertions
        K event))

/-- Antisymmetrization doubles the genuine centered score-event moment. -/
theorem fineCouplingPhysicalAntisymmetricSourcePairDifferenceSum_eqv_two_centeredMoment
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalAntisymmetricSourcePairDifferenceSum K event ≈
      (2 : Q') *
        fineCouplingPhysicalSourceKernelEventMoment K
          (fineCouplingPhysicalSourceCenteredMarginRawDebt S) event := by
  refine Q'.eqv_trans _
    ((2 : Q') *
      fineCouplingPhysicalOrientedSourcePairDifferenceSum K event) _ ?_ ?_
  · unfold fineCouplingPhysicalAntisymmetricSourcePairDifferenceSum
      fineCouplingPhysicalAntisymmetricSourcePairDifferenceTerm
      fineCouplingPhysicalOrientedSourcePairDifferenceSum
      fineCouplingPhysicalOrientedSourcePairDifferenceTerm
    exact listQSum_antisymmetricPairDifference_eqv_two_oriented
      S.fine.physicalLabellings
      (fineCouplingPhysicalMarginTerm S)
      S.fine.physicalTerm
      (fun source => fineCouplingKernelOutputEventMass K source event)
  · exact Q'.mul_eqv_congr_left _ _ _
      (fineCouplingPhysicalOrientedSourcePairDifferenceSum_eqv_centeredMoment
        K event)

/-- At cutoff one, the antisymmetric source-pair sum is twice the marked
occupied-face difference sum. -/
theorem fineCouplingPhysicalAntisymmetricSourcePairDifferenceSum_eqv_two_marked
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    (K : S.FiniteSlabKernel) (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalAntisymmetricSourcePairDifferenceSum K event ≈
      (2 : Q') *
        fineCouplingPhysicalSymmetricMarkedSourcePairDifferenceSum
          K event := by
  exact Q'.eqv_trans _ _ _
    (fineCouplingPhysicalAntisymmetricSourcePairDifferenceSum_eqv_two_centeredMoment
      K event)
    (Q'.mul_eqv_congr_left _ _ _
      (fineCouplingPhysicalSourceCenteredMarginEventMoment_eqv_markedPairDifference
        hfineCutoff K event))

/-! ## 3. Binary occupation factorization of the source masses -/

/-- Number of occupied displayed fine faces in one source. -/
def fineCouplingPhysicalOccupiedFaceCount
    (S : SlabScalePair) (source : EdgeLabelling) : Nat :=
  (slabCutoffOneOccupiedFaces source
    (slabPhysicalFaceEdges S.fine.extent)).length

/-- At cutoff one, the total source Casimir exponent is three times its
occupied-face count. -/
theorem slabPhysicalCasimirExponent_eq_three_mul_occupiedFaceCount
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : EdgeLabelling) (hsource : source ∈ S.fine.physicalLabellings) :
    slabPhysicalCasimirExponent S.fine.extent source =
      3 * fineCouplingPhysicalOccupiedFaceCount S source := by
  unfold slabPhysicalCasimirExponent fineCouplingPhysicalOccupiedFaceCount
  apply slabPhysicalCasimirExponentOn_eq_three_mul_occupiedCount
  intro faceId hface
  exact finePhysicalFaceSpin_zero_or_one
    S hfineCutoff source hsource faceId hface

/-- At cutoff one, one actual fine source mass is its coupling-one mass
times exactly `w^(3*n)`. -/
theorem fineCouplingPhysicalTerm_eqv_occupiedPower_mul_unit
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : EdgeLabelling) (hsource : source ∈ S.fine.physicalLabellings) :
    S.fine.physicalTerm source ≈
      qpow S.fine.coupling
          (3 * fineCouplingPhysicalOccupiedFaceCount S source) *
        fineUnitCouplingPhysicalTerm S source := by
  have hbounded : source ∈ boundedEdgeLabellings S.fine.cutoff
      (slabPhysicalFaceEdges S.fine.extent) := by
    simpa only [SlabPhysicalData.physicalLabellings,
      SlabPhysicalData.faceEdges] using hsource
  have hfactor :=
    slabParametricKPhysicalTerm_eqv_power_mul_atOne
      S.fine.coupling S.fine.cutoff S.fine.extent source hbounded
  have hexponent :=
    slabPhysicalCasimirExponent_eq_three_mul_occupiedFaceCount
      S hfineCutoff source hsource
  rw [hexponent] at hfactor
  simpa only [SlabPhysicalData.physicalTerm,
    fineUnitCouplingPhysicalTerm] using hfactor

/-- At cutoff one, one geometric source-margin mass is its coupling-one
mass times exactly `geomSum(w,3*n)`. -/
theorem fineCouplingPhysicalMarginTerm_eqv_occupiedGeomSum_mul_unit
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : EdgeLabelling) (hsource : source ∈ S.fine.physicalLabellings) :
    fineCouplingPhysicalMarginTerm S source ≈
      geomSum S.fine.coupling
          (3 * fineCouplingPhysicalOccupiedFaceCount S source) *
        fineUnitCouplingPhysicalTerm S source := by
  unfold fineCouplingPhysicalMarginTerm
  rw [slabPhysicalCasimirExponent_eq_three_mul_occupiedFaceCount
    S hfineCutoff source hsource]
  exact Q'.eqv_refl _

/-! ## 4. The exact signed occupation-imbalance cofactor -/

/-- The scalar left after removing the common coupling-one product from the
antisymmetric source-mass determinant. -/
def fineCouplingPhysicalOccupationSkewCoefficient
    (S : SlabScalePair) (pair : FineCouplingPhysicalSourcePair) : Q' :=
  let leftExponent :=
    3 * fineCouplingPhysicalOccupiedFaceCount S pair.1
  let rightExponent :=
    3 * fineCouplingPhysicalOccupiedFaceCount S pair.2
  geomSum S.fine.coupling leftExponent *
      qpow S.fine.coupling rightExponent -
    qpow S.fine.coupling leftExponent *
      geomSum S.fine.coupling rightExponent

/-- The mixed-coupling antisymmetric determinant factors exactly into the
occupation-skew scalar and the common coupling-one pair product. -/
theorem fineCouplingPhysicalAntisymmetricMassDeterminant_eqv_occupationSkew
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (pair : FineCouplingPhysicalSourcePair)
    (hleft : pair.1 ∈ S.fine.physicalLabellings)
    (hright : pair.2 ∈ S.fine.physicalLabellings) :
    fineCouplingPhysicalMarginTerm S pair.1 *
          S.fine.physicalTerm pair.2 -
        S.fine.physicalTerm pair.1 *
          fineCouplingPhysicalMarginTerm S pair.2 ≈
      fineCouplingPhysicalOccupationSkewCoefficient S pair *
        (fineUnitCouplingPhysicalTerm S pair.1 *
          fineUnitCouplingPhysicalTerm S pair.2) := by
  let leftExponent :=
    3 * fineCouplingPhysicalOccupiedFaceCount S pair.1
  let rightExponent :=
    3 * fineCouplingPhysicalOccupiedFaceCount S pair.2
  refine Q'.eqv_trans _
    ((geomSum S.fine.coupling leftExponent *
          fineUnitCouplingPhysicalTerm S pair.1) *
        (qpow S.fine.coupling rightExponent *
          fineUnitCouplingPhysicalTerm S pair.2) -
      (qpow S.fine.coupling leftExponent *
          fineUnitCouplingPhysicalTerm S pair.1) *
        (geomSum S.fine.coupling rightExponent *
          fineUnitCouplingPhysicalTerm S pair.2)) _ ?_ ?_
  · apply sub_eqv_both_local
    · exact mul_eqv_both_local
        (fineCouplingPhysicalMarginTerm_eqv_occupiedGeomSum_mul_unit
          S hfineCutoff pair.1 hleft)
        (fineCouplingPhysicalTerm_eqv_occupiedPower_mul_unit
          S hfineCutoff pair.2 hright)
    · exact mul_eqv_both_local
        (fineCouplingPhysicalTerm_eqv_occupiedPower_mul_unit
          S hfineCutoff pair.1 hleft)
        (fineCouplingPhysicalMarginTerm_eqv_occupiedGeomSum_mul_unit
          S hfineCutoff pair.2 hright)
  let leftGeom := geomSum S.fine.coupling leftExponent
  let rightGeom := geomSum S.fine.coupling rightExponent
  let leftPower := qpow S.fine.coupling leftExponent
  let rightPower := qpow S.fine.coupling rightExponent
  let leftUnit := fineUnitCouplingPhysicalTerm S pair.1
  let rightUnit := fineUnitCouplingPhysicalTerm S pair.2
  change
    (leftGeom * leftUnit) * (rightPower * rightUnit) -
        (leftPower * leftUnit) * (rightGeom * rightUnit) ≈
      (leftGeom * rightPower - leftPower * rightGeom) *
        (leftUnit * rightUnit)
  refine Q'.eqv_trans _
    (leftGeom * rightPower * (leftUnit * rightUnit) -
      leftPower * rightGeom * (leftUnit * rightUnit)) _ ?_ ?_
  · apply sub_eqv_both_local <;> ring_qeqv
  exact Q'.eqv_symm
    (sub_mul_expand_local
      (leftGeom * rightPower) (leftPower * rightGeom)
      (leftUnit * rightUnit))

/-- Generic positive-orientation skew identity.  If the left exponent is
`base+extra`, the geometric/power determinant is exactly
`w^base * geomSum(w,extra)`. -/
theorem geomSum_qpow_skew_add_eqv
    (w : Q') (base extra : Nat) :
    geomSum w (base + extra) * qpow w base -
        qpow w (base + extra) * geomSum w base ≈
      qpow w base * geomSum w extra := by
  have hgeom : geomSum w (base + extra) ≈
      geomSum w extra + qpow w extra * geomSum w base := by
    rw [Nat.add_comm base extra]
    exact geomSum_add_eqv w extra base
  have hpower : qpow w (base + extra) ≈
      qpow w base * qpow w extra :=
    qpow_add w base extra
  refine Q'.eqv_trans _
    ((geomSum w extra + qpow w extra * geomSum w base) *
        qpow w base -
      (qpow w base * qpow w extra) * geomSum w base) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.mul_eqv_congr_right _ _ _ hgeom)
      (Q'.mul_eqv_congr_right _ _ _ hpower)
  let first := geomSum w extra
  let repeated := qpow w extra * geomSum w base
  let factor := qpow w base
  refine Q'.eqv_trans _
    ((first * factor + repeated * factor) -
      repeated * factor) _ ?_ ?_
  · apply sub_eqv_both_local
    · exact Q'.add_mul_eqv first repeated factor
    · simp only [repeated, factor]
      ring_qeqv
  refine Q'.eqv_trans _ (first * factor) _
    (add_sub_right_cancel_local (first * factor) (repeated * factor)) ?_
  exact Q'.mul_comm_eqv first factor

/-- If the right occupation count is no larger, the skew coefficient is a
nonnegative-orientation geometric quotient at the smaller heat exponent. -/
theorem fineCouplingPhysicalOccupationSkewCoefficient_eqv_of_right_le_left
    (S : SlabScalePair) (pair : FineCouplingPhysicalSourcePair)
    (hcount : fineCouplingPhysicalOccupiedFaceCount S pair.2 ≤
      fineCouplingPhysicalOccupiedFaceCount S pair.1) :
    fineCouplingPhysicalOccupationSkewCoefficient S pair ≈
      qpow S.fine.coupling
          (3 * fineCouplingPhysicalOccupiedFaceCount S pair.2) *
        geomSum S.fine.coupling
          (3 * (fineCouplingPhysicalOccupiedFaceCount S pair.1 -
            fineCouplingPhysicalOccupiedFaceCount S pair.2)) := by
  let leftCount := fineCouplingPhysicalOccupiedFaceCount S pair.1
  let rightCount := fineCouplingPhysicalOccupiedFaceCount S pair.2
  have hexponent :
      3 * leftCount = 3 * rightCount + 3 * (leftCount - rightCount) := by
    omega
  unfold fineCouplingPhysicalOccupationSkewCoefficient
  rw [hexponent]
  exact geomSum_qpow_skew_add_eqv
    S.fine.coupling (3 * rightCount) (3 * (leftCount - rightCount))

/-- If the left occupation count is no larger, the skew coefficient is the
negative of the same geometric quotient at the smaller heat exponent. -/
theorem fineCouplingPhysicalOccupationSkewCoefficient_eqv_neg_of_left_le_right
    (S : SlabScalePair) (pair : FineCouplingPhysicalSourcePair)
    (hcount : fineCouplingPhysicalOccupiedFaceCount S pair.1 ≤
      fineCouplingPhysicalOccupiedFaceCount S pair.2) :
    fineCouplingPhysicalOccupationSkewCoefficient S pair ≈
      -(qpow S.fine.coupling
          (3 * fineCouplingPhysicalOccupiedFaceCount S pair.1) *
        geomSum S.fine.coupling
          (3 * (fineCouplingPhysicalOccupiedFaceCount S pair.2 -
            fineCouplingPhysicalOccupiedFaceCount S pair.1))) := by
  let leftCount := fineCouplingPhysicalOccupiedFaceCount S pair.1
  let rightCount := fineCouplingPhysicalOccupiedFaceCount S pair.2
  have hexponent :
      3 * rightCount = 3 * leftCount + 3 * (rightCount - leftCount) := by
    omega
  have hpositive := geomSum_qpow_skew_add_eqv
    S.fine.coupling (3 * leftCount) (3 * (rightCount - leftCount))
  unfold fineCouplingPhysicalOccupationSkewCoefficient
  rw [hexponent]
  refine Q'.eqv_trans _
    (qpow S.fine.coupling
          (3 * leftCount + 3 * (rightCount - leftCount)) *
        geomSum S.fine.coupling (3 * leftCount) -
      geomSum S.fine.coupling
          (3 * leftCount + 3 * (rightCount - leftCount)) *
        qpow S.fine.coupling (3 * leftCount)) _ ?_ ?_
  · apply sub_eqv_both_local
    · exact Q'.mul_comm_eqv _ _
    · exact Q'.mul_comm_eqv _ _
  refine Q'.eqv_trans _
    (-(geomSum S.fine.coupling
          (3 * leftCount + 3 * (rightCount - leftCount)) *
        qpow S.fine.coupling (3 * leftCount) -
      qpow S.fine.coupling
          (3 * leftCount + 3 * (rightCount - leftCount)) *
        geomSum S.fine.coupling (3 * leftCount))) _ ?_ ?_
  · exact reverse_sub_eqv_neg_local _ _
  exact Q'.neg_eqv_congr _ _ hpositive

#print axioms orientedPairDifferenceTerm
#print axioms antisymmetricPairDifferenceTerm
#print axioms antisymmetricPairDifferenceTerm_eqv_oriented_add_swapped
#print axioms listQSum_antisymmetricPairDifference_eqv_two_oriented
#print axioms FineCouplingPhysicalSourcePair
#print axioms fineCouplingPhysicalOrientedSourcePairDifferenceTerm
#print axioms fineCouplingPhysicalOrientedSourcePairDifferenceSum
#print axioms fineCouplingPhysicalAntisymmetricSourcePairDifferenceTerm
#print axioms fineCouplingPhysicalAntisymmetricSourcePairDifferenceSum
#print axioms fineCouplingPhysicalCenteredMarginLocalInsertionSum_eqv_marginResponseSum
#print axioms fineCouplingPhysicalOrientedSourcePairDifferenceSum_eqv_centeredMoment
#print axioms fineCouplingPhysicalAntisymmetricSourcePairDifferenceSum_eqv_two_centeredMoment
#print axioms fineCouplingPhysicalAntisymmetricSourcePairDifferenceSum_eqv_two_marked
#print axioms fineCouplingPhysicalOccupiedFaceCount
#print axioms slabPhysicalCasimirExponent_eq_three_mul_occupiedFaceCount
#print axioms fineCouplingPhysicalTerm_eqv_occupiedPower_mul_unit
#print axioms fineCouplingPhysicalMarginTerm_eqv_occupiedGeomSum_mul_unit
#print axioms fineCouplingPhysicalOccupationSkewCoefficient
#print axioms fineCouplingPhysicalAntisymmetricMassDeterminant_eqv_occupationSkew
#print axioms geomSum_qpow_skew_add_eqv
#print axioms fineCouplingPhysicalOccupationSkewCoefficient_eqv_of_right_le_left
#print axioms fineCouplingPhysicalOccupationSkewCoefficient_eqv_neg_of_left_le_right

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
