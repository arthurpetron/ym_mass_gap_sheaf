/-
# The rank-one positive order of the reflected all-spin Taylor endpoint

The global alternating Taylor kernel is not positive at arbitrary finite
order.  Its first positive order is nevertheless exact and useful:

`geometricMehlerTaylorPartial left right 1`

contains only the constant kernel term.  Product Haar therefore factors it
as the product of the source and target five-Haar amplitudes.  This module
proves that factorization constructively and uses it to discharge the
partition, symmetry, and PSD fields of the pinned Taylor endpoint at order
one.  It does not claim the resulting rank-one endpoint has the strict
physical Perron rate or AF-uniform row comparison needed for the final
certificate.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
import YMGap.Continuum.BF4CompactActionCPOrder
import YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
import YMGap.Continuum.ThetaExponentConvexity

namespace YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact block factorization of monomial Haar moments -/

private theorem list_eq_nil_of_length_zero
    (values : List Nat) (h : values.length = 0) :
    values = [] := by
  cases values with
  | nil => rfl
  | cons head tail =>
      simp at h

theorem quaternionHaarPrefix_append_exact
    (sourceBlocks targetBlocks : Nat) :
    ∀ source target : List Nat,
      source.length = 4 * sourceBlocks →
      quaternionHaarPrefix
          (sourceBlocks + targetBlocks)
          (source ++ target) ≈
        quaternionHaarPrefix sourceBlocks source *
          quaternionHaarPrefix targetBlocks target
  | source, target, hsource => by
      induction sourceBlocks generalizing source with
      | zero =>
          have hnil : source = [] :=
            list_eq_nil_of_length_zero source
              (by simpa using hsource)
          subst source
          simp only [Nat.zero_add, List.nil_append,
            quaternionHaarPrefix]
          exact Q'.eqv_symm
            (Q'.one_mul_eqv _)
      | succ blocks induction =>
          cases source with
          | nil =>
              simp at hsource
          | cons x0 source1 =>
              cases source1 with
              | nil =>
                  simp only [List.length_cons,
                    List.length_nil] at hsource
                  omega
              | cons x1 source2 =>
                  cases source2 with
                  | nil =>
                      simp only [List.length_cons,
                        List.length_nil] at hsource
                      omega
                  | cons x2 source3 =>
                      cases source3 with
                      | nil =>
                          simp only [List.length_cons,
                            List.length_nil] at hsource
                          omega
                      | cons x3 tail =>
                          have htail :
                              tail.length = 4 * blocks := by
                            simp at hsource
                            omega
                          rw [show
                            blocks + 1 + targetBlocks =
                              (blocks + targetBlocks) + 1 by omega]
                          simp only [quaternionHaarPrefix,
                            exponentAt, List.getD_cons_zero,
                            List.getD_cons_succ,
                            List.drop_succ_cons,
                            List.drop_zero]
                          change
                            sphereMoment4 x0 x1 x2 x3 *
                                  quaternionHaarPrefix
                                    (blocks + targetBlocks)
                                    (tail ++ target) ≈
                              (sphereMoment4 x0 x1 x2 x3 *
                                  quaternionHaarPrefix
                                    blocks tail) *
                                quaternionHaarPrefix
                                  targetBlocks target
                          refine Q'.eqv_trans _
                            (sphereMoment4 x0 x1 x2 x3 *
                              (quaternionHaarPrefix blocks tail *
                                quaternionHaarPrefix
                                  targetBlocks target)) _
                            (Q'.mul_eqv_congr_left
                              (sphereMoment4 x0 x1 x2 x3) _ _
                              (induction tail htail)) ?_
                          exact Q'.eqv_symm
                            (Q'.mul_assoc_eqv
                              (sphereMoment4 x0 x1 x2 x3)
                              (quaternionHaarPrefix blocks tail)
                              (quaternionHaarPrefix
                                targetBlocks target))

theorem quaternionHaarMono_append_exact
    (sourceBlocks targetBlocks : Nat)
    (source target : List Nat)
    (hsource : source.length = 4 * sourceBlocks)
    (htarget : target.length = 4 * targetBlocks) :
    quaternionHaarMono
        (sourceBlocks + targetBlocks)
        (source ++ target) ≈
      quaternionHaarMono sourceBlocks source *
        quaternionHaarMono targetBlocks target := by
  have htotal :
      (source ++ target).length =
        4 * (sourceBlocks + targetBlocks) := by
    simp [hsource, htarget]
    omega
  have hsourceTail :
      allZero (source.drop (4 * sourceBlocks)) = true := by
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  have htargetTail :
      allZero (target.drop (4 * targetBlocks)) = true := by
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  have htotalTail :
      allZero
        ((source ++ target).drop
          (4 * (sourceBlocks + targetBlocks))) = true := by
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  unfold quaternionHaarMono
  rw [if_pos htotalTail, if_pos hsourceTail, if_pos htargetTail]
  exact quaternionHaarPrefix_append_exact
    sourceBlocks targetBlocks source target hsource

/-! ## 2. Source/target polynomial product Haar factorization -/

private theorem monoMul_replicate_append
    (source target : List Nat) :
    monoMul source
        (List.replicate source.length 0 ++ target) =
      source ++ target := by
  induction source with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.length_cons, List.replicate_succ,
        List.cons_append, monoMul, Nat.add_zero,
        induction]

theorem monoMul_shift_exact
    (source target : List Nat)
    (hsource : source.length = 20) :
    monoMul source
        (List.replicate 20 0 ++ target) =
      source ++ target := by
  rw [← hsource]
  exact monoMul_replicate_append source target

/-- The exact five-Haar amplitude of one geometric BF4 boundary state. -/
def geometricZerothHalfAmplitude
    (state : EdgeLabelling) : Q' :=
  quaternionHaar 5
    (sourceGeometricWavefunction state)

private theorem sourceGeometricWavefunction_term_length
    (state : EdgeLabelling) :
    ∀ term,
      term ∈ sourceGeometricWavefunction state →
        term.1.length = 20 := by
  intro term hterm
  unfold sourceGeometricWavefunction
    geometricBF4WavefunctionOfState
    geometricBF4Wavefunction
    integrateEighteenChords at hterm
  rcases List.mem_map.mp hterm with
    ⟨source, _, hsource⟩
  subst term
  exact retainedFiveMonomial_length source.1

private theorem shifted_target_term
    (state : EdgeLabelling) :
    ∀ term,
      term ∈ sourceGeometricWavefunction state →
        (List.replicate 20 0 ++ term.1, term.2) ∈
          targetGeometricWavefunction state := by
  intro term hterm
  unfold targetGeometricWavefunction shiftPolynomial
  exact List.mem_map.mpr
    ⟨term, hterm, rfl⟩

/- The polynomial-level factorization is proved below by two finite-list
inductions. -/

private theorem quaternionHaar_single_source_shift_factorization
    (source : RatTerm)
    (hsource : source.1.length = 20) :
    ∀ target : RatPoly,
      (∀ term, term ∈ target → term.1.length = 20) →
      quaternionHaar 10
          (polyMul [source] (shiftPolynomial 20 target)) ≈
        (source.2 * quaternionHaarMono 5 source.1) *
          quaternionHaar 5 target
  | [], _ => by
      exact Q'.eqv_symm
        (Q'.mul_zero_eqv
          (source.2 * quaternionHaarMono 5 source.1))
  | target :: rest, htarget => by
      have htargetLength : target.1.length = 20 :=
        htarget target (by simp)
      have hrest :
          ∀ term, term ∈ rest → term.1.length = 20 := by
        intro term hterm
        exact htarget term (by simp [hterm])
      have hmono :
          monoMul source.1
              (List.replicate 20 0 ++ target.1) =
            source.1 ++ target.1 :=
        monoMul_shift_exact source.1 target.1 hsource
      change
        (source.2 * target.2) *
              quaternionHaarMono 10
                (monoMul source.1
                  (List.replicate 20 0 ++ target.1)) +
            quaternionHaar 10
              (polyMul [source]
                (shiftPolynomial 20 rest)) ≈
          (source.2 * quaternionHaarMono 5 source.1) *
            (target.2 * quaternionHaarMono 5 target.1 +
              quaternionHaar 5 rest)
      rw [hmono]
      refine Q'.eqv_trans _
        ((source.2 * quaternionHaarMono 5 source.1) *
              (target.2 * quaternionHaarMono 5 target.1) +
            (source.2 * quaternionHaarMono 5 source.1) *
              quaternionHaar 5 rest) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left
              (source.2 * target.2) _ _
              (quaternionHaarMono_append_exact
                5 5 source.1 target.1 hsource htargetLength))
            (q_mul4_swap
              source.2 target.2
              (quaternionHaarMono 5 source.1)
              (quaternionHaarMono 5 target.1)))
          (quaternionHaar_single_source_shift_factorization
            source hsource rest hrest)
      · exact Q'.eqv_symm
          (Q'.mul_add_eqv
            (source.2 * quaternionHaarMono 5 source.1)
            (target.2 * quaternionHaarMono 5 target.1)
            (quaternionHaar 5 rest))

/-- Exact source/target factorization for the ten-fold product Haar
functional.  No positivity or convergence assumption enters: the twenty
source coordinates and twenty shifted target coordinates occupy disjoint
five-holonomy blocks. -/
theorem tenfoldHaar_source_target_factorization :
    ∀ source target : RatPoly,
      (∀ term, term ∈ source → term.1.length = 20) →
      (∀ term, term ∈ target → term.1.length = 20) →
      quaternionHaar 10
          (polyMul source (shiftPolynomial 20 target)) ≈
        quaternionHaar 5 source * quaternionHaar 5 target
  | [], target, _, _ => by
      exact Q'.eqv_symm
        (Q'.zero_mul_eqv (quaternionHaar 5 target))
  | source :: rest, target, hsource, htarget => by
      have hsourceLength : source.1.length = 20 :=
        hsource source (by simp)
      have hrest :
          ∀ term, term ∈ rest → term.1.length = 20 := by
        intro term hterm
        exact hsource term (by simp [hterm])
      rw [show
        polyMul (source :: rest) (shiftPolynomial 20 target) =
          polyMul [source] (shiftPolynomial 20 target) ++
            polyMul rest (shiftPolynomial 20 target) by
          simp [polyMul]]
      change
        quaternionHaar 10
            (polyMul [source] (shiftPolynomial 20 target) ++
              polyMul rest (shiftPolynomial 20 target)) ≈
          (source.2 * quaternionHaarMono 5 source.1 +
              quaternionHaar 5 rest) *
            quaternionHaar 5 target
      refine Q'.eqv_trans _
        (quaternionHaar 10
              (polyMul [source] (shiftPolynomial 20 target)) +
            quaternionHaar 10
              (polyMul rest (shiftPolynomial 20 target))) _ ?_ ?_
      · exact quaternionHaar_append 10
          (polyMul [source] (shiftPolynomial 20 target))
          (polyMul rest (shiftPolynomial 20 target))
      · refine Q'.eqv_trans _
          ((source.2 * quaternionHaarMono 5 source.1) *
                quaternionHaar 5 target +
              quaternionHaar 5 rest *
                quaternionHaar 5 target) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (quaternionHaar_single_source_shift_factorization
              source hsourceLength target htarget)
            (tenfoldHaar_source_target_factorization
              rest target hrest htarget)
        · exact Q'.eqv_symm
            (Q'.add_mul_eqv
              (source.2 * quaternionHaarMono 5 source.1)
              (quaternionHaar 5 rest)
              (quaternionHaar 5 target))

/-! ## 3. The order-one Taylor endpoint is exactly rank one -/

/-- The one-term global Taylor endpoint contains only the constant kernel,
so product Haar splits it into the two exact reflected half-amplitudes. -/
theorem geometricMehlerTaylorPartial_one_rankOne
    (left right : EdgeLabelling) :
    geometricMehlerTaylorPartial left right 1 ≈
      geometricZerothHalfAmplitude left *
        geometricZerothHalfAmplitude right := by
  change
    0 +
        quaternionHaar 10
          (polyMul
            (polyMul
              (sourceGeometricWavefunction left)
              (targetGeometricWavefunction right))
            polyOne) ≈
      quaternionHaar 5
          (sourceGeometricWavefunction left) *
        quaternionHaar 5
          (sourceGeometricWavefunction right)
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul
        (polyMul
          (sourceGeometricWavefunction left)
          (targetGeometricWavefunction right))
        polyOne)) _
    (QPoly.q_zero_add_eqv _) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul
        (sourceGeometricWavefunction left)
        (targetGeometricWavefunction right))) _
    (quaternionHaar_polyMul_one_right 10 _) ?_
  exact tenfoldHaar_source_target_factorization
    (sourceGeometricWavefunction left)
    (sourceGeometricWavefunction right)
    (sourceGeometricWavefunction_term_length left)
    (sourceGeometricWavefunction_term_length right)

/-- At the zero boundary labelling the retained spin network is the constant
function, so its exact five-Haar half-amplitude is one. -/
theorem geometricZerothHalfAmplitude_vacuum :
    geometricZerothHalfAmplitude (fun _ => 0) ≈ 1 := by
  unfold geometricZerothHalfAmplitude
    sourceGeometricWavefunction
    geometricBF4WavefunctionOfState
    geometricBF4Wavefunction
    integrateEighteenChords
  decide

/-- The pinned order-one Taylor partition is exactly one. -/
theorem geometricTaylorVacuumPartition_one :
    geometricTaylorVacuumPartition 1 ≈ 1 := by
  refine Q'.eqv_trans _
    (geometricZerothHalfAmplitude (fun _ => 0) *
      geometricZerothHalfAmplitude (fun _ => 0)) _
    (geometricMehlerTaylorPartial_one_rankOne
      (fun _ => 0) (fun _ => 0)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_trans _
      (1 * geometricZerothHalfAmplitude (fun _ => 0)) _
      (Q'.mul_eqv_congr_right _ _ _
        geometricZerothHalfAmplitude_vacuum)
      (Q'.mul_eqv_congr_left 1 _ _
        geometricZerothHalfAmplitude_vacuum))
    (Q'.one_mul_eqv 1)

/-- In particular the pinned order-one Taylor partition is strictly
positive, with no analytic positivity hypothesis. -/
theorem geometricTaylorVacuumPartition_one_pos :
    (0 : Q') < geometricTaylorVacuumPartition 1 := by
  exact Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv geometricTaylorVacuumPartition_one)

/-! ## 4. Normalization, symmetry, and finite reflection positivity -/

private theorem divPos_eqv_self_of_den_eqv_one
    (value denominator : Q')
    (hdenominator : (0 : Q') < denominator)
    (hone : denominator ≈ 1) :
    Q'.divPos value denominator hdenominator ≈ value := by
  apply Q'.mul_left_cancel_of_pos hdenominator
  refine Q'.eqv_trans _
    value
    (denominator * value) ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv denominator
        (Q'.divPos value denominator hdenominator))
      (Q'.divPos_mul_eqv
        value denominator hdenominator)
  · exact Q'.eqv_symm
      (Q'.eqv_trans _
        (1 * value) _
        (Q'.mul_eqv_congr_right
          denominator 1 value hone)
        (Q'.one_mul_eqv value))

/-- The normalized pinned order-one entry is the same rank-one product:
normalization by its exact unit partition changes nothing. -/
theorem normalized_geometricMehlerTaylorPartial_one_rankOne
    (left right : EdgeLabelling) :
    Q'.divPos
        (geometricMehlerTaylorPartial left right 1)
        (geometricTaylorVacuumPartition 1)
        geometricTaylorVacuumPartition_one_pos ≈
      geometricZerothHalfAmplitude left *
        geometricZerothHalfAmplitude right := by
  exact Q'.eqv_trans _ _ _
    (divPos_eqv_self_of_den_eqv_one
      (geometricMehlerTaylorPartial left right 1)
      (geometricTaylorVacuumPartition 1)
      geometricTaylorVacuumPartition_one_pos
      geometricTaylorVacuumPartition_one)
    (geometricMehlerTaylorPartial_one_rankOne left right)

/-- Symmetry of the pinned order-one numerator is a theorem, not input
data. -/
theorem geometricMehlerTaylorPartial_one_symmetric
    (left right : EdgeLabelling) :
    geometricMehlerTaylorPartial left right 1 ≈
      geometricMehlerTaylorPartial right left 1 := by
  exact Q'.eqv_trans _
    (geometricZerothHalfAmplitude left *
      geometricZerothHalfAmplitude right) _
    (geometricMehlerTaylorPartial_one_rankOne left right)
    (Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv
        (geometricZerothHalfAmplitude left)
        (geometricZerothHalfAmplitude right))
      (Q'.eqv_symm
        (geometricMehlerTaylorPartial_one_rankOne right left)))

/-- Any finite rank-one kernel `a(x)a(y)` is positive semidefinite.  The
proof passes through the constructive finite weighted-Gram SOS theorem with
one unit-weight channel. -/
theorem finiteJointQuadratic_rankOne_nonnegative
    {State : Type}
    (states : List State)
    (observable amplitude : State → Q') :
    (0 : Q') ≤
      finiteJointQuadratic states observable
        (fun left right =>
          amplitude left * amplitude right) := by
  have hgram :
      (0 : Q') ≤
        weightedGramQuadratic
          states [()]
          (fun _ => 1)
          (fun state _ => amplitude state)
          observable :=
    weightedGramQuadratic_nonnegative
      states [()]
      (fun _ => 1)
      (fun state _ => amplitude state)
      observable
      (by
        intro channel _
        cases channel
        exact Q'.zero_le_one)
  have heq :
      weightedGramQuadratic
          states [()]
          (fun _ => 1)
          (fun state _ => amplitude state)
          observable ≈
        finiteJointQuadratic states observable
          (fun left right =>
            amplitude left * amplitude right) := by
    unfold weightedGramQuadratic
      weightedGram finiteJointQuadratic
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    apply Q'.mul_eqv_congr_left
    exact Q'.eqv_trans _ _ _
      (QPoly.q_add_zero_eqv
        (1 * (amplitude left * amplitude right)))
      (Q'.one_mul_eqv
        (amplitude left * amplitude right))
  exact Q'.le_trans' _ _ _ hgram
    (Q'.le_of_eqv heq)

/-- The normalized pinned order-one Taylor endpoint is positive
semidefinite on every finite carrier, hence in particular on the exact
positive-row BF4 carrier. -/
theorem normalized_geometricMehlerTaylorPartial_one_quadratic_nonnegative
    (states : List EdgeLabelling)
    (observable : EdgeLabelling → Q') :
    (0 : Q') ≤
      finiteJointQuadratic states observable
        (fun left right =>
          Q'.divPos
            (geometricMehlerTaylorPartial left right 1)
            (geometricTaylorVacuumPartition 1)
            geometricTaylorVacuumPartition_one_pos) := by
  have hrank :
      (0 : Q') ≤
        finiteJointQuadratic states observable
          (fun left right =>
            geometricZerothHalfAmplitude left *
              geometricZerothHalfAmplitude right) :=
    finiteJointQuadratic_rankOne_nonnegative
      states observable geometricZerothHalfAmplitude
  exact Q'.le_trans' _ _ _ hrank
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (finiteJointQuadratic_joint_eqv
          states observable
          (fun left right =>
            Q'.divPos
              (geometricMehlerTaylorPartial left right 1)
              (geometricTaylorVacuumPartition 1)
              geometricTaylorVacuumPartition_one_pos)
          (fun left right =>
            geometricZerothHalfAmplitude left *
              geometricZerothHalfAmplitude right)
          (by
            intro left _ right _
            exact
              normalized_geometricMehlerTaylorPartial_one_rankOne
                left right))))

/-! ## 5. A physical-marginal floor supplies the Rayleigh datum -/

/-- Exact squared `L²` size, with respect to counting measure on a finite
carrier, of the five-Haar order-zero half-amplitude. -/
def rankOneAmplitudeL2Sum
    (states : List EdgeLabelling) : Q' :=
  listQSum
    (fun state =>
      geometricZerothHalfAmplitude state *
        geometricZerothHalfAmplitude state)
    states

theorem rankOneAmplitudeL2Sum_nonnegative
    (states : List EdgeLabelling) :
    (0 : Q') ≤ rankOneAmplitudeL2Sum states := by
  unfold rankOneAmplitudeL2Sum
  apply listQSum_nonnegative_on
  intro state _
  exact
    YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
      (geometricZerothHalfAmplitude state)

/-- A finite rank-one quadratic is exactly the square of the scalar
pairing with its half-amplitude. -/
theorem finiteJointQuadratic_rankOne_eq_square
    {State : Type}
    (states : List State)
    (observable amplitude : State → Q') :
    finiteJointQuadratic states observable
        (fun left right =>
          amplitude left * amplitude right) ≈
      listQSum
          (fun state => observable state * amplitude state)
          states *
        listQSum
          (fun state => observable state * amplitude state)
          states := by
  unfold finiteJointQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            (observable left * amplitude left) *
              (observable right * amplitude right))
          states)
      states) _ ?_ ?_
  · apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    exact q_mul4_swap
      (observable left) (observable right)
      (amplitude left) (amplitude right)
  · exact listQSum_product
      (fun state => observable state * amplitude state)
      (fun state => observable state * amplitude state)
      states states

/-- Constructive finite-list Cauchy--Schwarz on the exact BF4 labelling
carrier.  The proof transports the repository's indexed Lagrange identity
through the explicit `supportLabel` enumeration. -/
theorem edgeLabelling_listQSum_cauchy_schwarz
    (states : List EdgeLabelling)
    (left right : EdgeLabelling → Q') :
    listQSum (fun state => left state * right state) states *
          listQSum (fun state => left state * right state) states ≤
      listQSum (fun state => left state * left state) states *
        listQSum (fun state => right state * right state) states := by
  have hcs :=
    YMGap.Continuum.ThetaExponentConvexity.cauchy_schwarz
      (fun index =>
        left
          (YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.supportLabel
            states index))
      (fun index =>
        right
          (YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.supportLabel
            states index))
      states.length
  have hcross :=
    fsum_supportLabel_eq_listQSum
      (fun state => left state * right state) states
  have hleft :=
    fsum_supportLabel_eq_listQSum
      (fun state => left state * left state) states
  have hright :=
    fsum_supportLabel_eq_listQSum
      (fun state => right state * right state) states
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hcross)
        (Q'.mul_eqv_congr_left _ _ _ hcross))) ?_
  exact Q'.le_trans' _ _ _ hcs
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hleft)
        (Q'.mul_eqv_congr_left _ _ _ hright)))

/-- Located minimum of `value` on the displayed nonempty list. -/
def rankOneFiniteMin
    {State : Type} (value : State → Q') :
    State → List State → Q'
  | first, [] => value first
  | first, next :: rest =>
      Q'.min' (value first)
        (rankOneFiniteMin value next rest)

theorem rankOneFiniteMin_le_of_mem
    {State : Type} (value : State → Q') :
    ∀ first rest state,
      state ∈ first :: rest →
        rankOneFiniteMin value first rest ≤ value state
  | first, [], state, hstate => by
      rcases List.mem_cons.mp hstate with rfl | htail
      · exact Q'.le_refl' _
      · nomatch htail
  | first, next :: rest, state, hstate => by
      rcases List.mem_cons.mp hstate with rfl | htail
      · exact Q'.min_le_left' _ _
      · exact Q'.le_trans' _ _ _
          (Q'.min_le_right' _ _)
          (rankOneFiniteMin_le_of_mem
            value next rest state htail)

theorem rankOneFiniteMin_pos
    {State : Type} (value : State → Q') :
    ∀ first rest,
      (∀ state,
        state ∈ first :: rest →
          (0 : Q') < value state) →
      (0 : Q') <
        rankOneFiniteMin value first rest
  | first, [], hpos =>
      hpos first List.mem_cons_self
  | first, next :: rest, hpos => by
      have hfirst :
          (0 : Q') < value first :=
        hpos first List.mem_cons_self
      have htail :
          (0 : Q') <
            rankOneFiniteMin value next rest :=
        rankOneFiniteMin_pos value next rest
          (fun state hstate =>
            hpos state
              (List.mem_cons_of_mem first hstate))
      unfold rankOneFiniteMin
      unfold Q'.min'
      by_cases hle :
          value first ≤
            rankOneFiniteMin value next rest
      · rw [if_pos hle]
        exact hfirst
      · rw [if_neg hle]
        exact htail

/-- Generic finite positive-floor package.  Its inhabitant below is obtained
by recursion on a supplied nonempty list, so no choice principle is used. -/
structure PositiveFiniteFloor
    {State : Type}
    (states : List State)
    (value : State → Q') : Type where
  floor : Q'
  floor_pos : (0 : Q') < floor
  floor_le :
    ∀ state, state ∈ states → floor ≤ value state

def positiveFiniteFloorOfNonempty
    {State : Type}
    (states : List State)
    (value : State → Q')
    (hne : states ≠ [])
    (hpos :
      ∀ state, state ∈ states →
        (0 : Q') < value state) :
    PositiveFiniteFloor states value := by
  cases states with
  | nil =>
      exact False.elim (hne rfl)
  | cons first rest =>
      exact
        { floor := rankOneFiniteMin value first rest
          floor_pos :=
            rankOneFiniteMin_pos
              value first rest hpos
          floor_le := by
            intro state hstate
            exact rankOneFiniteMin_le_of_mem
              value first rest state hstate }

/-- Intermediate package comparing counting measure with the BF4 stationary
law: a strictly positive lower bound for every retained row marginal.  The
next definition constructs it from the located finite minimum; it is not an
additional analytic assumption. -/
structure RankOnePhysicalMarginalFloorData
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) : Type where
  floor : Q'
  floor_pos : (0 : Q') < floor
  floor_le :
    ∀ state,
      state ∈ centralPositiveHalfStates
        w hw K halfExtent →
      floor ≤
        centralPhysicalRowMarginal
          w hw K halfExtent state

/-- The retained carrier was defined by strict row positivity, and it is
constructively nonempty.  Its exact finite minimum therefore supplies the
physical marginal-floor datum without any additional hypothesis. -/
def centralPositivePhysicalMarginalFloorData
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) :
    RankOnePhysicalMarginalFloorData
      w hw K halfExtent := by
  let states :=
    centralPositiveHalfStates
      w hw K halfExtent
  let value :=
    centralPhysicalRowMarginal
      w hw K halfExtent
  have hne : states ≠ [] :=
    centralPositiveHalfStates_ne_nil
      w hw K halfExtent
  have hpos :
      ∀ state, state ∈ states →
        (0 : Q') < value state := by
    intro state hstate
    exact
      (mem_centralPositiveHalfStates_iff.mp
        hstate).2
  let finiteFloor :=
    positiveFiniteFloorOfNonempty
      states value hne hpos
  exact
    { floor := finiteFloor.floor
      floor_pos := finiteFloor.floor_pos
      floor_le := finiteFloor.floor_le }

/-- The marginal floor converts the unweighted coefficient square into the
exact physical weighted inner product. -/
theorem marginalFloor_mul_unweightedSquare_le_physicalInner
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (floorData :
      RankOnePhysicalMarginalFloorData
        w hw K halfExtent)
    (observable : EdgeLabelling → Q') :
    floorData.floor *
        listQSum
          (fun state => observable state * observable state)
          (centralPositiveHalfStates
            w hw K halfExtent) ≤
      centralPhysicalWeightedInner
        w hw K halfExtent observable observable := by
  unfold centralPhysicalWeightedInner
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (listQSum_mul_left
        floorData.floor
        (fun state => observable state * observable state)
        (centralPositiveHalfStates
          w hw K halfExtent))) ?_
  apply listQSum_mono
  intro state hstate
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (floorData.floor_le state hstate)
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
      (observable state))

/-- Consequently the unweighted coefficient square is bounded by physical
`L²`, divided only by the explicit positive marginal floor. -/
theorem unweightedSquare_le_divPos_physicalInner
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (floorData :
      RankOnePhysicalMarginalFloorData
        w hw K halfExtent)
    (observable : EdgeLabelling → Q') :
    listQSum
          (fun state => observable state * observable state)
          (centralPositiveHalfStates
            w hw K halfExtent) ≤
      Q'.divPos
        (centralPhysicalWeightedInner
          w hw K halfExtent observable observable)
        floorData.floor floorData.floor_pos := by
  apply Q'.le_divPos_of_mul_le
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (Q'.mul_comm_eqv
        floorData.floor
        (listQSum
          (fun state => observable state * observable state)
          (centralPositiveHalfStates
            w hw K halfExtent)))) ?_
  exact
    marginalFloor_mul_unweightedSquare_le_physicalInner
      floorData observable

private theorem amplitude_mul_physicalDiv_eqv_rate_mul_physical
    (amplitudeSquare physical floor : Q')
    (hfloor : (0 : Q') < floor) :
    amplitudeSquare *
        Q'.divPos physical floor hfloor ≈
      Q'.divPos amplitudeSquare floor hfloor *
        physical := by
  unfold Q'.divPos
  refine Q'.eqv_trans _
    ((amplitudeSquare * physical) *
      Q'.recipPos floor hfloor) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        amplitudeSquare physical
        (Q'.recipPos floor hfloor))
  · refine Q'.eqv_trans _
      (Q'.recipPos floor hfloor *
        (amplitudeSquare * physical)) _
      (Q'.mul_comm_eqv
        (amplitudeSquare * physical)
        (Q'.recipPos floor hfloor)) ?_
    refine Q'.eqv_trans _
      ((Q'.recipPos floor hfloor * amplitudeSquare) *
        physical) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (Q'.recipPos floor hfloor)
          amplitudeSquare physical)) ?_
    exact Q'.mul_eqv_congr_right _ _ physical
      (Q'.mul_comm_eqv
        (Q'.recipPos floor hfloor)
        amplitudeSquare)

/-! ## 6. Reduced spectral input and the pinned endpoint inhabitant -/

/-- After the algebraic order-one discharge, the sole residual spectral
input is the physical-mean-zero Rayleigh estimate.  It is kept explicit
rather than hidden in a larger endpoint structure. -/
structure RankOneTaylorPhysicalRateData
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) : Type where
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  normalized_meanZero_quadratic :
    ∀ observable,
      CentralPhysicalMeanZero
        w hw K halfExtent observable →
        Q'.abs
            (finiteJointQuadratic
              (centralPositiveHalfStates
                w hw K halfExtent)
              observable
              (fun left right =>
                Q'.divPos
                  (geometricMehlerTaylorPartial
                    left right 1)
                  (geometricTaylorVacuumPartition 1)
                  geometricTaylorVacuumPartition_one_pos)) ≤
          rate *
            centralPhysicalWeightedInner
              w hw K halfExtent observable observable

/-- An explicit inhabitant of the complete rank-one Rayleigh datum from a
positive physical-row marginal floor.  The mean-zero hypothesis is not
needed for this (coarse but exact) finite-dimensional estimate. -/
def rankOneTaylorPhysicalRateDataOfMarginalFloor
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (floorData :
      RankOnePhysicalMarginalFloorData
        w hw K halfExtent) :
    RankOneTaylorPhysicalRateData
      w hw K halfExtent where
  rate :=
    Q'.divPos
      (rankOneAmplitudeL2Sum
        (centralPositiveHalfStates
          w hw K halfExtent))
      floorData.floor floorData.floor_pos
  rate_nonnegative := by
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (rankOneAmplitudeL2Sum_nonnegative
        (centralPositiveHalfStates
          w hw K halfExtent))
      (Q'.le_of_lt
        (Q'.recipPos_pos
          floorData.floor floorData.floor_pos))
  normalized_meanZero_quadratic := by
    intro observable _
    let states :=
      centralPositiveHalfStates
        w hw K halfExtent
    let amplitudeSquare :=
      rankOneAmplitudeL2Sum states
    let observableSquare :=
      listQSum
        (fun state => observable state * observable state)
        states
    let physicalSquare :=
      centralPhysicalWeightedInner
        w hw K halfExtent observable observable
    have hnormalizedNonnegative :
        (0 : Q') ≤
          finiteJointQuadratic states observable
            (fun left right =>
              Q'.divPos
                (geometricMehlerTaylorPartial
                  left right 1)
                (geometricTaylorVacuumPartition 1)
                geometricTaylorVacuumPartition_one_pos) :=
      normalized_geometricMehlerTaylorPartial_one_quadratic_nonnegative
        states observable
    rw [YMGap.Constructive.TrigAdd.abs_of_nonneg
      hnormalizedNonnegative]
    have hnormalizedRankOne :
        finiteJointQuadratic states observable
            (fun left right =>
              Q'.divPos
                (geometricMehlerTaylorPartial
                  left right 1)
                (geometricTaylorVacuumPartition 1)
                geometricTaylorVacuumPartition_one_pos) ≈
          finiteJointQuadratic states observable
            (fun left right =>
              geometricZerothHalfAmplitude left *
                geometricZerothHalfAmplitude right) :=
      finiteJointQuadratic_joint_eqv
        states observable
        (fun left right =>
          Q'.divPos
            (geometricMehlerTaylorPartial
              left right 1)
            (geometricTaylorVacuumPartition 1)
            geometricTaylorVacuumPartition_one_pos)
        (fun left right =>
          geometricZerothHalfAmplitude left *
            geometricZerothHalfAmplitude right)
        (by
          intro left _ right _
          exact
            normalized_geometricMehlerTaylorPartial_one_rankOne
              left right)
    have hrankOneSquare :=
      finiteJointQuadratic_rankOne_eq_square
        states observable geometricZerothHalfAmplitude
    have hcauchy :
        listQSum
              (fun state =>
                observable state *
                  geometricZerothHalfAmplitude state)
              states *
            listQSum
              (fun state =>
                observable state *
                  geometricZerothHalfAmplitude state)
              states ≤
          observableSquare * amplitudeSquare := by
      exact
        edgeLabelling_listQSum_cauchy_schwarz
          states observable geometricZerothHalfAmplitude
    have hobservable :
        observableSquare ≤
          Q'.divPos physicalSquare
            floorData.floor floorData.floor_pos := by
      exact
        unweightedSquare_le_divPos_physicalInner
          floorData observable
    have hamplitudeNonnegative :
        (0 : Q') ≤ amplitudeSquare := by
      exact rankOneAmplitudeL2Sum_nonnegative states
    have hscaled :
        observableSquare * amplitudeSquare ≤
          Q'.divPos physicalSquare
              floorData.floor floorData.floor_pos *
            amplitudeSquare :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        hobservable hamplitudeNonnegative
    have hscaledRate :
        Q'.divPos physicalSquare
              floorData.floor floorData.floor_pos *
            amplitudeSquare ≈
          Q'.divPos amplitudeSquare
              floorData.floor floorData.floor_pos *
            physicalSquare := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv
          (Q'.divPos physicalSquare
            floorData.floor floorData.floor_pos)
          amplitudeSquare)
        (amplitude_mul_physicalDiv_eqv_rate_mul_physical
          amplitudeSquare physicalSquare
          floorData.floor floorData.floor_pos)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hnormalizedRankOne)
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv hrankOneSquare)
        (Q'.le_trans' _ _ _ hcauchy
          (Q'.le_trans' _ _ _ hscaled
            (Q'.le_of_eqv hscaledRate))))

/-- Explicit inhabitant of the original pinned
`GeometricTaylorEndpointSpectralData` at order one.  Partition positivity,
symmetry, and PSD are filled by theorems above; only the physical Rayleigh
datum is supplied. -/
def rankOneGeometricTaylorEndpointSpectralData
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (physicalRate :
      RankOneTaylorPhysicalRateData
        w hw K halfExtent) :
    GeometricTaylorEndpointSpectralData
      w hw K halfExtent 1 where
  partition_pos :=
    geometricTaylorVacuumPartition_one_pos
  numerator_symmetric := by
    intro left right _ _
    exact geometricMehlerTaylorPartial_one_symmetric
      left right
  normalized_quadratic_nonnegative := by
    intro observable
    exact
      normalized_geometricMehlerTaylorPartial_one_quadratic_nonnegative
        (centralPositiveHalfStates
          w hw K halfExtent)
        observable
  rate := physicalRate.rate
  rate_nonnegative :=
    physicalRate.rate_nonnegative
  normalized_meanZero_quadratic :=
    physicalRate.normalized_meanZero_quadratic

/-- The canonical order-one spectral datum at any finite physical BF4
carrier.  Its rate is executable: the counting `L²` norm of the exact
five-Haar half-amplitude divided by the located minimum of the positive
physical row marginals. -/
def canonicalRankOneGeometricTaylorEndpointSpectralData
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) :
    GeometricTaylorEndpointSpectralData
      w hw K halfExtent 1 :=
  rankOneGeometricTaylorEndpointSpectralData
    (rankOneTaylorPhysicalRateDataOfMarginalFloor
      (centralPositivePhysicalMarginalFloorData
        w hw K halfExtent))

/-! ## 6. Explicit assembly of the original matched AF certificate -/

/-- Canonical rank-one endpoint specialized once to the exact matched BF4
coordinates at a scale.  Keeping this dependent specialization named avoids
re-elaborating its expanded physical carrier in each downstream field. -/
def matchedRankOneSpectralAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (scale : Nat) :
    GeometricTaylorEndpointSpectralData
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale) 1 :=
  canonicalRankOneGeometricTaylorEndpointSpectralData
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative
      family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)

/-- The precise residual data needed after fixing the original certificate's
Taylor order to one.  This does not repeat partition positivity, symmetry,
or PSD.  The `physicalRate` field is retained so the dependent analytic
budget stays small for Lean; it has the canonical explicit inhabitant
`rankOneTaylorPhysicalRateDataOfMarginalFloor
  (centralPositivePhysicalMarginalFloorData ...)` proved above.  Thus the
genuine residuals are the coupling window and the AF-uniform
numerator/partition/marginal comparison budget. -/
structure RankOneMatchedReflectedAllSpinAFData
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  physicalRate :
    ∀ scale,
      RankOneTaylorPhysicalRateData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
  epsilon : Q'
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  analyticBudget :
    ∀ scale,
      CentralPhysicalNumeratorPartitionBudget
        (rankOneGeometricTaylorEndpointSpectralData
          (physicalRate scale)).toRawEndpoint
        epsilon

/-- An explicit inhabitant constructor for the original, unchanged
`MatchedReflectedAllSpinAFRowCertificate`.  Its order is definitionally the
one-term Taylor endpoint, while every algebraic endpoint field is supplied
by a proved theorem. -/
def matchedReflectedAllSpinAFRowCertificateOfRankOne
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent : Nat → Nat}
    (data :
      RankOneMatchedReflectedAllSpinAFData
        family law spacing coupling halfExtent) :
    MatchedReflectedAllSpinAFRowCertificate
      family law spacing coupling halfExtent where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  order := fun _ => 1
  spectral := fun scale =>
    rankOneGeometricTaylorEndpointSpectralData
      (data.physicalRate scale)
  epsilon := data.epsilon
  epsilon_nonnegative := data.epsilon_nonnegative
  analyticBudget := data.analyticBudget

/-- Direct canonical inhabitant constructor.  Unlike the record-level
constructor above, this version fixes the physical Rayleigh datum to the
located positive-row minimum and therefore asks only for the coupling
window and the genuine AF-uniform analytic budget. -/
def matchedReflectedAllSpinAFRowCertificateOfCanonicalRankOne
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent : Nat → Nat}
    (coupling_pos :
      ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window :
      ∀ scale, coupling scale ≤ law.g₁)
    (epsilon : Q')
    (epsilon_nonnegative : (0 : Q') ≤ epsilon)
    (analyticBudget :
      ∀ scale,
        CentralPhysicalNumeratorPartitionBudget
          (matchedRankOneSpectralAt
            family coupling halfExtent scale).toRawEndpoint
          epsilon) :
    MatchedReflectedAllSpinAFRowCertificate
      family law spacing coupling halfExtent where
  coupling_pos := coupling_pos
  coupling_le_window := coupling_le_window
  order := fun _ => 1
  spectral := fun scale =>
    matchedRankOneSpectralAt
      family coupling halfExtent scale
  epsilon := epsilon
  epsilon_nonnegative := epsilon_nonnegative
  analyticBudget := analyticBudget

theorem matchedReflectedAllSpinAFRowCertificateOfCanonicalRankOne_order
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent : Nat → Nat}
    (coupling_pos :
      ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window :
      ∀ scale, coupling scale ≤ law.g₁)
    (epsilon : Q')
    (epsilon_nonnegative : (0 : Q') ≤ epsilon)
    (analyticBudget :
      ∀ scale,
        CentralPhysicalNumeratorPartitionBudget
          (matchedRankOneSpectralAt
            family coupling halfExtent scale).toRawEndpoint
          epsilon)
    (scale : Nat) :
    (matchedReflectedAllSpinAFRowCertificateOfCanonicalRankOne
      (spacing := spacing)
      coupling_pos coupling_le_window
      epsilon epsilon_nonnegative analyticBudget).order scale = 1 := rfl

theorem matchedReflectedAllSpinAFRowCertificateOfRankOne_order
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent : Nat → Nat}
    (data :
      RankOneMatchedReflectedAllSpinAFData
        family law spacing coupling halfExtent)
    (scale : Nat) :
    (matchedReflectedAllSpinAFRowCertificateOfRankOne
      data).order scale = 1 := rfl

end YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint

#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.quaternionHaarPrefix_append_exact
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.quaternionHaarMono_append_exact
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.monoMul_shift_exact
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.tenfoldHaar_source_target_factorization
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.geometricMehlerTaylorPartial_one_rankOne
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.geometricZerothHalfAmplitude_vacuum
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.geometricTaylorVacuumPartition_one_pos
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.normalized_geometricMehlerTaylorPartial_one_rankOne
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.geometricMehlerTaylorPartial_one_symmetric
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.finiteJointQuadratic_rankOne_nonnegative
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.normalized_geometricMehlerTaylorPartial_one_quadratic_nonnegative
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.edgeLabelling_listQSum_cauchy_schwarz
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.centralPositivePhysicalMarginalFloorData
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.rankOneTaylorPhysicalRateDataOfMarginalFloor
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.rankOneGeometricTaylorEndpointSpectralData
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.canonicalRankOneGeometricTaylorEndpointSpectralData
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.matchedReflectedAllSpinAFRowCertificateOfRankOne
#print axioms YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint.matchedReflectedAllSpinAFRowCertificateOfCanonicalRankOne
