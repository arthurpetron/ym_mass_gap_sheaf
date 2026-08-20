/-
# Deterministic finite statistics for the regularized rank-one projection

For a finite nonnegative matrix `A`, the canonical aggregate-column profile
is a regularized empirical marginal.  This file gives an exact deterministic
decomposition of its rank-one projection error.

After clearing the positive normalization denominator, the error at
`(source,target)` is the sum of

* pairwise cross-row residuals
  `rowMass(other) * A(source,target) - rowMass(source) * A(other,target)`; and
* the explicit pseudocount bias
  `epsilon * (|targets| * A(source,target) - rowMass(source))`.

Consequently a pointwise pairwise-row budget pays only the finite source
cardinality, and division by the constructive positive denominator recovers
an entrywise rank-one defect bound.  Source shards give an exact map-reduce
schedule, while source blocks whose residuals are exactly invariant can be
replaced by a representative and an exact multiplicity.  These are
finite-system theorems: they use no probability limit, compactness, choice,
or continuum inference.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Constructive.CRealAbs
import YMGap.Continuum.FiniteWeightedGramSOS
import YMGap.Continuum.RcQuadResidualClose
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.FiniteRegularizedRankOneStatistics

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RcQuadResidualClose
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

/-- Cancellation-free normalization for the small exact rational identities
in this file. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic finite matrix marginals -/

def finiteRowMass {Source Target : Type}
    (targets : List Target) (amplitude : Source → Target → Q')
    (source : Source) : Q' :=
  listQSum (amplitude source) targets

def finiteColumnMass {Source Target : Type}
    (sources : List Source) (amplitude : Source → Target → Q')
    (target : Target) : Q' :=
  listQSum (fun source => amplitude source target) sources

def finiteTotalMass {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q') : Q' :=
  listQSum (finiteRowMass targets amplitude) sources

def finiteRegularizedNumerator {Source Target : Type}
    (sources : List Source) (amplitude : Source → Target → Q')
    (pseudocount : Q') (target : Target) : Q' :=
  pseudocount + finiteColumnMass sources amplitude target

def finiteRegularizedDenominator {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q') : Q' :=
  listQSum
    (finiteRegularizedNumerator sources amplitude pseudocount)
    targets

def finiteRegularizedProfile {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q')
    (denominator_pos :
      (0 : Q') <
        finiteRegularizedDenominator
          sources targets amplitude pseudocount)
    (target : Target) : Q' :=
  Q'.divPos
    (finiteRegularizedNumerator sources amplitude pseudocount target)
    (finiteRegularizedDenominator sources targets amplitude pseudocount)
    denominator_pos

def finiteRegularizedProjection {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q')
    (denominator_pos :
      (0 : Q') <
        finiteRegularizedDenominator
          sources targets amplitude pseudocount)
    (source : Source) (target : Target) : Q' :=
  finiteRowMass targets amplitude source *
    finiteRegularizedProfile
      sources targets amplitude pseudocount denominator_pos target

/-! ## 2. Exact cross-multiplied statistical decomposition -/

def finitePairwiseRowCrossTerm {Source Target : Type}
    (targets : List Target) (amplitude : Source → Target → Q')
    (source other : Source) (target : Target) : Q' :=
  finiteRowMass targets amplitude other * amplitude source target +
    -(finiteRowMass targets amplitude source * amplitude other target)

def finitePairwiseRowCrossSum {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q')
    (source : Source) (target : Target) : Q' :=
  listQSum
    (fun other =>
      finitePairwiseRowCrossTerm targets amplitude source other target)
    sources

def finitePseudocountBiasTerm {Source Target : Type}
    (targets : List Target) (amplitude : Source → Target → Q')
    (pseudocount : Q') (source : Source) (target : Target) : Q' :=
  pseudocount *
    (Q'.ofNat targets.length * amplitude source target +
      -finiteRowMass targets amplitude source)

def finiteRegularizedCrossDefect {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q')
    (source : Source) (target : Target) : Q' :=
  finiteRegularizedDenominator sources targets amplitude pseudocount *
      amplitude source target +
    -(finiteRowMass targets amplitude source *
      finiteRegularizedNumerator sources amplitude pseudocount target)

private theorem listQSum_neg {A : Type} (value : A → Q') :
    ∀ items : List A,
      listQSum (fun item => -(value item)) items ≈
        -(listQSum value items)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.eqv_refl _)
          (listQSum_neg value tail)) ?_
      change
        -value head + -(listQSum value tail) ≈
          -(value head + listQSum value tail)
      q_ring

private theorem listQSum_const {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _head :: tail => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat tail.length * constant) _ ?_ ?_
      · exact Q'.add_eqv_congr_left constant _ _
          (listQSum_const constant tail)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv (Q'.ofNat tail.length * constant) constant)

/-- The empirical-profile denominator is exactly total matrix mass plus one
pseudocount for every target coordinate. -/
theorem finiteRegularizedDenominator_eqv_total_add_pseudocount
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q') :
    finiteRegularizedDenominator
        sources targets amplitude pseudocount ≈
      finiteTotalMass sources targets amplitude +
        Q'.ofNat targets.length * pseudocount := by
  unfold finiteRegularizedDenominator finiteRegularizedNumerator
  refine Q'.eqv_trans _
    (listQSum (fun _target => pseudocount) targets +
      listQSum
        (finiteColumnMass sources amplitude) targets) _
    (listQSum_add
      (fun _target => pseudocount)
      (finiteColumnMass sources amplitude) targets) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat targets.length * pseudocount +
      finiteTotalMass sources targets amplitude) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (listQSum_const pseudocount targets)
      (by
        unfold finiteColumnMass finiteTotalMass finiteRowMass
        exact listQSum_swap amplitude sources targets)
  · exact Q'.add_comm_eqv _ _

theorem finitePairwiseRowCrossSum_eqv
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q')
    (source : Source) (target : Target) :
    finitePairwiseRowCrossSum
        sources targets amplitude source target ≈
      finiteTotalMass sources targets amplitude *
          amplitude source target +
        -(finiteRowMass targets amplitude source *
          finiteColumnMass sources amplitude target) := by
  unfold finitePairwiseRowCrossSum finitePairwiseRowCrossTerm
    finiteTotalMass finiteColumnMass
  refine Q'.eqv_trans _ _ _
    (listQSum_add
      (fun other =>
        finiteRowMass targets amplitude other *
          amplitude source target)
      (fun other =>
        -(finiteRowMass targets amplitude source *
          amplitude other target))
      sources) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (listQSum_mul_right
        (finiteRowMass targets amplitude)
        (amplitude source target) sources)
      (listQSum_neg
        (fun other =>
          finiteRowMass targets amplitude source *
            amplitude other target)
        sources)) ?_
  refine Q'.add_eqv_congr_left _ _ _ ?_
  apply Q'.neg_eqv_congr
  exact listQSum_mul_left
    (finiteRowMass targets amplitude source)
    (fun other => amplitude other target) sources

theorem finiteRegularizedCrossDefect_eqv
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q')
    (source : Source) (target : Target) :
    finiteRegularizedCrossDefect
        sources targets amplitude pseudocount source target ≈
      finitePairwiseRowCrossSum
          sources targets amplitude source target +
        finitePseudocountBiasTerm
          targets amplitude pseudocount source target := by
  refine Q'.eqv_trans _
    ((finiteTotalMass sources targets amplitude * amplitude source target +
        -(finiteRowMass targets amplitude source *
          finiteColumnMass sources amplitude target)) +
      finitePseudocountBiasTerm
        targets amplitude pseudocount source target) _ ?_ ?_
  · unfold finiteRegularizedCrossDefect finiteRegularizedDenominator
      finiteRegularizedNumerator finitePseudocountBiasTerm
    refine Q'.eqv_trans _
      ((finiteTotalMass sources targets amplitude +
          Q'.ofNat targets.length * pseudocount) *
            amplitude source target +
        -(finiteRowMass targets amplitude source *
          (pseudocount +
            finiteColumnMass sources amplitude target))) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ (amplitude source target)
          (finiteRegularizedDenominator_eqv_total_add_pseudocount
            sources targets amplitude pseudocount))
    · q_ring
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm
        (finitePairwiseRowCrossSum_eqv
          sources targets amplitude source target))

/-! ## 3. Absolute budgets and the finite-cardinality cost -/

def finitePairwiseRowResidualBudget {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q')
    (source : Source) (target : Target) : Q' :=
  listQSum
    (fun other =>
      Q'.abs
        (finitePairwiseRowCrossTerm
          targets amplitude source other target))
    sources

private theorem listQSum_append_local {A : Type}
    (value : A → Q') : ∀ left right : List A,
    listQSum value (left ++ right) ≈
      listQSum value left + listQSum value right
  | [], right =>
      Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' (listQSum value right)))
  | head :: tail, right => by
      change
        value head + listQSum value (tail ++ right) ≈
          (value head + listQSum value tail) + listQSum value right
      exact Q'.eqv_trans _
        (value head +
          (listQSum value tail + listQSum value right)) _
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_append_local value tail right))
        (Q'.eqv_symm
          (Q'.add_assoc_eqv
            (value head) (listQSum value tail) (listQSum value right)))

/-- Pairwise residual work is exactly additive under a split of the retained
source list.  This is the algebraic basis for bounded-memory certificate
shards. -/
theorem finitePairwiseRowResidualBudget_append
    {Source Target : Type}
    (left right : List Source) (targets : List Target)
    (amplitude : Source → Target → Q')
    (source : Source) (target : Target) :
    finitePairwiseRowResidualBudget
        (left ++ right) targets amplitude source target ≈
      finitePairwiseRowResidualBudget
          left targets amplitude source target +
        finitePairwiseRowResidualBudget
          right targets amplitude source target := by
  unfold finitePairwiseRowResidualBudget
  exact listQSum_append_local _ left right

/-- The exact residual budget computed shard by shard.  Each inner source
list can be elaborated and checked in an independent generated module. -/
def finiteChunkedPairwiseRowResidualBudget {Source Target : Type}
    (sourceChunks : List (List Source)) (targets : List Target)
    (amplitude : Source → Target → Q')
    (source : Source) (target : Target) : Q' :=
  listQSum
    (fun chunk =>
      finitePairwiseRowResidualBudget
        chunk targets amplitude source target)
    sourceChunks

/-- Chunking changes the evaluation schedule but not the exact rational
statistic. -/
theorem finiteChunkedPairwiseRowResidualBudget_eqv_flatten
    {Source Target : Type}
    (targets : List Target) (amplitude : Source → Target → Q')
    (source : Source) (target : Target) :
    ∀ sourceChunks : List (List Source),
      finiteChunkedPairwiseRowResidualBudget
          sourceChunks targets amplitude source target ≈
        finitePairwiseRowResidualBudget
          sourceChunks.flatten targets amplitude source target
  | [] => Q'.eqv_refl 0
  | chunk :: chunks => by
      simp only [finiteChunkedPairwiseRowResidualBudget,
        List.flatten_cons, listQSum]
      exact Q'.eqv_trans _
        (finitePairwiseRowResidualBudget
            chunk targets amplitude source target +
          finitePairwiseRowResidualBudget
            chunks.flatten targets amplitude source target) _
        (Q'.add_eqv_congr_left _ _ _
          (finiteChunkedPairwiseRowResidualBudget_eqv_flatten
            targets amplitude source target chunks))
        (Q'.eqv_symm
          (finitePairwiseRowResidualBudget_append
            chunk chunks.flatten targets amplitude source target))

/-- Sum of externally proposed per-shard majorants.  The proposal is not
trusted: Lean still requires a proof for every shard. -/
def finiteChunkedPairwiseRowResidualMajorant {Source : Type}
    (sourceChunks : List (List Source))
    (chunkMajorant : List Source → Q') : Q' :=
  listQSum chunkMajorant sourceChunks

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hbound => by
      exact Q'.add_le_add
        (hbound head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hbound item (List.mem_cons_of_mem head hitem)))

/-- Independently checked shard bounds add to a bound for the exact chunked
residual statistic. -/
theorem finiteChunkedPairwiseRowResidualBudget_le_majorant
    {Source Target : Type}
    (sourceChunks : List (List Source)) (targets : List Target)
    (amplitude : Source → Target → Q')
    (chunkMajorant : List Source → Q')
    (source : Source) (target : Target)
    (chunk_bound :
      ∀ chunk, chunk ∈ sourceChunks →
        finitePairwiseRowResidualBudget
            chunk targets amplitude source target ≤
          chunkMajorant chunk) :
    finiteChunkedPairwiseRowResidualBudget
        sourceChunks targets amplitude source target ≤
      finiteChunkedPairwiseRowResidualMajorant
        sourceChunks chunkMajorant := by
  exact listQSum_le_termwise_local _ _ sourceChunks chunk_bound

/-! ## 4. Exact block compression by sufficient statistics -/

private theorem listQSum_flatMap_local {Class Item : Type}
    (block : Class → List Item) (value : Item → Q') :
    ∀ classes : List Class,
      listQSum value (classes.flatMap block) ≈
        listQSum (fun cls => listQSum value (block cls)) classes
  | [] => Q'.eqv_refl 0
  | cls :: classes => by
      simp only [List.flatMap_cons, listQSum]
      exact Q'.eqv_trans _
        (listQSum value (block cls) +
          listQSum value (classes.flatMap block)) _
        (listQSum_append_local value (block cls)
          (classes.flatMap block))
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_flatMap_local block value classes))

/-- Exact source-block statistic.  A class contributes its multiplicity
times the absolute pairwise residual of one representative.  No external
classification is trusted: the compression theorem below requires Lean
proofs that every listed block member has the representative statistic. -/
def finiteBlockCompressedPairwiseRowResidualBudget
    {Class Source Target : Type}
    (classes : List Class) (block : Class → List Source)
    (representative : Class → Source) (targets : List Target)
    (amplitude : Source → Target → Q')
    (source : Source) (target : Target) : Q' :=
  listQSum
    (fun cls =>
      Q'.ofNat (block cls).length *
        Q'.abs
          (finitePairwiseRowCrossTerm targets amplitude source
            (representative cls) target))
    classes

/-- Exact block compression of the pairwise residual budget.  Coverage is
expressed by `flatMap`; repetitions and empty blocks are therefore handled
as list data rather than silently quotiented away. -/
theorem finitePairwiseRowResidualBudget_eqv_blockCompressed
    {Class Source Target : Type}
    (classes : List Class) (block : Class → List Source)
    (representative : Class → Source) (targets : List Target)
    (amplitude : Source → Target → Q')
    (source : Source) (target : Target)
    (block_invariant :
      ∀ cls, cls ∈ classes → ∀ other, other ∈ block cls →
        Q'.abs
            (finitePairwiseRowCrossTerm
              targets amplitude source other target) ≈
          Q'.abs
            (finitePairwiseRowCrossTerm
              targets amplitude source (representative cls) target)) :
    finitePairwiseRowResidualBudget
        (classes.flatMap block) targets amplitude source target ≈
      finiteBlockCompressedPairwiseRowResidualBudget
        classes block representative targets amplitude source target := by
  unfold finitePairwiseRowResidualBudget
    finiteBlockCompressedPairwiseRowResidualBudget
  refine Q'.eqv_trans _
    (listQSum
      (fun cls =>
        listQSum
          (fun other =>
            Q'.abs
              (finitePairwiseRowCrossTerm
                targets amplitude source other target))
          (block cls))
      classes) _
    (listQSum_flatMap_local block _ classes) ?_
  apply listQSum_congr_on
  intro cls hcls
  refine Q'.eqv_trans _
    (listQSum
      (fun _other =>
        Q'.abs
          (finitePairwiseRowCrossTerm targets amplitude source
            (representative cls) target))
      (block cls)) _ ?_ ?_
  · exact listQSum_congr_on _ _ (block cls)
      (fun other hother => block_invariant cls hcls other hother)
  · exact listQSum_const _ (block cls)

def finitePseudocountBiasBudget {Source Target : Type}
    (targets : List Target) (amplitude : Source → Target → Q')
    (pseudocount : Q') (source : Source) (target : Target) : Q' :=
  Q'.abs
    (finitePseudocountBiasTerm
      targets amplitude pseudocount source target)

private theorem abs_listQSum_le_sum_abs
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      Q'.abs (listQSum value items) ≤
        listQSum (fun item => Q'.abs (value item)) items
  | [] => by
      change Q'.abs (0 : Q') ≤ 0
      decide
  | head :: tail => by
      exact Q'.le_trans' _ _ _
        (Q'.abs_add_le' (value head) (listQSum value tail))
        (Q'.add_le_add_left _ _ _
          (abs_listQSum_le_sum_abs value tail))

theorem finiteRegularizedCrossDefect_abs_le
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q')
    (source : Source) (target : Target) :
    Q'.abs
        (finiteRegularizedCrossDefect
          sources targets amplitude pseudocount source target) ≤
      finitePairwiseRowResidualBudget
          sources targets amplitude source target +
        finitePseudocountBiasBudget
          targets amplitude pseudocount source target := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (finiteRegularizedCrossDefect_eqv
          sources targets amplitude pseudocount source target))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.abs_add_le'
      (finitePairwiseRowCrossSum
        sources targets amplitude source target)
      (finitePseudocountBiasTerm
        targets amplitude pseudocount source target)) ?_
  exact Q'.add_le_add_right _ _ _
    (abs_listQSum_le_sum_abs
      (fun other =>
        finitePairwiseRowCrossTerm
          targets amplitude source other target)
      sources)

private theorem listQSum_le_length_mul
    {A : Type} (value : A → Q') {bound : Q'}
    (bound_nonnegative : (0 : Q') ≤ bound) :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≤ bound) →
        listQSum value items ≤ Q'.ofNat items.length * bound
  | [], _ => Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail := listQSum_le_length_mul value bound_nonnegative tail
        (fun item hitem => hbound item (List.mem_cons_of_mem head hitem))
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add hhead htail) ?_
      refine Q'.le_of_eqv (Q'.eqv_symm ?_)
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ bound
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + (1 : Q') * bound) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 bound) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + bound) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
        (Q'.add_comm_eqv (Q'.ofNat tail.length * bound) bound)

theorem finitePairwiseRowResidualBudget_le_cardinality
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q')
    (pairwiseBound : Q')
    (pairwiseBound_nonnegative : (0 : Q') ≤ pairwiseBound)
    (source : Source) (target : Target)
    (pairwise :
      ∀ other, other ∈ sources →
        Q'.abs
            (finitePairwiseRowCrossTerm
              targets amplitude source other target) ≤
          pairwiseBound) :
    finitePairwiseRowResidualBudget
        sources targets amplitude source target ≤
      Q'.ofNat sources.length * pairwiseBound := by
  exact listQSum_le_length_mul _ pairwiseBound_nonnegative sources pairwise

/-- For nonnegative scalars, the absolute difference is bounded by their
sum. -/
private theorem abs_sub_nonnegative_le_add
    {left right : Q'}
    (left_nonnegative : (0 : Q') ≤ left)
    (right_nonnegative : (0 : Q') ≤ right) :
    Q'.abs (left + -right) ≤ left + right := by
  apply Q'.abs_le
  · have neg_left_le_left : -left ≤ left :=
      Q'.le_trans' _ _ _
        (Q'.nonpos_neg_of_nonneg left_nonnegative)
        left_nonnegative
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_add_eqv left right))
      (Q'.add_le_add_right (-left) left (-right)
        neg_left_le_left)
  · have neg_right_le_right : -right ≤ right :=
      Q'.le_trans' _ _ _
        (Q'.nonpos_neg_of_nonneg right_nonnegative)
        right_nonnegative
    exact Q'.add_le_add_left left (-right) right
      neg_right_le_right

/-- The regularization term is a transparent finite-sample bias: it is at
most `epsilon * (targetCount * entry + rowMass)` for a nonnegative matrix. -/
theorem finitePseudocountBiasBudget_le
    {Source Target : Type}
    (targets : List Target) (amplitude : Source → Target → Q')
    {pseudocount : Q'}
    (pseudocount_nonnegative : (0 : Q') ≤ pseudocount)
    (amplitude_nonnegative :
      ∀ source target, target ∈ targets →
        (0 : Q') ≤ amplitude source target)
    (source : Source) (target : Target)
    (target_mem : target ∈ targets) :
    finitePseudocountBiasBudget
        targets amplitude pseudocount source target ≤
      pseudocount *
        (Q'.ofNat targets.length * amplitude source target +
          finiteRowMass targets amplitude source) := by
  let entryScale :=
    Q'.ofNat targets.length * amplitude source target
  let rowMass := finiteRowMass targets amplitude source
  have entryScale_nonnegative : (0 : Q') ≤ entryScale :=
    Q'.mul_nonneg _ _ (YMGap.Constructive.ExpNeg.ofNat_nonneg' targets.length)
      (amplitude_nonnegative source target target_mem)
  have rowMass_nonnegative : (0 : Q') ≤ rowMass := by
    exact listQSum_nonnegative_on (amplitude source) targets
      (fun item hitem => amplitude_nonnegative source item hitem)
  have difference_bound :
      Q'.abs (entryScale + -rowMass) ≤ entryScale + rowMass :=
    abs_sub_nonnegative_le_add
      entryScale_nonnegative rowMass_nonnegative
  unfold finitePseudocountBiasBudget finitePseudocountBiasTerm
  change Q'.abs (pseudocount * (entryScale + -rowMass)) ≤
    pseudocount * (entryScale + rowMass)
  refine Q'.le_trans' _
    (Q'.abs pseudocount * Q'.abs (entryScale + -rowMass)) _
    (Q'.le_of_eqv (q_abs_mul_eqv _ _)) ?_
  refine Q'.le_trans' _
    (pseudocount * Q'.abs (entryScale + -rowMass)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ _
        (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
          pseudocount_nonnegative))
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      difference_bound pseudocount_nonnegative

/-! ## 4. Return from the cleared statistic to the rank-one defect -/

def finiteRegularizedRankOneDefect {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q')
    (denominator_pos :
      (0 : Q') <
        finiteRegularizedDenominator
          sources targets amplitude pseudocount)
    (source : Source) (target : Target) : Q' :=
  Q'.abs
    (amplitude source target +
      -finiteRegularizedProjection
        sources targets amplitude pseudocount denominator_pos
        source target)

theorem finiteRegularizedRankOneDefect_mul_denominator_eqv
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q')
    (denominator_pos :
      (0 : Q') <
        finiteRegularizedDenominator
          sources targets amplitude pseudocount)
    (source : Source) (target : Target) :
    finiteRegularizedRankOneDefect
          sources targets amplitude pseudocount denominator_pos
          source target *
        finiteRegularizedDenominator
          sources targets amplitude pseudocount ≈
      Q'.abs
        (finiteRegularizedCrossDefect
          sources targets amplitude pseudocount source target) := by
  let denominator :=
    finiteRegularizedDenominator
      sources targets amplitude pseudocount
  let numerator :=
    finiteRegularizedNumerator
      sources amplitude pseudocount target
  let rowMass := finiteRowMass targets amplitude source
  let difference :=
    amplitude source target +
      -(rowMass * Q'.divPos numerator denominator denominator_pos)
  have difference_mul :
      difference * denominator ≈
        finiteRegularizedCrossDefect
          sources targets amplitude pseudocount source target := by
    refine Q'.eqv_trans _
      (denominator * amplitude source target +
        -(rowMass * numerator)) _ ?_ ?_
    · refine Q'.eqv_trans _
        (denominator * amplitude source target +
          -(rowMass *
            (Q'.divPos numerator denominator denominator_pos *
              denominator))) _ ?_ ?_
      · dsimp only [difference]
        q_ring
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_left rowMass _ _
              (Q'.divPos_mul_eqv
                numerator denominator denominator_pos)))
    · unfold finiteRegularizedCrossDefect
      exact Q'.eqv_refl _
  change Q'.abs difference * denominator ≈
    Q'.abs
      (finiteRegularizedCrossDefect
        sources targets amplitude pseudocount source target)
  refine Q'.eqv_trans _
    (Q'.abs difference * Q'.abs denominator) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (Q'.abs difference) _ _
      (Q'.eqv_symm
        (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
          (Q'.le_of_lt denominator_pos)))
  refine Q'.eqv_trans _ (Q'.abs (difference * denominator)) _
    (Q'.eqv_symm (q_abs_mul_eqv difference denominator)) ?_
  exact Q'.abs_eqv_congr difference_mul

theorem finiteRegularizedRankOneDefect_le_divPos_budget
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q')
    (denominator_pos :
      (0 : Q') <
        finiteRegularizedDenominator
          sources targets amplitude pseudocount)
    (source : Source) (target : Target) :
    finiteRegularizedRankOneDefect
        sources targets amplitude pseudocount denominator_pos
        source target ≤
      Q'.divPos
        (finitePairwiseRowResidualBudget
            sources targets amplitude source target +
          finitePseudocountBiasBudget
            targets amplitude pseudocount source target)
        (finiteRegularizedDenominator
          sources targets amplitude pseudocount)
        denominator_pos := by
  apply Q'.le_divPos_of_mul_le
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (finiteRegularizedRankOneDefect_mul_denominator_eqv
        sources targets amplitude pseudocount denominator_pos
        source target))
    (finiteRegularizedCrossDefect_abs_le
      sources targets amplitude pseudocount source target)

/-- A finite sufficient-statistics theorem: exact source blocks may be
replaced by their cardinalities and one representative residual.  The
pointwise block-invariance hypotheses are checked by Lean, so an external
orbit finder or factor-graph program may only propose the partition. -/
theorem finiteRegularizedRankOneDefect_le_blockCompressed
    {Class Source Target : Type}
    (classes : List Class) (block : Class → List Source)
    (representative : Class → Source) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q')
    (denominator_pos :
      (0 : Q') <
        finiteRegularizedDenominator
          (classes.flatMap block) targets amplitude pseudocount)
    (source : Source) (target : Target)
    (block_invariant :
      ∀ cls, cls ∈ classes → ∀ other, other ∈ block cls →
        Q'.abs
            (finitePairwiseRowCrossTerm
              targets amplitude source other target) ≈
          Q'.abs
            (finitePairwiseRowCrossTerm
              targets amplitude source (representative cls) target)) :
    finiteRegularizedRankOneDefect
        (classes.flatMap block) targets amplitude pseudocount denominator_pos
        source target ≤
      Q'.divPos
        (finiteBlockCompressedPairwiseRowResidualBudget
            classes block representative targets amplitude source target +
          finitePseudocountBiasBudget
            targets amplitude pseudocount source target)
        (finiteRegularizedDenominator
          (classes.flatMap block) targets amplitude pseudocount)
        denominator_pos := by
  apply Q'.le_divPos_of_mul_le
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (finiteRegularizedRankOneDefect_mul_denominator_eqv
        (classes.flatMap block) targets amplitude pseudocount denominator_pos
        source target)) ?_
  refine Q'.le_trans' _ _ _
    (finiteRegularizedCrossDefect_abs_le
      (classes.flatMap block) targets amplitude pseudocount source target) ?_
  apply Q'.add_le_add_right
  exact Q'.le_of_eqv
    (finitePairwiseRowResidualBudget_eqv_blockCompressed
      classes block representative targets amplitude source target
      block_invariant)

/-- Extensional block-compression theorem for a separately named source
enumeration.  The exact list equality is the coverage certificate. -/
theorem finiteRegularizedRankOneDefect_le_blockCompressed_of_flatMap_eq
    {Class Source Target : Type}
    (sources : List Source) (classes : List Class)
    (block : Class → List Source)
    (blocks_flatten : classes.flatMap block = sources)
    (representative : Class → Source) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q')
    (denominator_pos :
      (0 : Q') <
        finiteRegularizedDenominator
          sources targets amplitude pseudocount)
    (source : Source) (target : Target)
    (block_invariant :
      ∀ cls, cls ∈ classes → ∀ other, other ∈ block cls →
        Q'.abs
            (finitePairwiseRowCrossTerm
              targets amplitude source other target) ≈
          Q'.abs
            (finitePairwiseRowCrossTerm
              targets amplitude source (representative cls) target)) :
    finiteRegularizedRankOneDefect
        sources targets amplitude pseudocount denominator_pos source target ≤
      Q'.divPos
        (finiteBlockCompressedPairwiseRowResidualBudget
            classes block representative targets amplitude source target +
          finitePseudocountBiasBudget
            targets amplitude pseudocount source target)
        (finiteRegularizedDenominator
          sources targets amplitude pseudocount)
        denominator_pos := by
  subst sources
  exact finiteRegularizedRankOneDefect_le_blockCompressed
    classes block representative targets amplitude pseudocount
    denominator_pos source target block_invariant

/-- A map-reduce certificate theorem: each source shard is checked against
its own proposed rational majorant, the shard majorants are added by Lean,
and the resulting sum bounds the rank-one defect for the flattened source
list.  External parallel computation may propose the shard partition and
numbers, but neither is trusted. -/
theorem finiteRegularizedRankOneDefect_le_chunkedMajorant
    {Source Target : Type}
    (sourceChunks : List (List Source)) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q')
    (denominator_pos :
      (0 : Q') <
        finiteRegularizedDenominator
          sourceChunks.flatten targets amplitude pseudocount)
    (chunkMajorant : List Source → Q')
    (source : Source) (target : Target)
    (chunk_bound :
      ∀ chunk, chunk ∈ sourceChunks →
        finitePairwiseRowResidualBudget
            chunk targets amplitude source target ≤
          chunkMajorant chunk) :
    finiteRegularizedRankOneDefect
        sourceChunks.flatten targets amplitude pseudocount denominator_pos
        source target ≤
      Q'.divPos
        (finiteChunkedPairwiseRowResidualMajorant
            sourceChunks chunkMajorant +
          finitePseudocountBiasBudget
            targets amplitude pseudocount source target)
        (finiteRegularizedDenominator
          sourceChunks.flatten targets amplitude pseudocount)
        denominator_pos := by
  apply Q'.le_divPos_of_mul_le
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (finiteRegularizedRankOneDefect_mul_denominator_eqv
        sourceChunks.flatten targets amplitude pseudocount denominator_pos
        source target)) ?_
  refine Q'.le_trans' _ _ _
    (finiteRegularizedCrossDefect_abs_le
      sourceChunks.flatten targets amplitude pseudocount source target) ?_
  apply Q'.add_le_add_right
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (finiteChunkedPairwiseRowResidualBudget_eqv_flatten
          targets amplitude source target sourceChunks))) ?_
  exact finiteChunkedPairwiseRowResidualBudget_le_majorant
    sourceChunks targets amplitude chunkMajorant source target chunk_bound

/-- Extensional form of the map-reduce theorem for a separately named source
list.  The coverage equality is checked by Lean and rules out missing or
duplicated shards relative to that named enumeration. -/
theorem finiteRegularizedRankOneDefect_le_chunkedMajorant_of_flatten_eq
    {Source Target : Type}
    (sources : List Source) (sourceChunks : List (List Source))
    (sourceChunks_flatten : sourceChunks.flatten = sources)
    (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q')
    (denominator_pos :
      (0 : Q') <
        finiteRegularizedDenominator
          sources targets amplitude pseudocount)
    (chunkMajorant : List Source → Q')
    (source : Source) (target : Target)
    (chunk_bound :
      ∀ chunk, chunk ∈ sourceChunks →
        finitePairwiseRowResidualBudget
            chunk targets amplitude source target ≤
          chunkMajorant chunk) :
    finiteRegularizedRankOneDefect
        sources targets amplitude pseudocount denominator_pos
        source target ≤
      Q'.divPos
        (finiteChunkedPairwiseRowResidualMajorant
            sourceChunks chunkMajorant +
          finitePseudocountBiasBudget
            targets amplitude pseudocount source target)
        (finiteRegularizedDenominator
          sources targets amplitude pseudocount)
        denominator_pos := by
  subst sources
  exact finiteRegularizedRankOneDefect_le_chunkedMajorant
    sourceChunks targets amplitude pseudocount denominator_pos
    chunkMajorant source target chunk_bound

/-- A uniform pairwise residual estimate can be combined with the exact
pseudocount-bias term.  This pays the source cardinality without replacing
the bias absolute value by the coarser sum of its two nonnegative parts. -/
theorem finiteRegularizedRankOneDefect_le_of_pairwise_exactBias
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q') (pseudocount : Q')
    (denominator_pos :
      (0 : Q') <
        finiteRegularizedDenominator
          sources targets amplitude pseudocount)
    (pairwiseBound : Q')
    (pairwiseBound_nonnegative : (0 : Q') ≤ pairwiseBound)
    (source : Source) (target : Target)
    (pairwise :
      ∀ other, other ∈ sources →
        Q'.abs
            (finitePairwiseRowCrossTerm
              targets amplitude source other target) ≤
          pairwiseBound) :
    finiteRegularizedRankOneDefect
        sources targets amplitude pseudocount denominator_pos
        source target ≤
      Q'.divPos
        (Q'.ofNat sources.length * pairwiseBound +
          finitePseudocountBiasBudget
            targets amplitude pseudocount source target)
        (finiteRegularizedDenominator
          sources targets amplitude pseudocount)
        denominator_pos := by
  apply Q'.le_divPos_of_mul_le
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (finiteRegularizedRankOneDefect_mul_denominator_eqv
        sources targets amplitude pseudocount denominator_pos
        source target)) ?_
  refine Q'.le_trans' _ _ _
    (finiteRegularizedCrossDefect_abs_le
      sources targets amplitude pseudocount source target) ?_
  exact Q'.add_le_add_right _ _ _
    (finitePairwiseRowResidualBudget_le_cardinality
      sources targets amplitude pairwiseBound
      pairwiseBound_nonnegative source target pairwise)

/-- A uniform pairwise cross-row residual bound and the explicit pseudocount
bias give a completely deterministic entrywise rank-one estimate.  The only
finite-size loss is `sources.length`; no probabilistic or continuum limit is
used. -/
theorem finiteRegularizedRankOneDefect_le_of_pairwise
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (amplitude : Source → Target → Q') {pseudocount : Q'}
    (pseudocount_nonnegative : (0 : Q') ≤ pseudocount)
    (denominator_pos :
      (0 : Q') <
        finiteRegularizedDenominator
          sources targets amplitude pseudocount)
    (amplitude_nonnegative :
      ∀ source target, target ∈ targets →
        (0 : Q') ≤ amplitude source target)
    (pairwiseBound : Q')
    (pairwiseBound_nonnegative : (0 : Q') ≤ pairwiseBound)
    (source : Source) (target : Target)
    (target_mem : target ∈ targets)
    (pairwise :
      ∀ other, other ∈ sources →
        Q'.abs
            (finitePairwiseRowCrossTerm
              targets amplitude source other target) ≤
          pairwiseBound) :
    finiteRegularizedRankOneDefect
        sources targets amplitude pseudocount denominator_pos
        source target ≤
      Q'.divPos
        (Q'.ofNat sources.length * pairwiseBound +
          pseudocount *
            (Q'.ofNat targets.length * amplitude source target +
              finiteRowMass targets amplitude source))
        (finiteRegularizedDenominator
          sources targets amplitude pseudocount)
        denominator_pos := by
  apply Q'.le_divPos_of_mul_le
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (finiteRegularizedRankOneDefect_mul_denominator_eqv
        sources targets amplitude pseudocount denominator_pos
        source target)) ?_
  refine Q'.le_trans' _ _ _
    (finiteRegularizedCrossDefect_abs_le
      sources targets amplitude pseudocount source target) ?_
  exact Q'.add_le_add
    (finitePairwiseRowResidualBudget_le_cardinality
      sources targets amplitude pairwiseBound
      pairwiseBound_nonnegative source target pairwise)
    (finitePseudocountBiasBudget_le
      targets amplitude pseudocount_nonnegative amplitude_nonnegative
      source target target_mem)

end YMGap.Continuum.FiniteRegularizedRankOneStatistics

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finitePairwiseRowCrossSum_eqv
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finiteRegularizedCrossDefect_eqv
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finiteRegularizedCrossDefect_abs_le
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finitePairwiseRowResidualBudget_le_cardinality
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finitePairwiseRowResidualBudget_append
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finiteChunkedPairwiseRowResidualBudget_eqv_flatten
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finiteChunkedPairwiseRowResidualBudget_le_majorant
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finitePairwiseRowResidualBudget_eqv_blockCompressed
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finitePseudocountBiasBudget_le
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finiteRegularizedRankOneDefect_le_divPos_budget
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finiteRegularizedRankOneDefect_le_blockCompressed
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finiteRegularizedRankOneDefect_le_blockCompressed_of_flatMap_eq
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finiteRegularizedRankOneDefect_le_chunkedMajorant
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finiteRegularizedRankOneDefect_le_chunkedMajorant_of_flatten_eq
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finiteRegularizedRankOneDefect_le_of_pairwise_exactBias
#print axioms YMGap.Continuum.FiniteRegularizedRankOneStatistics.finiteRegularizedRankOneDefect_le_of_pairwise
