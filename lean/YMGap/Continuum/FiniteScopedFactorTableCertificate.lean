/-
# Kernel-checked local tables for finite scoped factor graphs

An external exact-arithmetic program may propose a table equation on a small
factor scope.  This file supplies the constructive proof contract that turns
the finite Boolean check into a theorem for every bounded global labelling.
The reduction uses an explicit restriction of a global labelling to the
checked scope and the locality carried by each factor.

This is a general computer-science theorem about finite table certificates.
It neither trusts an external evaluator nor asserts any asymptotic or
continuum statement.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
import YMGap.Continuum.FiniteWeightedGramSOS
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

namespace YMGap.Continuum.FiniteScopedFactorTableCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-- A rational factor together with the finite list of coordinates on which
it depends.  The locality law uses structural equality, which is stronger
than rational-setoid equality and convenient for executable tables. -/
structure ScopedQFactor : Type where
  scope : List Nat
  value : EdgeLabelling → Q'
  local_eq :
    ∀ left right,
      (∀ id, id ∈ scope → left id = right id) →
        value left = value right

/-- Base-`domainSize` index of a local label word, with the head digit most
significant.  This is the same table order used by `allSeqs`. -/
def scopedTableIndex (domainSize : Nat) : List Nat → Nat
  | [] => 0
  | head :: tail =>
      head * domainSize ^ tail.length + scopedTableIndex domainSize tail

/-- Lookup of a literal local table on the labels selected by its scope. -/
def scopedTableValue
    (domainSize : Nat) (scope : List Nat) (table : List Q')
    (labelling : EdgeLabelling) : Q' :=
  table.getD
    (scopedTableIndex domainSize (scope.map labelling)) 0

/-- Any literal table defines a scoped factor with a kernel-checked locality
law.  Cardinality and value correctness are checked separately by the local
equation contract. -/
def scopedTableFactor
    (domainSize : Nat) (scope : List Nat) (table : List Q') :
    ScopedQFactor where
  scope := scope
  value := scopedTableValue domainSize scope table
  local_eq := by
    intro left right hagree
    unfold scopedTableValue
    apply congrArg (fun index => table.getD index 0)
    apply congrArg (scopedTableIndex domainSize)
    apply List.map_congr_left
    intro id hid
    exact hagree id hid

/-- Sparse lookup by table index; absent entries are exactly zero. -/
def scopedSparseTableLookup
    (entries : List (Nat × Q')) (index : Nat) : Q' :=
  ((entries.find? fun entry => decide (entry.1 = index)).map Prod.snd).getD 0

/-- A sparse literal table reads the index selected by its scope. -/
def scopedSparseTableValue
    (domainSize : Nat) (scope : List Nat)
    (entries : List (Nat × Q')) (labelling : EdgeLabelling) : Q' :=
  scopedSparseTableLookup entries
    (scopedTableIndex domainSize (scope.map labelling))

/-- Sparse literal tables are scoped factors by the same structural locality
argument as dense tables. -/
def scopedSparseTableFactor
    (domainSize : Nat) (scope : List Nat)
    (entries : List (Nat × Q')) : ScopedQFactor where
  scope := scope
  value := scopedSparseTableValue domainSize scope entries
  local_eq := by
    intro left right hagree
    unfold scopedSparseTableValue
    apply congrArg (scopedSparseTableLookup entries)
    apply congrArg (scopedTableIndex domainSize)
    apply List.map_congr_left
    intro id hid
    exact hagree id hid

/-- The indexer agrees with the length of the complete Cartesian table. -/
theorem scopedTableIndex_lt_pow
    {domainSize : Nat} : ∀ {labels : List Nat},
    (∀ label, label ∈ labels → label < domainSize) →
      scopedTableIndex domainSize labels < domainSize ^ labels.length
  | [], _ => by simp [scopedTableIndex]
  | head :: tail, hbounded => by
      have hhead := hbounded head List.mem_cons_self
      have htail := scopedTableIndex_lt_pow
        (labels := tail)
        (fun label hlabel =>
          hbounded label (List.mem_cons_of_mem head hlabel))
      simp only [scopedTableIndex, List.length_cons, Nat.pow_succ]
      calc
        head * domainSize ^ tail.length + scopedTableIndex domainSize tail <
            head * domainSize ^ tail.length +
              domainSize ^ tail.length :=
          Nat.add_lt_add_left htail _
        _ = (head + 1) * domainSize ^ tail.length := by
          rw [Nat.add_mul, Nat.one_mul]
        _ ≤ domainSize * domainSize ^ tail.length :=
          Nat.mul_le_mul_right (domainSize ^ tail.length)
            (Nat.succ_le_of_lt hhead)
        _ = domainSize ^ tail.length * domainSize :=
          Nat.mul_comm _ _

/-- Product of a finite family of scoped factors. -/
def scopedFactorProduct
    (factors : List ScopedQFactor) (labelling : EdgeLabelling) : Q' :=
  listQProduct (fun factor => factor.value labelling) factors

private theorem listQSum_congr_eq_local
    {Item : Type} {left right : Item → Q'} : ∀ items : List Item,
    (∀ item, item ∈ items → left item = right item) →
      listQSum left items = listQSum right items
  | [], _ => rfl
  | head :: tail, hagree => by
      change left head + listQSum left tail =
        right head + listQSum right tail
      rw [hagree head List.mem_cons_self,
        listQSum_congr_eq_local tail
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem head hitem))]

theorem scopedFactorProduct_local_eq
    (factors : List ScopedQFactor) (left right : EdgeLabelling)
    (hagree : ∀ factor, factor ∈ factors →
      ∀ id, id ∈ factor.scope → left id = right id) :
    scopedFactorProduct factors left =
      scopedFactorProduct factors right := by
  unfold scopedFactorProduct
  apply listQProduct_congr
  intro factor hfactor
  exact factor.local_eq left right (hagree factor hfactor)

/-- Restrict a labelling to a listed coordinate scope and set every other
coordinate to zero.  Repeated coordinates are harmless for membership; the
agreement theorem below asks for `Nodup`. -/
def restrictEdgeLabelling : List Nat → EdgeLabelling → EdgeLabelling
  | [], _ => zeroEdgeLabelling
  | edge :: rest, labelling =>
      setEdgeLabel (restrictEdgeLabelling rest labelling)
        edge (labelling edge)

/-- The explicit restriction belongs to the cutoff-bounded Cartesian
enumeration whenever the original labels are bounded on the scope. -/
theorem restrictEdgeLabelling_mem_bounded
    (K : Nat) (labelling : EdgeLabelling) : ∀ scope : List Nat,
    (∀ id, id ∈ scope → labelling id < K + 1) →
      restrictEdgeLabelling scope labelling ∈
        boundedEdgeLabellings K scope
  | [], _ => List.mem_singleton.mpr rfl
  | edge :: rest, hbounded => by
      unfold restrictEdgeLabelling boundedEdgeLabellings
      apply List.mem_flatMap.mpr
      refine ⟨labelling edge,
        List.mem_range.mpr (hbounded edge List.mem_cons_self), ?_⟩
      apply List.mem_map.mpr
      refine ⟨restrictEdgeLabelling rest labelling,
        restrictEdgeLabelling_mem_bounded K labelling rest
          (fun id hid =>
            hbounded id (List.mem_cons_of_mem edge hid)), rfl⟩

/-- On a duplicate-free scope, explicit restriction preserves every listed
coordinate exactly. -/
theorem restrictEdgeLabelling_agrees
    (labelling : EdgeLabelling) : ∀ (scope : List Nat),
    scope.Nodup → ∀ id, id ∈ scope →
      restrictEdgeLabelling scope labelling id = labelling id
  | [], _, id, hid => absurd hid List.not_mem_nil
  | edge :: rest, hnodup, id, hid => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hid with rfl | hrest
      · simp [restrictEdgeLabelling, setEdgeLabel]
      · have hne : id ≠ edge := by
          intro heq
          subst id
          exact hparts.1 hrest
        simp only [restrictEdgeLabelling, setEdgeLabel, if_neg hne]
        exact restrictEdgeLabelling_agrees labelling rest hparts.2 id hrest

/-- Executable pointwise comparison on the complete bounded scope carrier. -/
def boundedLocalEquationCheck
    (K : Nat) (scope : List Nat)
    (left right : EdgeLabelling → Q') : Bool :=
  (boundedEdgeLabellings K scope).all fun labelling =>
    decide (left labelling ≈ right labelling)

/-- A proof tree that validates a Boolean predicate on a finite list in
bounded chunks.  Each chunk proof is a separate kernel constant in concrete
certificates, so checking a long finite computation does not require the
kernel to retain one monolithic reduction proof. -/
inductive ChunkedListAll
    {Item : Type} (chunkSize : Nat) (predicate : Item → Bool) :
    List Item → Type
  | done {items : List Item} (items_empty : items = []) :
      ChunkedListAll chunkSize predicate items
  | step {items : List Item}
      (head_checked : (items.take chunkSize).all predicate = true)
      (tail_checked :
        ChunkedListAll chunkSize predicate (items.drop chunkSize)) :
      ChunkedListAll chunkSize predicate items

namespace ChunkedListAll

/-- Chunk certificates compose to the ordinary whole-list `all` fact. -/
theorem all_eq_true
    {Item : Type} {chunkSize : Nat} {predicate : Item → Bool}
    {items : List Item}
    (certificate : ChunkedListAll chunkSize predicate items) :
    items.all predicate = true := by
  induction certificate with
  | done items_empty => simp [items_empty]
  | @step items head_checked tail_checked ih =>
      rw [← List.take_append_drop chunkSize items, List.all_append,
        head_checked, ih]
      rfl

end ChunkedListAll

/-- Soundness of a checked local equation.  Exhaustive checking scales with
the scope size, not with the number of coordinates in the ambient system. -/
theorem localEquation_of_check
    (K : Nat) (scope : List Nat) (left right : EdgeLabelling → Q')
    (hnodup : scope.Nodup)
    (hleftLocal : ∀ first second,
      (∀ id, id ∈ scope → first id = second id) →
        left first = left second)
    (hrightLocal : ∀ first second,
      (∀ id, id ∈ scope → first id = second id) →
        right first = right second)
    (hcheck : boundedLocalEquationCheck K scope left right = true)
    (labelling : EdgeLabelling)
    (hbounded : ∀ id, id ∈ scope → labelling id < K + 1) :
    left labelling ≈ right labelling := by
  let restricted := restrictEdgeLabelling scope labelling
  have hrestricted : restricted ∈ boundedEdgeLabellings K scope :=
    restrictEdgeLabelling_mem_bounded K labelling scope hbounded
  have hchecked : left restricted ≈ right restricted := by
    exact of_decide_eq_true
      (List.all_eq_true.mp hcheck restricted hrestricted)
  have hagree : ∀ id, id ∈ scope → restricted id = labelling id :=
    restrictEdgeLabelling_agrees labelling scope hnodup
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq (hleftLocal labelling restricted
      (fun id hid => (hagree id hid).symm)))
    (Q'.eqv_trans _ _ _ hchecked
      (Q'.eqv_of_eq (hrightLocal restricted labelling hagree)))

/-- Soundness wrapper for a local equation checked in independently compiled
chunks.  The trusted conclusion is identical to `localEquation_of_check`;
chunking changes only the size of individual executable proof terms. -/
theorem localEquation_of_chunked_check
    (K chunkSize : Nat) (scope : List Nat)
    (left right : EdgeLabelling → Q')
    (hnodup : scope.Nodup)
    (hleftLocal : ∀ first second,
      (∀ id, id ∈ scope → first id = second id) →
        left first = left second)
    (hrightLocal : ∀ first second,
      (∀ id, id ∈ scope → first id = second id) →
        right first = right second)
    (certificate : ChunkedListAll chunkSize
      (fun labelling => decide (left labelling ≈ right labelling))
      (boundedEdgeLabellings K scope))
    (labelling : EdgeLabelling)
    (hbounded : ∀ id, id ∈ scope → labelling id < K + 1) :
    left labelling ≈ right labelling := by
  apply localEquation_of_check K scope left right hnodup hleftLocal
    hrightLocal certificate.all_eq_true labelling hbounded

/-- Factors whose scopes contain the coordinate currently being eliminated. -/
def factorBucket
    (coordinate : Nat) (factors : List ScopedQFactor) :
    List ScopedQFactor :=
  factors.filter fun factor => decide (coordinate ∈ factor.scope)

/-- Factors independent of the coordinate currently being eliminated. -/
def factorOutside
    (coordinate : Nat) (factors : List ScopedQFactor) :
    List ScopedQFactor :=
  factors.filter fun factor => decide (coordinate ∉ factor.scope)

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- Filtering by dependence partitions the factor product, up to the
commutative rational setoid. -/
theorem scopedFactorProduct_partition
    (coordinate : Nat) (labelling : EdgeLabelling) :
    ∀ factors : List ScopedQFactor,
    scopedFactorProduct factors labelling ≈
      scopedFactorProduct (factorOutside coordinate factors) labelling *
        scopedFactorProduct (factorBucket coordinate factors) labelling
  | [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | factor :: factors => by
      have ih := scopedFactorProduct_partition coordinate labelling factors
      by_cases hdepends : coordinate ∈ factor.scope
      · simp only [scopedFactorProduct, factorOutside, factorBucket,
          List.filter_cons]
        simp only [hdepends, decide_true, not_true_eq_false,
          decide_false, Bool.false_eq_true, ↓reduceIte]
        let a := factor.value labelling
        let outside := scopedFactorProduct
          (factorOutside coordinate factors) labelling
        let bucket := scopedFactorProduct
          (factorBucket coordinate factors) labelling
        refine Q'.eqv_trans _ (a * (outside * bucket)) _
          (Q'.mul_eqv_congr_left a _ _ ih) ?_
        refine Q'.eqv_trans _ ((a * outside) * bucket) _
          (Q'.eqv_symm (Q'.mul_assoc_eqv a outside bucket)) ?_
        refine Q'.eqv_trans _ ((outside * a) * bucket) _
          (Q'.mul_eqv_congr_right _ _ bucket
            (Q'.mul_comm_eqv a outside)) ?_
        exact Q'.mul_assoc_eqv outside a bucket
      · simp only [scopedFactorProduct, factorOutside, factorBucket,
          List.filter_cons]
        simp only [hdepends, decide_false, not_false_eq_true,
          decide_true, Bool.false_eq_true, ↓reduceIte]
        let a := factor.value labelling
        let outside := scopedFactorProduct
          (factorOutside coordinate factors) labelling
        let bucket := scopedFactorProduct
          (factorBucket coordinate factors) labelling
        refine Q'.eqv_trans _ (a * (outside * bucket)) _
          (Q'.mul_eqv_congr_left a _ _ ih) ?_
        exact Q'.eqv_symm (Q'.mul_assoc_eqv a outside bucket)

/-- Outside factors are structurally unchanged when the eliminated
coordinate is overwritten. -/
theorem scopedFactorProduct_outside_set_eq
    (coordinate spin : Nat) (factors : List ScopedQFactor)
    (labelling : EdgeLabelling) :
    scopedFactorProduct (factorOutside coordinate factors)
        (setEdgeLabel labelling coordinate spin) =
      scopedFactorProduct (factorOutside coordinate factors) labelling := by
  apply scopedFactorProduct_local_eq
  intro factor hfactor id hid
  have hparts := List.mem_filter.mp hfactor
  have hnot : coordinate ∉ factor.scope := of_decide_eq_true hparts.2
  have hne : id ≠ coordinate := by
    intro heq
    subst id
    exact hnot hid
  simp [setEdgeLabel, hne]

/-- Exact local sum after eliminating one coordinate from a bucket. -/
def eliminatedBucketValue
    (K coordinate : Nat) (bucket : List ScopedQFactor)
    (labelling : EdgeLabelling) : Q' :=
  listQSum
    (fun spin => scopedFactorProduct bucket
      (setEdgeLabel labelling coordinate spin))
    (List.range (K + 1))

/-- Canonical active result scope inside a fixed duplicate-free universe. -/
def computedBucketScope
    (carrier : List Nat) (coordinate : Nat)
    (bucket : List ScopedQFactor) : List Nat :=
  carrier.filter fun id =>
    decide (id ≠ coordinate) &&
      bucket.any (fun factor => decide (id ∈ factor.scope))

/-- Materialized exact result table proposed entirely by Lean evaluation. -/
def computedBucketTable
    (K coordinate : Nat) (scope : List Nat)
    (bucket : List ScopedQFactor) : List Q' :=
  (allSeqs (K + 1) scope.length).map fun labels =>
    eliminatedBucketValue K coordinate bucket
      (wordToEdgeLabelling scope labels)

/-- Executable table factor produced by one sparse bucket contraction. -/
def computedBucketFactor
    (K coordinate : Nat) (scope : List Nat)
    (bucket : List ScopedQFactor) : ScopedQFactor :=
  scopedTableFactor (K + 1) scope
    (computedBucketTable K coordinate scope bucket)

/-- The eliminated bucket depends only on a scope covering every non-eliminated
coordinate of every bucket factor. -/
theorem eliminatedBucketValue_local_eq
    (K coordinate : Nat) (bucket : List ScopedQFactor)
    (resultScope : List Nat)
    (hcover : ∀ factor, factor ∈ bucket →
      ∀ id, id ∈ factor.scope → id ≠ coordinate → id ∈ resultScope)
    (left right : EdgeLabelling)
    (hagree : ∀ id, id ∈ resultScope → left id = right id) :
    eliminatedBucketValue K coordinate bucket left =
      eliminatedBucketValue K coordinate bucket right := by
  unfold eliminatedBucketValue
  apply listQSum_congr_eq_local
  intro spin hspin
  apply scopedFactorProduct_local_eq
  intro factor hfactor id hid
  by_cases hvar : id = coordinate
  · subst id
    simp [setEdgeLabel]
  · have hresult : id ∈ resultScope :=
      hcover factor hfactor id hid hvar
    have hidEq := hagree id hresult
    simp only [setEdgeLabel, if_neg hvar]
    exact hidEq

/-- A proof-carrying proposed result table for one bucket elimination. -/
structure CheckedBucketResult
    (K coordinate : Nat) (bucket : List ScopedQFactor) : Type where
  result : ScopedQFactor
  scope_nodup : result.scope.Nodup
  coordinate_not_scope : coordinate ∉ result.scope
  scope_cover_checked : bucket.all (fun factor =>
    factor.scope.all fun id =>
      decide (id = coordinate ∨ id ∈ result.scope)) = true
  table_checked :
    boundedLocalEquationCheck K result.scope result.value
      (eliminatedBucketValue K coordinate bucket) = true

/-- Compact externally proposed result data.  Only nonzero table entries are
stored; the coordinate being eliminated comes from the trace order. -/
structure SparseEliminationDatum : Type where
  scope : List Nat
  nonzeroEntries : List (Nat × Q')

namespace SparseEliminationDatum

def factor (K : Nat) (datum : SparseEliminationDatum) : ScopedQFactor :=
  scopedSparseTableFactor (K + 1) datum.scope datum.nonzeroEntries

end SparseEliminationDatum

/-- A trace entry may ask Lean to compute a small result table directly or
may provide a sparse literal table proposed by an external exact evaluator. -/
inductive EliminationTableDatum : Type
  | computed
  | sparse (datum : SparseEliminationDatum)

/-- Attempt to certify an arbitrary sparse literal result factor. -/
def checkedSparseBucketResult?
    (K coordinate : Nat) (bucket : List ScopedQFactor)
    (datum : SparseEliminationDatum) :
    Option (CheckedBucketResult K coordinate bucket) :=
  let result := datum.factor K
  if hnodup : result.scope.Nodup then
    if hcoordinate : coordinate ∉ result.scope then
      if hcover : bucket.all (fun factor =>
          factor.scope.all fun id =>
            decide (id = coordinate ∨ id ∈ result.scope)) = true then
        if htable : boundedLocalEquationCheck K result.scope result.value
            (eliminatedBucketValue K coordinate bucket) = true then
          some
            { result := result
              scope_nodup := hnodup
              coordinate_not_scope := hcoordinate
              scope_cover_checked := hcover
              table_checked := htable }
        else none
      else none
    else none
  else none

/-- Attempt to construct a checked bucket result by kernel evaluation of all
structural and local-table obligations. -/
def checkedComputedBucketResult?
    (K coordinate : Nat) (carrier : List Nat)
    (bucket : List ScopedQFactor) :
    Option (CheckedBucketResult K coordinate bucket) :=
  let scope := computedBucketScope carrier coordinate bucket
  let result := computedBucketFactor K coordinate scope bucket
  if hnodup : result.scope.Nodup then
    if hcoordinate : coordinate ∉ result.scope then
      if hcover : bucket.all (fun factor =>
          factor.scope.all fun id =>
            decide (id = coordinate ∨ id ∈ result.scope)) = true then
        if htable : boundedLocalEquationCheck K result.scope result.value
            (eliminatedBucketValue K coordinate bucket) = true then
          some
            { result := result
              scope_nodup := hnodup
              coordinate_not_scope := hcoordinate
              scope_cover_checked := hcover
              table_checked := htable }
        else none
      else none
    else none
  else none

namespace CheckedBucketResult

theorem scope_covers
    {K coordinate : Nat} {bucket : List ScopedQFactor}
    (certificate : CheckedBucketResult K coordinate bucket) :
    ∀ factor, factor ∈ bucket →
      ∀ id, id ∈ factor.scope → id ≠ coordinate →
        id ∈ certificate.result.scope := by
  intro factor hfactor id hid hne
  have hfactorCheck := List.all_eq_true.mp
    certificate.scope_cover_checked factor hfactor
  have hidCheck := List.all_eq_true.mp hfactorCheck id hid
  rcases of_decide_eq_true hidCheck with heq | hresult
  · exact False.elim (hne heq)
  · exact hresult

/-- A checked table is the exact eliminated bucket value on every bounded
global labelling, even when the ambient system has many more coordinates. -/
theorem result_correct
    {K coordinate : Nat} {bucket : List ScopedQFactor}
    (certificate : CheckedBucketResult K coordinate bucket)
    (labelling : EdgeLabelling)
    (hbounded : ∀ id, id ∈ certificate.result.scope →
      labelling id < K + 1) :
    certificate.result.value labelling ≈
      eliminatedBucketValue K coordinate bucket labelling := by
  exact localEquation_of_check K certificate.result.scope
    certificate.result.value
    (eliminatedBucketValue K coordinate bucket)
    certificate.scope_nodup certificate.result.local_eq
    (eliminatedBucketValue_local_eq K coordinate bucket
      certificate.result.scope certificate.scope_covers)
    certificate.table_checked labelling hbounded

end CheckedBucketResult

/-- One globally sound elimination step: the result scope lies among the
remaining coordinates, while its local table has passed the checked bucket
contract above. -/
structure CheckedScopedEliminationStep
    (K coordinate : Nat) (remaining : List Nat)
    (factors : List ScopedQFactor) : Type where
  bucketResult :
    CheckedBucketResult K coordinate (factorBucket coordinate factors)
  result_scope_remaining_checked :
    bucketResult.result.scope.all
      (fun id => decide (id ∈ remaining)) = true

/-- Attempt to construct one globally checked sparse elimination step. -/
def checkedComputedEliminationStep?
    (K coordinate : Nat) (remaining carrier : List Nat)
    (factors : List ScopedQFactor) :
    Option (CheckedScopedEliminationStep
      K coordinate remaining factors) :=
  match checkedComputedBucketResult? K coordinate carrier
      (factorBucket coordinate factors) with
  | none => none
  | some bucketResult =>
      if hremaining : bucketResult.result.scope.all
          (fun id => decide (id ∈ remaining)) = true then
        some
          { bucketResult := bucketResult
            result_scope_remaining_checked := hremaining }
      else none

/-- Attempt to certify one sparse literal step against the current factors. -/
def checkedSparseEliminationStep?
    (K coordinate : Nat) (remaining : List Nat)
    (factors : List ScopedQFactor) (datum : SparseEliminationDatum) :
    Option (CheckedScopedEliminationStep
      K coordinate remaining factors) :=
  match checkedSparseBucketResult? K coordinate
      (factorBucket coordinate factors) datum with
  | none => none
  | some bucketResult =>
      if hremaining : bucketResult.result.scope.all
          (fun id => decide (id ∈ remaining)) = true then
        some
          { bucketResult := bucketResult
            result_scope_remaining_checked := hremaining }
      else none

/-- Select and certify either a Lean-computed or sparse-literal step. -/
def checkedEliminationTableStep?
    (K coordinate : Nat) (remaining carrier : List Nat)
    (factors : List ScopedQFactor) (datum : EliminationTableDatum) :
    Option (CheckedScopedEliminationStep
      K coordinate remaining factors) :=
  match datum with
  | .computed =>
      checkedComputedEliminationStep?
        K coordinate remaining carrier factors
  | .sparse sparseDatum =>
      checkedSparseEliminationStep?
        K coordinate remaining factors sparseDatum

namespace CheckedScopedEliminationStep

theorem result_scope_remaining
    {K coordinate : Nat} {remaining : List Nat}
    {factors : List ScopedQFactor}
    (step : CheckedScopedEliminationStep K coordinate remaining factors) :
    ∀ id, id ∈ step.bucketResult.result.scope → id ∈ remaining := by
  intro id hid
  exact of_decide_eq_true
    (List.all_eq_true.mp step.result_scope_remaining_checked id hid)

/-- The factor family after one certified bucket elimination. -/
def afterFactors
    {K coordinate : Nat} {remaining : List Nat}
    {factors : List ScopedQFactor}
    (step : CheckedScopedEliminationStep K coordinate remaining factors) :
    List ScopedQFactor :=
  step.bucketResult.result :: factorOutside coordinate factors

/-- Pointwise algebra behind one elimination step. -/
theorem eliminatedFullProduct_eqv_after
    {K coordinate : Nat} {remaining : List Nat}
    {factors : List ScopedQFactor}
    (step : CheckedScopedEliminationStep K coordinate remaining factors)
    (labelling : EdgeLabelling)
    (hbounded : ∀ id, id ∈ remaining → labelling id < K + 1) :
    eliminatedBucketValue K coordinate factors labelling ≈
      scopedFactorProduct step.afterFactors labelling := by
  let outside := factorOutside coordinate factors
  let bucket := factorBucket coordinate factors
  have hpoint : ∀ spin,
      scopedFactorProduct factors
          (setEdgeLabel labelling coordinate spin) ≈
        scopedFactorProduct outside labelling *
          scopedFactorProduct bucket
            (setEdgeLabel labelling coordinate spin) := by
    intro spin
    exact Q'.eqv_trans _ _ _
      (scopedFactorProduct_partition coordinate
        (setEdgeLabel labelling coordinate spin) factors)
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_of_eq
          (scopedFactorProduct_outside_set_eq
            coordinate spin factors labelling)))
  have hsum : eliminatedBucketValue K coordinate factors labelling ≈
      scopedFactorProduct outside labelling *
        eliminatedBucketValue K coordinate bucket labelling := by
    unfold eliminatedBucketValue
    exact Q'.eqv_trans _ _ _
      (listQSum_congr hpoint (List.range (K + 1)))
      (listQSum_mul_left
        (scopedFactorProduct outside labelling)
        (fun spin => scopedFactorProduct bucket
          (setEdgeLabel labelling coordinate spin))
        (List.range (K + 1)))
  have hresult : step.bucketResult.result.value labelling ≈
      eliminatedBucketValue K coordinate bucket labelling := by
    apply step.bucketResult.result_correct
    intro id hid
    exact hbounded id (step.result_scope_remaining id hid)
  refine Q'.eqv_trans _ _ _ hsum ?_
  unfold afterFactors scopedFactorProduct
  exact Q'.eqv_trans _
    (scopedFactorProduct outside labelling *
      step.bucketResult.result.value labelling) _
    (Q'.mul_eqv_congr_left
      (scopedFactorProduct outside labelling) _ _
      (Q'.eqv_symm hresult))
    (Q'.mul_comm_eqv _ _)

/-- Exact partition sum of a finite scoped factor graph. -/
def scopedFactorPartitionSum
    (K : Nat) (coordinates : List Nat)
    (factors : List ScopedQFactor) : Q' :=
  listQSum (scopedFactorProduct factors)
    (boundedEdgeLabellings K coordinates)

private theorem scopedFactorPartitionSum_head_fubini
    (K coordinate : Nat) (remaining : List Nat)
    (factors : List ScopedQFactor) :
    scopedFactorPartitionSum K (coordinate :: remaining) factors ≈
      listQSum
        (fun labelling =>
          eliminatedBucketValue K coordinate factors labelling)
        (boundedEdgeLabellings K remaining) := by
  unfold scopedFactorPartitionSum
  refine Q'.eqv_trans _
    (YMGap.Continuum.BondMovingStep.fsum
      (fun spin =>
        listQSum
          (fun labelling => scopedFactorProduct factors
            (setEdgeLabel labelling coordinate spin))
          (boundedEdgeLabellings K remaining))
      (K + 1)) _
    (listQSum_bounded_cons K coordinate remaining
      (scopedFactorProduct factors)) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun spin =>
        listQSum
          (fun labelling => scopedFactorProduct factors
            (setEdgeLabel labelling coordinate spin))
          (boundedEdgeLabellings K remaining))
      (List.range (K + 1))) _
    (Q'.eqv_symm
      (listQSum_range_eq_fsum
        (fun spin =>
          listQSum
            (fun labelling => scopedFactorProduct factors
              (setEdgeLabel labelling coordinate spin))
            (boundedEdgeLabellings K remaining))
        (K + 1))) ?_
  exact listQSum_swap
    (fun labelling spin => scopedFactorProduct factors
      (setEdgeLabel labelling coordinate spin))
    (boundedEdgeLabellings K remaining)
    (List.range (K + 1))

/-- Global soundness of one checked local bucket elimination. -/
theorem partitionSum_eqv_after
    {K coordinate : Nat} {remaining : List Nat}
    {factors : List ScopedQFactor}
    (step : CheckedScopedEliminationStep K coordinate remaining factors) :
    scopedFactorPartitionSum K (coordinate :: remaining) factors ≈
      scopedFactorPartitionSum K remaining step.afterFactors := by
  refine Q'.eqv_trans _
    (listQSum
      (fun labelling =>
        eliminatedBucketValue K coordinate factors labelling)
      (boundedEdgeLabellings K remaining)) _
    (scopedFactorPartitionSum_head_fubini
      K coordinate remaining factors) ?_
  unfold scopedFactorPartitionSum
  apply listQSum_congr_on
  intro labelling hlabelling
  apply step.eliminatedFullProduct_eqv_after
  exact (boundedEdgeLabellings_sound K remaining
    labelling hlabelling).1

end CheckedScopedEliminationStep

open CheckedScopedEliminationStep

/-- A recursively replayable exact elimination trace.  Each constructor
removes the head coordinate and changes the factor family only through a
checked local bucket result. -/
inductive CheckedScopedEliminationTrace (K : Nat) :
    (coordinates : List Nat) → List ScopedQFactor → Type
  | done (factors : List ScopedQFactor) :
      CheckedScopedEliminationTrace K [] factors
  | step
      (coordinate : Nat) (remaining : List Nat)
      (factors : List ScopedQFactor)
      (head : CheckedScopedEliminationStep
        K coordinate remaining factors)
      (tail : CheckedScopedEliminationTrace
        K remaining head.afterFactors) :
      CheckedScopedEliminationTrace
        K (coordinate :: remaining) factors

/-- Fully executable construction of a recursive checked trace.  Failure of
any geometry, coverage, or table equation returns `none`. -/
def checkedComputedEliminationTrace?
    (K : Nat) (carrier : List Nat) :
    (coordinates : List Nat) → (factors : List ScopedQFactor) →
      Option (CheckedScopedEliminationTrace K coordinates factors)
  | [], factors => some (.done factors)
  | coordinate :: remaining, factors =>
      match checkedComputedEliminationStep?
          K coordinate remaining carrier factors with
      | none => none
      | some head =>
          match checkedComputedEliminationTrace?
              K carrier remaining head.afterFactors with
          | none => none
          | some tail =>
              some (.step coordinate remaining factors head tail)

/-- Replay a list of sparse literal result tables.  Any length mismatch or
failed local obligation returns `none`. -/
def checkedSparseEliminationTrace? (K : Nat) :
    (coordinates : List Nat) → (factors : List ScopedQFactor) →
      List SparseEliminationDatum →
        Option (CheckedScopedEliminationTrace K coordinates factors)
  | [], factors, [] => some (.done factors)
  | coordinate :: remaining, factors, datum :: data =>
      match checkedSparseEliminationStep?
          K coordinate remaining factors datum with
      | none => none
      | some head =>
          match checkedSparseEliminationTrace?
              K remaining head.afterFactors data with
          | none => none
          | some tail =>
              some (.step coordinate remaining factors head tail)
  | _, _, _ => none

/-- Replay a mixed trace, computing small tables inside Lean while using
sparse literals to cap memory at the widest stages. -/
def checkedEliminationTableTrace?
    (K : Nat) (carrier : List Nat) :
    (coordinates : List Nat) → (factors : List ScopedQFactor) →
      List EliminationTableDatum →
        Option (CheckedScopedEliminationTrace K coordinates factors)
  | [], factors, [] => some (.done factors)
  | coordinate :: remaining, factors, datum :: data =>
      match checkedEliminationTableStep?
          K coordinate remaining carrier factors datum with
      | none => none
      | some head =>
          match checkedEliminationTableTrace?
              K carrier remaining head.afterFactors data with
          | none => none
          | some tail =>
              some (.step coordinate remaining factors head tail)
  | _, _, _ => none

namespace CheckedScopedEliminationTrace

/-- Scalar obtained after all coordinates have been eliminated. -/
def bottomValue {K : Nat} :
    {coordinates : List Nat} → {factors : List ScopedQFactor} →
      CheckedScopedEliminationTrace K coordinates factors → Q'
  | [], _, .done factors =>
      scopedFactorProduct factors zeroEdgeLabelling
  | _ :: _, _, .step _ _ _ _ tail => tail.bottomValue

/-- Soundness of a complete sequence of locally checked bucket steps. -/
theorem partitionSum_eqv_bottom {K : Nat} :
    {coordinates : List Nat} → {factors : List ScopedQFactor} →
      (trace : CheckedScopedEliminationTrace K coordinates factors) →
        scopedFactorPartitionSum K coordinates factors ≈
          trace.bottomValue
  | [], _, .done factors => by
      unfold scopedFactorPartitionSum boundedEdgeLabellings
        listQSum bottomValue
      exact Q'.eqv_of_eq
        (Q'.add_zero' (scopedFactorProduct factors zeroEdgeLabelling))
  | _ :: _, _, .step coordinate remaining factors head tail => by
      exact Q'.eqv_trans _ _ _
        head.partitionSum_eqv_after
        (partitionSum_eqv_bottom tail)

end CheckedScopedEliminationTrace

end YMGap.Continuum.FiniteScopedFactorTableCertificate

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.FiniteScopedFactorTableCertificate.localEquation_of_check
#print axioms
  YMGap.Continuum.FiniteScopedFactorTableCertificate.ChunkedListAll.all_eq_true
#print axioms
  YMGap.Continuum.FiniteScopedFactorTableCertificate.localEquation_of_chunked_check
#print axioms
  YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedBucketResult.result_correct
#print axioms
  YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep.partitionSum_eqv_after
#print axioms
  YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationTrace.partitionSum_eqv_bottom
