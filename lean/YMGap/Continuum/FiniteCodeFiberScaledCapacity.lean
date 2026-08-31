/-
# Scaling a finite code partition with unit fiber capacity

Suppose every item carries a code in one explicit finite carrier and each
fixed-code fiber has total nonnegative weight at most one.  Exact finite
fiber partition then bounds the complete weight by the carrier length.
Multiplying every item by `invSucc carrier.length` gives unit total capacity.

The use of `length + 1` avoids any predecessor or nonemptiness branch.  It is
slightly weaker than division by a known-positive carrier length but remains
strictly positive and cutoff-independent whenever the carrier is fixed.

Constructive contract: finite representative fibers, one-occurrence deletion,
and exact rational order only.  No `Classical`, choice, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Constructive.CauchyConv
import YMGap.Continuum.FiniteKeyRepresentativePartition

namespace YMGap.Continuum.FiniteCodeFiberScaledCapacity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private def removeOneLocal {A : Type} [DecidableEq A]
    (item : A) : List A → List A
  | [] => []
  | head :: tail =>
      if head = item then tail else head :: removeOneLocal item tail

private theorem removeOneLocal_length {A : Type} [DecidableEq A]
    (item : A) : ∀ items : List A,
    item ∈ items → (removeOneLocal item items).length + 1 = items.length
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      show (if head = item then tail
        else head :: removeOneLocal item tail).length + 1 =
          (head :: tail).length
      by_cases heq : head = item
      · rw [if_pos heq, List.length_cons]
      · rw [if_neg heq, List.length_cons, List.length_cons]
        have htail : item ∈ tail := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim (heq hhead.symm)
          · exact htail
        have ih := removeOneLocal_length item tail htail
        omega

private theorem mem_removeOneLocal_of_ne {A : Type} [DecidableEq A]
    (item : A) : ∀ items : List A, ∀ other : A,
    other ∈ items → other ≠ item →
      other ∈ removeOneLocal item items
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, other, hmem, hne => by
      show other ∈ (if head = item then tail
        else head :: removeOneLocal item tail)
      by_cases heq : head = item
      · rw [if_pos heq]
        rcases List.mem_cons.mp hmem with hhead | htail
        · exact False.elim (hne (hhead.trans heq))
        · exact htail
      · rw [if_neg heq]
        rcases List.mem_cons.mp hmem with hhead | htail
        · rw [hhead]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _
            (mem_removeOneLocal_of_ne item tail other htail hne)

private theorem nodup_subset_length_le_local
    {A : Type} [DecidableEq A] : ∀ left right : List A,
    left.Nodup →
      (∀ item, item ∈ left → item ∈ right) →
      left.length ≤ right.length
  | [], _, _, _ => Nat.zero_le _
  | head :: tail, right, hleft, hsubset => by
      have hhead : head ∈ right := hsubset head List.mem_cons_self
      have hparts := List.nodup_cons.mp hleft
      have htail : ∀ item, item ∈ tail →
          item ∈ removeOneLocal head right := by
        intro item hitem
        have hne : item ≠ head := by
          intro heq
          apply hparts.1
          rw [← heq]
          exact hitem
        exact mem_removeOneLocal_of_ne head right item
          (hsubset item (List.mem_cons_of_mem head hitem)) hne
      have ih := nodup_subset_length_le_local tail
        (removeOneLocal head right) hparts.2 htail
      have hlength := removeOneLocal_length head right hhead
      show tail.length + 1 ≤ right.length
      omega

private theorem listQSum_le_length_mul_local
    {A : Type} (value : A → Q') {bound : Q'}
    (hboundNonnegative : (0 : Q') ≤ bound) : ∀ items : List A,
    (∀ item, item ∈ items → value item ≤ bound) →
      listQSum value items ≤ Q'.ofNat items.length * bound
  | [], _ => Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail := listQSum_le_length_mul_local
        value hboundNonnegative tail
        (fun item hitem => hbound item (List.mem_cons_of_mem head hitem))
      refine Q'.le_trans' _ _ _ (Q'.add_le_add hhead htail) ?_
      refine Q'.le_of_eqv (Q'.eqv_symm ?_)
      refine Q'.eqv_trans _ ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ bound
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + (1 : Q') * bound) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 bound) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + bound) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
        (Q'.add_comm_eqv (Q'.ofNat tail.length * bound) bound)

def codeFiber {Item Code : Type} [DecidableEq Code]
    (items : List Item) (code : Item → Code) (key : Code) : List Item :=
  items.filter fun item => decide (key = code item)

theorem mem_codeFiber_iff {Item Code : Type} [DecidableEq Code]
    (items : List Item) (code : Item → Code) (key : Code) (item : Item) :
    item ∈ codeFiber items code key ↔
      item ∈ items ∧ key = code item := by
  unfold codeFiber
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]

theorem codeFiber_eq_representativeFiber
    {Item Code : Type} [DecidableEq Code]
    (items : List Item) (code : Item → Code) (representative : Item) :
    codeFiber items code (code representative) =
      representativeFiber items code representative :=
  rfl

/-- If every realized code fiber has capacity one, the complete item weight
is bounded by the number of available codes. -/
theorem listQSum_le_codeSpace_length
    {Item Code : Type} [DecidableEq Code]
    (items : List Item) (weight : Item → Q') (code : Item → Code)
    (codeSpace : List Code)
    (hcodeMem : ∀ item, item ∈ items → code item ∈ codeSpace)
    (hfiber : ∀ key, key ∈ codeSpace →
      listQSum weight (codeFiber items code key) ≤ (1 : Q')) :
    listQSum weight items ≤ Q'.ofNat codeSpace.length := by
  let representatives := keyRepresentatives code items
  have hpartition := keyRepresentativeFibers_weight_total items weight code
  have houter :
      listQSum
          (fun representative =>
            listQSum weight
              (representativeFiber items code representative))
          representatives ≤ Q'.ofNat representatives.length * (1 : Q') := by
    apply listQSum_le_length_mul_local
    · exact Q'.zero_le_one
    · intro representative hrepresentative
      rw [← codeFiber_eq_representativeFiber]
      apply hfiber
      exact hcodeMem representative
        (keyRepresentatives_mem_source code items representative
          hrepresentative)
  have hrepresentativeLength : representatives.length ≤ codeSpace.length := by
    have hkeys := keyRepresentatives_keys_nodup code items
    have hsubset : ∀ key, key ∈ representatives.map code →
        key ∈ codeSpace := by
      intro key hkey
      obtain ⟨representative, hrepresentative, rfl⟩ := List.mem_map.mp hkey
      exact hcodeMem representative
        (keyRepresentatives_mem_source code items representative
          hrepresentative)
    have hlength := nodup_subset_length_le_local
      (representatives.map code) codeSpace hkeys hsubset
    simpa only [List.length_map] using hlength
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hpartition))
    (Q'.le_trans' _ _ _ houter
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.ofNat representatives.length)))
        (Q'.ofNat_le_ofNat hrepresentativeLength)))

/-- Scaling by the positive reciprocal of one more than the code-carrier
length turns the complete code-partitioned family into unit capacity. -/
theorem listQSum_invSucc_codeSpace_length_mul_le_one
    {Item Code : Type} [DecidableEq Code]
    (items : List Item) (weight : Item → Q') (code : Item → Code)
    (codeSpace : List Code)
    (hcodeMem : ∀ item, item ∈ items → code item ∈ codeSpace)
    (hfiber : ∀ key, key ∈ codeSpace →
      listQSum weight (codeFiber items code key) ≤ (1 : Q')) :
    listQSum
        (fun item => Q'.invSucc codeSpace.length * weight item)
        items ≤ (1 : Q') := by
  have htotal := listQSum_le_codeSpace_length
    items weight code codeSpace hcodeMem hfiber
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (listQSum weight items) (Q'.ofNat codeSpace.length)
    (Q'.invSucc codeSpace.length) htotal
    (Q'.invSucc_nonneg codeSpace.length)
  have hcount : Q'.ofNat codeSpace.length ≤
      Q'.ofNat (codeSpace.length + 1) :=
    Q'.ofNat_le_ofNat (Nat.le_succ codeSpace.length)
  have hscaledCount := Q'.mul_le_mul_of_nonneg_left
    (Q'.ofNat codeSpace.length) (Q'.ofNat (codeSpace.length + 1))
    (Q'.invSucc codeSpace.length) hcount
    (Q'.invSucc_nonneg codeSpace.length)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (listQSum_mul_left
      (Q'.invSucc codeSpace.length) weight items))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ hscaledCount
        (Q'.le_of_eqv
          (Q'.eqv_trans _ _ _
            (Q'.mul_comm_eqv
              (Q'.invSucc codeSpace.length)
              (Q'.ofNat (codeSpace.length + 1)))
            (Q'.ofNat_succ_mul_invSucc codeSpace.length)))))

#print axioms codeFiber
#print axioms mem_codeFiber_iff
#print axioms listQSum_le_codeSpace_length
#print axioms listQSum_invSucc_codeSpace_length_mul_le_one

end YMGap.Continuum.FiniteCodeFiberScaledCapacity
