/-
# Local certificates for scoped-factor coordinate reindexing

A target factor is pulled back along an explicit inverse coordinate map.  A
small finite table check on the source scope then proves equality of the two
factor values on every bounded pair of globally compatible labellings.  The
last theorem composes paired factors without enumerating the global carrier.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteScopedFactorCoordinateReindex

namespace YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteScopedFactorCoordinateReindex
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- Pull a target labelling back to source coordinates. -/
def pullEdgeLabelling
    (inverse : Nat → Nat) (source : EdgeLabelling) : EdgeLabelling :=
  fun targetId => source (inverse targetId)

def pulledFactorValue
    (inverse : Nat → Nat) (targetFactor : ScopedQFactor)
    (source : EdgeLabelling) : Q' :=
  targetFactor.value (pullEdgeLabelling inverse source)

/-- The proposed inverse is correct on the local source scope. -/
def InverseOnScope
    (scope : List Nat) (rename inverse : Nat → Nat) : Prop :=
  ∀ id, id ∈ scope → inverse (rename id) = id

theorem pulledFactorValue_local_eq
    (rename inverse : Nat → Nat)
    (sourceFactor targetFactor : ScopedQFactor)
    (hscope : targetFactor.scope.Perm
      (sourceFactor.scope.map rename))
    (hinverse : InverseOnScope sourceFactor.scope rename inverse) :
    ∀ left right,
      (∀ id, id ∈ sourceFactor.scope → left id = right id) →
      pulledFactorValue inverse targetFactor left =
        pulledFactorValue inverse targetFactor right := by
  intro left right hagree
  unfold pulledFactorValue pullEdgeLabelling
  apply targetFactor.local_eq
  intro targetId htarget
  have hmapped : targetId ∈ sourceFactor.scope.map rename :=
    hscope.mem_iff.mp htarget
  rcases List.mem_map.mp hmapped with ⟨sourceId, hsource, rfl⟩
  rw [hinverse sourceId hsource]
  exact hagree sourceId hsource

/-- One bounded local table certifies a factor transport theorem for arbitrary
compatible global labellings. -/
theorem factorValue_eqv_under_of_check
    (K : Nat) (coordinates : List Nat)
    (rename inverse : Nat → Nat)
    (sourceFactor targetFactor : ScopedQFactor)
    (hsourceNodup : sourceFactor.scope.Nodup)
    (hsourceScope : ∀ id, id ∈ sourceFactor.scope →
      id ∈ coordinates)
    (htargetScope : targetFactor.scope.Perm
      (sourceFactor.scope.map rename))
    (hinverse : InverseOnScope sourceFactor.scope rename inverse)
    (hcheck : boundedLocalEquationCheck K sourceFactor.scope
      sourceFactor.value (pulledFactorValue inverse targetFactor) = true)
    (source target : EdgeLabelling)
    (hagree : LabellingsAgreeUnder coordinates rename source target)
    (hbounded : ∀ id, id ∈ coordinates → source id < K + 1) :
    sourceFactor.value source ≈ targetFactor.value target := by
  have hpulled : sourceFactor.value source ≈
      pulledFactorValue inverse targetFactor source :=
    localEquation_of_check K sourceFactor.scope
      sourceFactor.value (pulledFactorValue inverse targetFactor)
      hsourceNodup sourceFactor.local_eq
      (pulledFactorValue_local_eq rename inverse
        sourceFactor targetFactor htargetScope hinverse)
      hcheck source
      (fun id hid => hbounded id (hsourceScope id hid))
  have htarget : pulledFactorValue inverse targetFactor source =
      targetFactor.value target := by
    unfold pulledFactorValue pullEdgeLabelling
    apply targetFactor.local_eq
    intro targetId htargetId
    have hmapped : targetId ∈ sourceFactor.scope.map rename :=
      htargetScope.mem_iff.mp htargetId
    rcases List.mem_map.mp hmapped with ⟨sourceId, hsourceId, rfl⟩
    rw [hinverse sourceId hsourceId]
    exact (hagree sourceId (hsourceScope sourceId hsourceId)).symm
  exact Q'.eqv_trans _ _ _ hpulled (Q'.eqv_of_eq htarget)

/-- Small transparent insertion sort used by generated permutation checks.
Unlike the optimized library sort, it remains reducible across module
boundaries during kernel evaluation. -/
@[reducible] def checkedListInsert {Item : Type}
    (le : Item → Item → Bool) (item : Item) : List Item → List Item
  | [] => [item]
  | head :: tail =>
      if le item head then item :: head :: tail
      else head :: checkedListInsert le item tail

@[reducible] def checkedListSort {Item : Type}
    (le : Item → Item → Bool) : List Item → List Item
  | [] => []
  | head :: tail =>
      checkedListInsert le head (checkedListSort le tail)

theorem checkedListInsert_perm {Item : Type}
    (le : Item → Item → Bool) (item : Item) : ∀ items,
    (checkedListInsert le item items).Perm (item :: items)
  | [] => List.Perm.refl _
  | head :: tail => by
      cases hle : le item head
      · simp only [checkedListInsert, hle, Bool.false_eq_true, ↓reduceIte]
        exact (List.Perm.cons head
          (checkedListInsert_perm le item tail)).trans
            (List.Perm.swap item head tail)
      · simp only [checkedListInsert, hle, ↓reduceIte]
        exact List.Perm.refl _

theorem checkedListSort_perm {Item : Type}
    (le : Item → Item → Bool) : ∀ items,
    (checkedListSort le items).Perm items
  | [] => List.Perm.refl []
  | head :: tail =>
      (checkedListInsert_perm le head (checkedListSort le tail)).trans
        (List.Perm.cons head (checkedListSort_perm le tail))

/-- Constructive permutation checker for natural-number lists.  The standard
decider for `List.Perm` uses a classical equality fallback; transparent
sorting by an explicit Boolean order avoids importing `Classical.choice`. -/
def natListPermutationCheck (left right : List Nat) : Bool :=
  decide (checkedListSort (fun a b => decide (a ≤ b)) left =
    checkedListSort (fun a b => decide (a ≤ b)) right)

theorem natListPerm_of_check
    (left right : List Nat)
    (hcheck : natListPermutationCheck left right = true) :
    left.Perm right := by
  have heq :
      checkedListSort (fun a b => decide (a ≤ b)) left =
        checkedListSort (fun a b => decide (a ≤ b)) right :=
    of_decide_eq_true hcheck
  apply (checkedListSort_perm
    (fun a b => decide (a ≤ b)) left).symm.trans
  rw [heq]
  exact checkedListSort_perm (fun a b => decide (a ≤ b)) right

def finListPermutationCheck {n : Nat}
    (left right : List (Fin n)) : Bool :=
  decide (checkedListSort (fun a b => decide (a.val ≤ b.val)) left =
    checkedListSort (fun a b => decide (a.val ≤ b.val)) right)

theorem finListPerm_of_check {n : Nat}
    (left right : List (Fin n))
    (hcheck : finListPermutationCheck left right = true) :
    left.Perm right := by
  have heq :
      checkedListSort (fun a b => decide (a.val ≤ b.val)) left =
        checkedListSort (fun a b => decide (a.val ≤ b.val)) right :=
    of_decide_eq_true hcheck
  apply (checkedListSort_perm
    (fun a b => decide (a.val ≤ b.val)) left).symm.trans
  rw [heq]
  exact checkedListSort_perm
    (fun a b => decide (a.val ≤ b.val)) right

/-- A single executable Boolean packages every local side condition needed by
`factorValue_eqv_under_of_check`.  Generated certificates therefore contain
only factor pairs and `by decide`; the kernel reconstructs all scope,
inverse, bounded-table, and locality obligations. -/
def factorTransportCheck
    (K : Nat) (coordinates : List Nat)
    (rename inverse : Nat → Nat)
    (sourceFactor targetFactor : ScopedQFactor) : Bool :=
  decide sourceFactor.scope.Nodup &&
  sourceFactor.scope.all (fun id => decide (id ∈ coordinates)) &&
  natListPermutationCheck targetFactor.scope
    (sourceFactor.scope.map rename) &&
  sourceFactor.scope.all (fun id => decide (inverse (rename id) = id)) &&
  boundedLocalEquationCheck K sourceFactor.scope
    sourceFactor.value (pulledFactorValue inverse targetFactor)

theorem factorValue_eqv_under_of_transportCheck
    (K : Nat) (coordinates : List Nat)
    (rename inverse : Nat → Nat)
    (sourceFactor targetFactor : ScopedQFactor)
    (hcheck : factorTransportCheck K coordinates rename inverse
      sourceFactor targetFactor = true)
    (source target : EdgeLabelling)
    (hagree : LabellingsAgreeUnder coordinates rename source target)
    (hbounded : ∀ id, id ∈ coordinates → source id < K + 1) :
    sourceFactor.value source ≈ targetFactor.value target := by
  unfold factorTransportCheck at hcheck
  have hfinal := Eq.mp (Bool.and_eq_true _ _) hcheck
  have hinverseParts := Eq.mp (Bool.and_eq_true _ _) hfinal.1
  have htargetParts := Eq.mp (Bool.and_eq_true _ _) hinverseParts.1
  have hsourceParts := Eq.mp (Bool.and_eq_true _ _) htargetParts.1
  have hsourceNodup : sourceFactor.scope.Nodup :=
    of_decide_eq_true hsourceParts.1
  have hsourceScope : ∀ id, id ∈ sourceFactor.scope →
      id ∈ coordinates := by
    intro id hid
    exact of_decide_eq_true
      (List.all_eq_true.mp hsourceParts.2 id hid)
  have htargetScope : targetFactor.scope.Perm
      (sourceFactor.scope.map rename) :=
    natListPerm_of_check _ _ htargetParts.2
  have hinverse : InverseOnScope sourceFactor.scope rename inverse := by
    intro id hid
    exact of_decide_eq_true
      (List.all_eq_true.mp hinverseParts.2 id hid)
  exact factorValue_eqv_under_of_check
    K coordinates rename inverse sourceFactor targetFactor
    hsourceNodup hsourceScope htargetScope hinverse hfinal.2
    source target hagree hbounded

/-- Paired factor lists whose values transport under a coordinate renaming. -/
inductive FactorListTransport
    (K : Nat) (coordinates : List Nat) (rename : Nat → Nat) :
    List ScopedQFactor → List ScopedQFactor → Prop
  | nil : FactorListTransport K coordinates rename [] []
  | cons {sourceFactor targetFactor : ScopedQFactor}
      {sourceTail targetTail : List ScopedQFactor}
      (head_transport : ∀ source target,
        LabellingsAgreeUnder coordinates rename source target →
        (∀ id, id ∈ coordinates → source id < K + 1) →
        sourceFactor.value source ≈ targetFactor.value target)
      (tail_transport : FactorListTransport K coordinates rename
        sourceTail targetTail) :
      FactorListTransport K coordinates rename
        (sourceFactor :: sourceTail) (targetFactor :: targetTail)

theorem FactorListTransport.append
    {K : Nat} {coordinates : List Nat} {rename : Nat → Nat}
    {sourceLeft sourceRight targetLeft targetRight : List ScopedQFactor}
    (hleft : FactorListTransport K coordinates rename
      sourceLeft targetLeft)
    (hright : FactorListTransport K coordinates rename
      sourceRight targetRight) :
    FactorListTransport K coordinates rename
      (sourceLeft ++ sourceRight) (targetLeft ++ targetRight) := by
  induction hleft with
  | nil => exact hright
  | cons head_transport _ induction =>
      exact FactorListTransport.cons head_transport induction

/-- Executable checker for a whole ordered list of paired local transports. -/
def factorListTransportCheck
    (K : Nat) (coordinates : List Nat)
    (rename inverse : Nat → Nat) :
    List ScopedQFactor → List ScopedQFactor → Bool
  | [], [] => true
  | sourceFactor :: sourceTail, targetFactor :: targetTail =>
      factorTransportCheck K coordinates rename inverse
          sourceFactor targetFactor &&
        factorListTransportCheck K coordinates rename inverse
          sourceTail targetTail
  | _, _ => false

theorem factorListTransport_of_check
    (K : Nat) (coordinates : List Nat)
    (rename inverse : Nat → Nat) :
    ∀ sourceFactors targetFactors,
      factorListTransportCheck K coordinates rename inverse
        sourceFactors targetFactors = true →
      FactorListTransport K coordinates rename
        sourceFactors targetFactors
  | [], [], _ => FactorListTransport.nil
  | [], _ :: _, hcheck => by simp [factorListTransportCheck] at hcheck
  | _ :: _, [], hcheck => by simp [factorListTransportCheck] at hcheck
  | sourceFactor :: sourceTail, targetFactor :: targetTail, hcheck => by
      simp only [factorListTransportCheck, Bool.and_eq_true] at hcheck
      exact FactorListTransport.cons
        (factorValue_eqv_under_of_transportCheck
          K coordinates rename inverse sourceFactor targetFactor hcheck.1)
        (factorListTransport_of_check K coordinates rename inverse
          sourceTail targetTail hcheck.2)

/-- Reorder a factor list by an explicit list of in-range indices.  Using
`Fin` makes out-of-range generated certificates unrepresentable. -/
def reorderFactors
    (factors : List ScopedQFactor)
    (indices : List (Fin factors.length)) : List ScopedQFactor :=
  indices.map factors.get

/-- Version of `reorderFactors` whose index bound is a separately certified
literal.  This keeps large generated index lists definitionally small. -/
def reorderFactorsWithLength
    (factors : List ScopedQFactor) (n : Nat)
    (hlength : factors.length = n)
    (indices : List (Fin n)) : List ScopedQFactor :=
  indices.map fun index => factors.get (Fin.cast hlength.symm index)

theorem reorderFactors_perm
    (factors : List ScopedQFactor)
    (indices : List (Fin factors.length))
    (hindices : indices.Perm (List.finRange factors.length)) :
    (reorderFactors factors indices).Perm factors := by
  have hmapped := hindices.map factors.get
  simpa [reorderFactors, List.finRange, Function.comp_def] using hmapped

theorem reorderFactorsWithLength_perm
    (factors : List ScopedQFactor) (n : Nat)
    (hlength : factors.length = n)
    (indices : List (Fin n))
    (hindices : indices.Perm (List.finRange n)) :
    (reorderFactorsWithLength factors n hlength indices).Perm factors := by
  subst n
  simpa [reorderFactorsWithLength, reorderFactors] using
    reorderFactors_perm factors indices hindices

theorem scopedFactorProduct_eqv_of_listTransport
    {K : Nat} {coordinates : List Nat} {rename : Nat → Nat}
    {sourceFactors targetFactors : List ScopedQFactor}
    (htransport : FactorListTransport K coordinates rename
      sourceFactors targetFactors)
    (source target : EdgeLabelling)
    (hagree : LabellingsAgreeUnder coordinates rename source target)
    (hbounded : ∀ id, id ∈ coordinates → source id < K + 1) :
    scopedFactorProduct sourceFactors source ≈
      scopedFactorProduct targetFactors target := by
  induction htransport with
  | nil => exact Q'.eqv_refl 1
  | cons head_transport tail_transport induction =>
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (head_transport source target hagree hbounded)) ?_
      exact Q'.mul_eqv_congr_left _ _ _ induction

/-- The target factors may be listed in the source matching order.  A separate
finite permutation certificate then identifies that matched list with the
canonical target factor list, without requiring decidable equality of factors
(whose records contain functions and proofs). -/
theorem scopedFactorProduct_eqv_of_listTransport_perm
    {K : Nat} {coordinates : List Nat} {rename : Nat → Nat}
    {sourceFactors matchedTargetFactors targetFactors : List ScopedQFactor}
    (htransport : FactorListTransport K coordinates rename
      sourceFactors matchedTargetFactors)
    (hperm : matchedTargetFactors.Perm targetFactors)
    (source target : EdgeLabelling)
    (hagree : LabellingsAgreeUnder coordinates rename source target)
    (hbounded : ∀ id, id ∈ coordinates → source id < K + 1) :
    scopedFactorProduct sourceFactors source ≈
      scopedFactorProduct targetFactors target := by
  refine Q'.eqv_trans _ _ _
    (scopedFactorProduct_eqv_of_listTransport htransport
      source target hagree hbounded) ?_
  unfold scopedFactorProduct
  exact
    YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights.listQProduct_perm
      (fun factor => factor.value target) hperm

end YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate

#print axioms
  YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate.factorValue_eqv_under_of_check
#print axioms
  YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate.scopedFactorProduct_eqv_of_listTransport
#print axioms
  YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate.scopedFactorProduct_eqv_of_listTransport_perm
#print axioms
  YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate.factorValue_eqv_under_of_transportCheck
#print axioms
  YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate.factorListTransport_of_check
