/-
# Shared-DAG certificates for finite scoped-factor elimination

Independent contractions often encounter the same local bucket.  A checked
elimination step naturally returns `result :: outside`; the next shared DAG
node may store those factors in a canonical order.  This module proves that a
finite permutation of the factor list preserves both the pointwise product
and the partition sum, and packages elimination followed by canonical
reordering as one reusable certified edge.

The result is a general computer-science theorem about memoized exact variable
elimination.  It does not trust a hash-consing producer or make an asymptotic
or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate

namespace YMGap.Continuum.FiniteScopedFactorDAGCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-- Factor multiplication is insensitive to a finite permutation of the
factor list. -/
theorem scopedFactorProduct_perm
    {left right : List ScopedQFactor}
    (hperm : left.Perm right) (labelling : EdgeLabelling) :
    scopedFactorProduct left labelling ≈
      scopedFactorProduct right labelling := by
  unfold scopedFactorProduct
  exact listQProduct_perm (fun factor => factor.value labelling) hperm

/-- The same factor-list permutation preserves every finite partition sum. -/
theorem scopedFactorPartitionSum_perm
    (K : Nat) (coordinates : List Nat)
    {left right : List ScopedQFactor}
    (hperm : left.Perm right) :
    scopedFactorPartitionSum K coordinates left ≈
      scopedFactorPartitionSum K coordinates right := by
  unfold scopedFactorPartitionSum
  exact listQSum_congr
    (fun labelling => scopedFactorProduct_perm hperm labelling)
    (boundedEdgeLabellings K coordinates)

/-- An identity-coordinate local table transport for every paired factor
lifts pointwise to the complete finite partition sum.  This is the bridge from
genuine production factors to hash-consed canonical literal factors. -/
theorem scopedFactorPartitionSum_eqv_of_identity_listTransport
    (K : Nat) (coordinates : List Nat)
    {sourceFactors targetFactors : List ScopedQFactor}
    (htransport : FactorListTransport K coordinates (fun id => id)
      sourceFactors targetFactors) :
    scopedFactorPartitionSum K coordinates sourceFactors ≈
      scopedFactorPartitionSum K coordinates targetFactors := by
  unfold scopedFactorPartitionSum
  apply listQSum_congr_on
  intro labelling hlabelling
  apply scopedFactorProduct_eqv_of_listTransport htransport
    labelling labelling
  · intro id _
    rfl
  · intro id hid
    exact (boundedEdgeLabellings_sound K coordinates labelling
      hlabelling).1 id hid

/-- One certified DAG edge: eliminate the stated coordinate exactly, then
permute the resulting factor family into the canonical representation of the
shared successor node. -/
structure CheckedReorderedEliminationStep
    (K coordinate : Nat) (remaining : List Nat)
    (beforeFactors afterFactors : List ScopedQFactor) : Type where
  step : CheckedScopedEliminationStep
    K coordinate remaining beforeFactors
  after_perm : step.afterFactors.Perm afterFactors

namespace CheckedReorderedEliminationStep

theorem partitionSum_eqv_after
    {K coordinate : Nat} {remaining : List Nat}
    {beforeFactors afterFactors : List ScopedQFactor}
    (edge : CheckedReorderedEliminationStep
      K coordinate remaining beforeFactors afterFactors) :
    scopedFactorPartitionSum K (coordinate :: remaining) beforeFactors ≈
      scopedFactorPartitionSum K remaining afterFactors := by
  exact Q'.eqv_trans _ _ _
    edge.step.partitionSum_eqv_after
    (scopedFactorPartitionSum_perm
      K remaining edge.after_perm)

end CheckedReorderedEliminationStep

/-- A compact path through canonical factor-list nodes.  The terminal factor
list is an explicit index of the type, so a generated certificate retains its
exact final scalar family without a projection or an existential choice. -/
inductive CheckedReorderedEliminationTrace (K : Nat) :
    (coordinates : List Nat) →
    (initialFactors terminalFactors : List ScopedQFactor) → Type
  | done (factors : List ScopedQFactor) :
      CheckedReorderedEliminationTrace K [] factors factors
  | step
      (coordinate : Nat) (remaining : List Nat)
      (beforeFactors afterFactors terminalFactors : List ScopedQFactor)
      (edge : CheckedReorderedEliminationStep
        K coordinate remaining beforeFactors afterFactors)
      (tail : CheckedReorderedEliminationTrace
        K remaining afterFactors terminalFactors) :
      CheckedReorderedEliminationTrace K
        (coordinate :: remaining) beforeFactors terminalFactors

namespace CheckedReorderedEliminationTrace

/-- A checked path composes its local DAG edges without rerunning any bucket
equation or relying on an untrusted graph traversal. -/
theorem partitionSum_eqv_terminal
    {K : Nat} {coordinates : List Nat}
    {initialFactors terminalFactors : List ScopedQFactor}
    (trace : CheckedReorderedEliminationTrace
      K coordinates initialFactors terminalFactors) :
    scopedFactorPartitionSum K coordinates initialFactors ≈
      scopedFactorPartitionSum K [] terminalFactors := by
  induction trace with
  | done => exact Q'.eqv_refl _
  | step _ _ _ _ _ edge _ induction =>
      exact Q'.eqv_trans _ _ _ edge.partitionSum_eqv_after induction

end CheckedReorderedEliminationTrace

end YMGap.Continuum.FiniteScopedFactorDAGCertificate

#print axioms
  YMGap.Continuum.FiniteScopedFactorDAGCertificate.scopedFactorProduct_perm
#print axioms
  YMGap.Continuum.FiniteScopedFactorDAGCertificate.scopedFactorPartitionSum_perm
#print axioms
  YMGap.Continuum.FiniteScopedFactorDAGCertificate.scopedFactorPartitionSum_eqv_of_identity_listTransport
#print axioms
  YMGap.Continuum.FiniteScopedFactorDAGCertificate.CheckedReorderedEliminationStep.partitionSum_eqv_after
#print axioms
  YMGap.Continuum.FiniteScopedFactorDAGCertificate.CheckedReorderedEliminationTrace.partitionSum_eqv_terminal
