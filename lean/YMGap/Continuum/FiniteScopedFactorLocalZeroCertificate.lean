/-
# Local zero certificates for finite scoped factor graphs

A large finite factor graph may vanish for a very small reason: at one
coordinate, the product of all incident factors has empty support.  This
module packages that observation as an executable certificate.  Lean checks
only the one-coordinate bucket table and then proves that every full product,
and hence the complete partition sum, is zero.

The certificate is useful when an external exact program identifies a local
conflict.  The external program is not trusted: scope containment and all
local values are rechecked by the kernel.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteScopedFactorComputedTernaryElimination

namespace YMGap.Continuum.FiniteScopedFactorLocalZeroCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorComputedTernaryElimination
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-- Check that the factors incident to one coordinate read no other
coordinate and that their complete local product is identically zero. -/
def factorBucketZeroCheck
    (K coordinate : Nat) (factors : List ScopedQFactor) : Bool :=
  let bucket := factorBucket coordinate factors
  factorsScopedByCheck [coordinate] bucket &&
    boundedLocalEquationCheck K [coordinate]
      (scopedFactorProduct bucket) (fun _ => 0)

/-- A checked one-coordinate conflict makes the incident bucket product zero
at every bounded global labelling. -/
theorem factorBucketProduct_eqv_zero_of_check
    {K coordinate : Nat} {factors : List ScopedQFactor}
    (hcheck : factorBucketZeroCheck K coordinate factors = true)
    (labelling : EdgeLabelling)
    (hbounded : labelling coordinate < K + 1) :
    scopedFactorProduct (factorBucket coordinate factors) labelling ≈ 0 := by
  have hparts := (Bool.and_eq_true _ _).mp hcheck
  have hscoped : FactorsScopedBy [coordinate]
      (factorBucket coordinate factors) :=
    factorsScopedBy_of_check hparts.1
  apply localEquation_of_check K [coordinate]
    (scopedFactorProduct (factorBucket coordinate factors))
    (fun _ => 0)
  · simp
  · intro left right hagree
    apply scopedFactorProduct_local_eq
    intro factor hfactor id hid
    exact hagree id (hscoped factor hfactor id hid)
  · intro _ _ _
    rfl
  · exact hparts.2
  · intro id hid
    rw [List.mem_singleton] at hid
    subst id
    exact hbounded

/-- A checked zero bucket annihilates the product of the entire factor list. -/
theorem scopedFactorProduct_eqv_zero_of_bucket_check
    {K coordinate : Nat} {factors : List ScopedQFactor}
    (hcheck : factorBucketZeroCheck K coordinate factors = true)
    (labelling : EdgeLabelling)
    (hbounded : labelling coordinate < K + 1) :
    scopedFactorProduct factors labelling ≈ 0 := by
  have hbucket := factorBucketProduct_eqv_zero_of_check
    hcheck labelling hbounded
  exact Q'.eqv_trans _ _ _
    (scopedFactorProduct_partition coordinate labelling factors)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        (scopedFactorProduct (factorOutside coordinate factors) labelling)
        _ _ hbucket)
      (Q'.mul_zero_eqv _))

/-- Products turn list append into multiplication, modulo rational setoid
equality. -/
theorem scopedFactorProduct_append
    (left right : List ScopedQFactor) (labelling : EdgeLabelling) :
    scopedFactorProduct (left ++ right) labelling ≈
      scopedFactorProduct left labelling *
        scopedFactorProduct right labelling := by
  induction left with
  | nil =>
      exact Q'.eqv_symm
        (Q'.one_mul_eqv (scopedFactorProduct right labelling))
  | cons head tail ih =>
      unfold scopedFactorProduct at *
      simp only [List.cons_append, listQProduct]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (head.value labelling) _ _ ih)
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

/-- Search a finite coordinate list for a checked local zero bucket. -/
def factorLocalZeroCheck
    (K : Nat) (coordinates : List Nat)
    (factors : List ScopedQFactor) : Bool :=
  coordinates.any fun coordinate =>
    factorBucketZeroCheck K coordinate factors

/-- A locally vanishing suffix annihilates a larger graph after arbitrary
prefix factors are restored. -/
theorem scopedFactorPartitionSum_append_eqv_zero_of_bucket_check
    (K : Nat) (coordinates : List Nat)
    (headFactors tailFactors : List ScopedQFactor)
    (coordinate : Nat) (hcoordinate : coordinate ∈ coordinates)
    (hcheck : factorBucketZeroCheck K coordinate tailFactors = true) :
    scopedFactorPartitionSum K coordinates
      (headFactors ++ tailFactors) ≈ 0 := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_congr_on
      (scopedFactorProduct (headFactors ++ tailFactors))
      (fun _ => 0)
      (boundedEdgeLabellings K coordinates)
      (fun labelling hlabelling => by
        have hbounded :=
          (boundedEdgeLabellings_sound K coordinates labelling
            hlabelling).1 coordinate hcoordinate
        have hsuffix :=
          scopedFactorProduct_eqv_zero_of_bucket_check
            hcheck labelling hbounded
        exact Q'.eqv_trans _ _ _
          (scopedFactorProduct_append headFactors tailFactors labelling)
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left
              (scopedFactorProduct headFactors labelling) _ _ hsuffix)
            (Q'.mul_zero_eqv _))))
    (listQSum_zero (boundedEdgeLabellings K coordinates))

/-- The search wrapper exposes the preceding one-coordinate theorem without
requiring a caller to name the witness. -/
theorem scopedFactorPartitionSum_append_eqv_zero_of_local_check
    (K : Nat) (coordinates : List Nat)
    (headFactors tailFactors : List ScopedQFactor)
    (hcheck : factorLocalZeroCheck K coordinates tailFactors = true) :
    scopedFactorPartitionSum K coordinates
      (headFactors ++ tailFactors) ≈ 0 := by
  obtain ⟨coordinate, hcoordinate, hcoordinateCheck⟩ :=
    List.any_eq_true.mp hcheck
  exact scopedFactorPartitionSum_append_eqv_zero_of_bucket_check
    K coordinates headFactors tailFactors coordinate
    hcoordinate hcoordinateCheck

end YMGap.Continuum.FiniteScopedFactorLocalZeroCertificate

#print axioms
  YMGap.Continuum.FiniteScopedFactorLocalZeroCertificate.factorBucketProduct_eqv_zero_of_check
#print axioms
  YMGap.Continuum.FiniteScopedFactorLocalZeroCertificate.scopedFactorProduct_eqv_zero_of_bucket_check
#print axioms
  YMGap.Continuum.FiniteScopedFactorLocalZeroCertificate.scopedFactorPartitionSum_append_eqv_zero_of_bucket_check
#print axioms
  YMGap.Continuum.FiniteScopedFactorLocalZeroCertificate.scopedFactorPartitionSum_append_eqv_zero_of_local_check
