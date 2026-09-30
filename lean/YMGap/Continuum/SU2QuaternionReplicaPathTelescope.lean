/-
# Finite replica-prefix path and its exact Cauchy certificate

The algebraic path telescopes from one original observable to its second
copy. The finite Cauchy certificate charges one squared increment per
coordinate with the literal path length. No interacting measure, edge-flow
normalization, or coercivity estimate is used here.
-/

import YMGap.Continuum.QuaternionHaarFiniteCauchyCertificate
import YMGap.Continuum.SU2QuaternionPartialSliceSwap
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.SU2QuaternionCoordinateColumnLift

namespace YMGap.Continuum.SU2QuaternionReplicaPathTelescope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarFiniteCauchyCertificate

def difference (right left : RatPoly) : RatPoly :=
  polyAdd right (polyNeg left)

def increments (p : Nat → RatPoly) (count : Nat) : List RatPoly :=
  (List.range count).map (fun j => difference (p (j+1)) (p j))

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem difference_supported {blocks : Nat} {right left : RatPoly}
    (hr : SupportedQuaternionBlocks blocks right)
    (hl : SupportedQuaternionBlocks blocks left) :
    SupportedQuaternionBlocks blocks (difference right left) :=
  supported_add hr (support_neg hl)

theorem increments_supported {blocks count : Nat} (p : Nat → RatPoly)
    (hp : ∀ j, j ≤ count → SupportedQuaternionBlocks blocks (p j)) :
    ∀ q, q ∈ increments p count → SupportedQuaternionBlocks blocks q := by
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  have hj' : j < count := List.mem_range.mp hj
  exact difference_supported (hp (j+1) (by omega)) (hp j (by omega))

private theorem increments_succ (p : Nat → RatPoly) (count : Nat) :
    RatPolyCoeffEqv (polySum (increments p (count+1)))
      (polyAdd (polySum (increments p count)) (difference (p (count+1)) (p count))) := by
  unfold increments
  rw [List.range_succ, List.map_append, List.map_singleton]
  exact (RatPolyCoeffEqv.polySum_append _ _).symm.trans
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _))

/-- The sum of adjacent polynomial differences is the endpoint difference,
as coefficient equality on the original carrier. -/
theorem increments_telescope (p : Nat → RatPoly) (count : Nat) :
    RatPolyCoeffEqv (polySum (increments p count)) (difference (p count) (p 0)) := by
  induction count with
  | zero =>
      exact (RatPolyCoeffEqv.zero_smul polyOne).symm.trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.const 0) (.add (.var 0) (.neg (.var 0)))
          (by decide) (fun _ => p 0))
  | succ count ih =>
      exact (increments_succ p count).trans
        ((ih.add (RatPolyCoeffEqv.refl _)).trans
          (coeffEvalExpr_eqv_of_normalize_eq
            (.add (.add (.var 1) (.neg (.var 0)))
              (.add (.var 2) (.neg (.var 1))))
            (.add (.var 2) (.neg (.var 0)))
            (by decide) (fun | 0 => p 0 | 1 => p count | _ => p (count+1))))

/-- A finite supported path pays exactly `count` times the sum of its
adjacent squares, not an exponential triangle constant. -/
def path_cauchy_certificate {blocks : Nat} (p : Nat → RatPoly) (count : Nat)
    (hp : ∀ j, j ≤ count → SupportedQuaternionBlocks blocks (p j)) :
    Certificate blocks
      (polyAdd
        (polySmul (Q'.ofNat count)
          (polySum ((increments p count).map (fun q => polyMul q q))))
        (polyNeg (polyMul (difference (p count) (p 0))
          (difference (p count) (p 0))))) := by
  have C := sum_square_certificate (increments p count) (increments_supported p hp)
  have hlen : (increments p count).length = count := by
    simp [increments]
  rw [hlen] at C
  have ht := increments_telescope p count
  exact Certificate.ofCoeff
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (ht.symm.mul ht.symm))) C

/-- The first `j` blocks of the lower copy have been exchanged. -/
def replicaPrefix (n j : Nat) (f : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial (swap n (List.range j)) f

theorem replicaPrefix_supported (n j : Nat) (f : RatPoly) :
    SupportedQuaternionBlocks (n+n) (replicaPrefix n j f) :=
  reindex_supported (swap n (List.range j)) f

theorem replicaPrefix_zero (n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    HaarCarrierEqv (n+n) (replicaPrefix n 0 f) f := by
  change HaarCarrierEqv (n+n) (reindexQuaternionPolynomial (swap n []) f) f
  exact reindex_fixed n [] f hf (fun j _ hj => False.elim (List.not_mem_nil hj))

theorem replicaPrefix_full (n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    HaarCarrierEqv (n+n) (replicaPrefix n n f) (liftBoundary n f) := by
  change HaarCarrierEqv (n+n)
    (reindexQuaternionPolynomial (swap n (List.range n)) f) (liftBoundary n f)
  exact reindex_to_lift n (List.range n) f hf
    (fun j hj hnot => False.elim (hnot (List.mem_range.mpr hj)))

/-- Endpoint square is the actual two-copy observable difference square;
the reversed endpoint orientation has the same square. -/
theorem replicaPrefix_end_square (n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    HaarCarrierEqv (n+n)
      (polyMul (difference (replicaPrefix n n f) (replicaPrefix n 0 f))
        (difference (replicaPrefix n n f) (replicaPrefix n 0 f)))
      (polyMul (difference f (liftBoundary n f))
        (difference f (liftBoundary n f))) := by
  have he : HaarCarrierEqv (n+n)
      (difference (replicaPrefix n n f) (replicaPrefix n 0 f))
      (difference (liftBoundary n f) f) :=
    HaarCarrierEqv.add (replicaPrefix_full n f hf)
      (HaarCarrierEqv.neg (replicaPrefix_zero n f hf))
  exact (HaarCarrierEqv.mul he he).trans
    (RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 1) (.neg (.var 0)))
        (.add (.var 1) (.neg (.var 0))))
      (.mul (.add (.var 0) (.neg (.var 1)))
        (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => f | _ => liftBoundary n f)))

/-- Explicit replica-prefix Cauchy certificate with the original endpoint
observable and the same doubled carrier throughout. -/
def replica_path_cauchy_certificate (n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    Certificate (n+n)
      (polyAdd
        (polySmul (Q'.ofNat n)
          (polySum ((increments (replicaPrefix n · f) n).map
            (fun q => polyMul q q))))
        (polyNeg (polyMul (difference f (liftBoundary n f))
          (difference f (liftBoundary n f))))) := by
  have C := path_cauchy_certificate (replicaPrefix n · f) n
    (fun j _ => replicaPrefix_supported n j f)
  exact .transport
    (HaarCarrierEqv.add (.refl _ _)
      (HaarCarrierEqv.neg (replicaPrefix_end_square n f hf).symm)) C

#print axioms difference
#print axioms increments
#print axioms difference_supported
#print axioms increments_supported
#print axioms increments_telescope
#print axioms path_cauchy_certificate
#print axioms replicaPrefix
#print axioms replicaPrefix_supported
#print axioms replicaPrefix_zero
#print axioms replicaPrefix_full
#print axioms replicaPrefix_end_square
#print axioms replica_path_cauchy_certificate

end YMGap.Continuum.SU2QuaternionReplicaPathTelescope
