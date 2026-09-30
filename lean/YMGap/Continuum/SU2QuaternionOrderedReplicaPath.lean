/-
# Arbitrarily ordered two-copy replacement path

Each coordinate is swapped exactly when its listed prefix reaches it. A
singleton increment is the prefix swap of the unweighted one-link
replacement difference; the same involution transports every supported
weighted Haar square. A permutation of the full lower range gives the
original-to-upper endpoints and the existing finite Cauchy certificate.
No interacting comparison or chronological-order assertion is made here.
-/

import YMGap.Continuum.SU2QuaternionReplicaPathTelescope
import YMGap.Continuum.SU2QuaternionReplicaPathIncrement
import YMGap.Continuum.SU2QuaternionDisjointPartialSwap

namespace YMGap.Continuum.SU2QuaternionOrderedReplicaPath

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionDisjointPartialSwap
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionReplicaPathTelescope
open YMGap.Continuum.SU2QuaternionReplicaPathIncrement
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Swap the listed lower coordinates, in any order, on the doubled carrier. -/
def selectedPrefix (n : Nat) (A : List Nat) (f : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial (swap n A) f

theorem selectedPrefix_supported (n : Nat) (A : List Nat) (f : RatPoly) :
    SupportedQuaternionBlocks (n+n) (selectedPrefix n A f) :=
  reindex_supported (swap n A) f

/-- The replacement difference before the earlier prefix is applied. -/
def singletonDifference (n j : Nat) (f : RatPoly) : RatPoly :=
  singleBlockDifference n j f

private theorem lower_supported {n : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks (n+n) f :=
  fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (by omega))

theorem singletonDifference_supported (n j : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks (n+n) (singletonDifference n j f) :=
  difference_supported (selectedPrefix_supported n [j] f) (lower_supported hf)

/-- The next replacement after an arbitrary already-selected list. -/
def increment (n : Nat) (A : List Nat) (j : Nat) (f : RatPoly) : RatPoly :=
  difference (selectedPrefix n (A ++ [j]) f) (selectedPrefix n A f)

theorem increment_supported (n : Nat) (A : List Nat) (j : Nat) (f : RatPoly) :
    SupportedQuaternionBlocks (n+n) (increment n A j f) :=
  difference_supported (selectedPrefix_supported n (A ++ [j]) f)
    (selectedPrefix_supported n A f)

/-- Disjoint prefix composition isolates the singleton replacement exactly
on the same doubled Haar carrier. -/
theorem increment_pin (n : Nat) (A : List Nat) (j : Nat) (hnot : j ∉ A)
    (f : RatPoly) :
    HaarCarrierEqv (n+n) (increment n A j f)
      (reindexQuaternionPolynomial (swap n A) (singletonDifference n j f)) := by
  have hdisj : ∀ i, i ∈ A → i ∉ [j] := by
    intro i hi hmem
    have heq := List.mem_singleton.mp hmem
    subst i
    exact hnot hi
  have hcomp := reindex_comp_carrier n A [j] hdisj f
  have hdiff : HaarCarrierEqv (n+n) (increment n A j f)
      (difference
        (reindexQuaternionPolynomial (swap n A)
          (reindexQuaternionPolynomial (swap n [j]) f))
        (reindexQuaternionPolynomial (swap n A) f)) :=
    HaarCarrierEqv.add hcomp.symm
      (HaarCarrierEqv.neg (HaarCarrierEqv.refl _
        (reindexQuaternionPolynomial (swap n A) f)))
  apply hdiff.trans
  unfold singletonDifference singleBlockDifference difference
  rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg]
  exact HaarCarrierEqv.refl _ _

/-- The singleton increment square is a reindexed one-link replacement
square. Orientation is immaterial only after forming this square. -/
theorem increment_square_pin (n : Nat) (A : List Nat) (j : Nat) (hnot : j ∉ A)
    (f : RatPoly) :
    HaarCarrierEqv (n+n) (polyMul (increment n A j f) (increment n A j f))
      (reindexQuaternionPolynomial (swap n A)
        (polyMul (singletonDifference n j f) (singletonDifference n j f))) := by
  have h := increment_pin n A j hnot f
  rw [reindexQuaternionPolynomial_mul]
  exact HaarCarrierEqv.mul h h

/-- The same prefix swap moves an arbitrary supported doubled-carrier
weight. No action factor is dropped; this is Haar change of variables. -/
theorem weighted_increment_transport (n : Nat) (A : List Nat) (j : Nat)
    (hnot : j ∉ A) (f weight : RatPoly)
    (hf : SupportedQuaternionBlocks n f)
    (hw : SupportedQuaternionBlocks (n+n) weight) :
    quaternionHaar (n+n)
        (polyMul weight (polyMul (increment n A j f) (increment n A j f))) ≈
      quaternionHaar (n+n)
        (polyMul (reindexQuaternionPolynomial (swap n A) weight)
          (polyMul (singletonDifference n j f) (singletonDifference n j f))) := by
  have hsq := increment_square_pin n A j hnot f
  have hsingle := singletonDifference_supported n j f hf
  exact Q'.eqv_trans _ _ _
    (haar_of_carrier (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ weight) hsq))
    (reindex_pair (swap n A) weight
      (polyMul (singletonDifference n j f) (singletonDifference n j f))
      hw (supported_polyMul hsingle hsingle))

/-- Consumer-facing version with the existing literal singleton replacement
polynomial on the right. The next index is explicitly in the lower carrier. -/
theorem weighted_singleton_increment_transport (n : Nat) (A : List Nat) (j : Nat)
    (_hj : j < n) (hnot : j ∉ A) (f weight : RatPoly)
    (hf : SupportedQuaternionBlocks n f)
    (hw : SupportedQuaternionBlocks (n+n) weight) :
    quaternionHaar (n+n)
        (polyMul weight (polyMul (increment n A j f) (increment n A j f))) ≈
      quaternionHaar (n+n)
        (polyMul (reindexQuaternionPolynomial (swap n A) weight)
          (polyMul (singleBlockDifference n j f) (singleBlockDifference n j f))) :=
  weighted_increment_transport n A j hnot f weight hf hw

/-- A genuinely ordered prefix; its list, not a canonical range, sets the
replacement schedule. -/
def orderedPrefix (n : Nat) (order : List Nat) (k : Nat) (f : RatPoly) : RatPoly :=
  selectedPrefix n (order.take k) f

theorem orderedPrefix_supported (n : Nat) (order : List Nat) (k : Nat)
    (f : RatPoly) : SupportedQuaternionBlocks (n+n) (orderedPrefix n order k f) :=
  selectedPrefix_supported n (order.take k) f

theorem orderedPrefix_zero (n : Nat) (order : List Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    HaarCarrierEqv (n+n) (orderedPrefix n order 0 f) f :=
  reindex_fixed n [] f hf (fun j _ hj => False.elim (List.not_mem_nil hj))

theorem orderedPrefix_full (n : Nat) (order : List Nat)
    (hperm : order.Perm (List.range n)) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    HaarCarrierEqv (n+n) (orderedPrefix n order n f) (liftBoundary n f) := by
  have hlen : order.length = n := by
    simpa only [List.length_range] using hperm.length_eq
  have htake : order.take n = order := by rw [← hlen, List.take_length]
  change HaarCarrierEqv (n+n)
    (reindexQuaternionPolynomial (swap n (order.take n)) f) (liftBoundary n f)
  rw [htake]
  exact reindex_to_lift n order f hf
    (fun j hj hnot => False.elim
      (hnot ((List.Perm.mem_iff hperm).mpr (List.mem_range.mpr hj))))

private theorem take_succ_getD : ∀ (order : List Nat) (k : Nat),
    k < order.length → order.take (k+1) = order.take k ++ [order.getD k 0]
  | [], _, hk => False.elim (Nat.not_lt_zero _ hk)
  | x::xs, 0, _ => rfl
  | x::xs, k+1, hk => by
      change x :: xs.take (k+1) = x :: (xs.take k ++ [xs.getD k 0])
      rw [take_succ_getD xs k (by simp only [List.length_cons] at hk; omega)]

private theorem getD_mem_of_lt : ∀ (order : List Nat) (k : Nat),
    k < order.length → order.getD k 0 ∈ order
  | [], _, hk => False.elim (Nat.not_lt_zero _ hk)
  | x::xs, 0, _ => List.mem_cons_self
  | x::xs, k+1, hk =>
      List.mem_cons_of_mem x (getD_mem_of_lt xs k (by simp only [List.length_cons] at hk; omega))

private theorem getD_not_mem_take : ∀ (order : List Nat), order.Nodup →
    ∀ k, k < order.length → order.getD k 0 ∉ order.take k
  | [], _, _, hk, _ => False.elim (Nat.not_lt_zero _ hk)
  | x::xs, hnodup, 0, _, hm => False.elim (List.not_mem_nil hm)
  | x::xs, hnodup, k+1, hk, hm => by
      have htail : xs.Nodup := (List.nodup_cons.mp hnodup).2
      have hhead : x ∉ xs := (List.nodup_cons.mp hnodup).1
      change xs.getD k 0 ∈ x :: xs.take k at hm
      rcases List.mem_cons.mp hm with heq | htake
      · exact hhead (heq ▸ getD_mem_of_lt xs k (by simp only [List.length_cons] at hk; omega))
      · exact getD_not_mem_take xs htail k
          (by simp only [List.length_cons] at hk; omega) htake

private theorem range_nodup (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy heq
      have hyk : y = k := List.mem_singleton.mp hy
      rw [heq, hyk] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)

/-- The next listed coordinate has not occurred in the preceding prefix. -/
theorem next_not_in_prefix (n : Nat) (order : List Nat)
    (hperm : order.Perm (List.range n)) (k : Nat) (hk : k < n) :
    order.getD k 0 ∉ order.take k := by
  have hlen : order.length = n := by
    simpa only [List.length_range] using hperm.length_eq
  have hk' : k < order.length := hlen ▸ hk
  have hnodup : order.Nodup := (List.Perm.nodup_iff hperm).2 (range_nodup n)
  exact getD_not_mem_take order hnodup k hk'

/-- The next entry in a full schedule is an actual lower-copy coordinate. -/
theorem next_in_range (n : Nat) (order : List Nat)
    (hperm : order.Perm (List.range n)) (k : Nat) (hk : k < n) :
    order.getD k 0 < n := by
  have hlen : order.length = n := by
    simpa only [List.length_range] using hperm.length_eq
  have hk' : k < order.length := hlen ▸ hk
  have hmem : order.getD k 0 ∈ List.range n :=
    (List.Perm.mem_iff hperm).mp (getD_mem_of_lt order k hk')
  exact List.mem_range.mp hmem

/-- An adjacent ordered difference is literally the arbitrary-prefix
increment at the next scheduled coordinate. -/
theorem ordered_increment_eq (n : Nat) (order : List Nat)
    (k : Nat) (hk : k < order.length) (f : RatPoly) :
    difference (orderedPrefix n order (k+1) f) (orderedPrefix n order k f) =
      increment n (order.take k) (order.getD k 0) f := by
  unfold orderedPrefix increment
  rw [take_succ_getD order k hk]

/-- One ordered step is the arbitrary-list singleton increment at its
actual next list entry; a permutation makes that entry fresh. -/
theorem ordered_increment_pin (n : Nat) (order : List Nat)
    (hperm : order.Perm (List.range n)) (k : Nat) (hk : k < n) (f : RatPoly) :
    HaarCarrierEqv (n+n)
      (difference (orderedPrefix n order (k+1) f) (orderedPrefix n order k f))
      (reindexQuaternionPolynomial (swap n (order.take k))
        (singletonDifference n (order.getD k 0) f)) := by
  have hlen : order.length = n := by
    simpa only [List.length_range] using hperm.length_eq
  have hk' : k < order.length := hlen ▸ hk
  rw [ordered_increment_eq n order k hk' f]
  exact increment_pin n (order.take k) (order.getD k 0)
    (next_not_in_prefix n order hperm k hk) f

/-- Weighted ordered-step transport to the pre-existing literal singleton
replacement square. The weight is moved by the same prefix swap. -/
theorem ordered_weighted_increment_transport (n : Nat) (order : List Nat)
    (hperm : order.Perm (List.range n)) (k : Nat) (hk : k < n)
    (f weight : RatPoly) (hf : SupportedQuaternionBlocks n f)
    (hw : SupportedQuaternionBlocks (n+n) weight) :
    quaternionHaar (n+n)
      (polyMul weight
        (polyMul
          (difference (orderedPrefix n order (k+1) f) (orderedPrefix n order k f))
          (difference (orderedPrefix n order (k+1) f) (orderedPrefix n order k f)))) ≈
    quaternionHaar (n+n)
      (polyMul (reindexQuaternionPolynomial (swap n (order.take k)) weight)
        (polyMul (singleBlockDifference n (order.getD k 0) f)
          (singleBlockDifference n (order.getD k 0) f))) := by
  have hlen : order.length = n := by
    simpa only [List.length_range] using hperm.length_eq
  rw [ordered_increment_eq n order k (hlen ▸ hk) f]
  exact weighted_singleton_increment_transport n (order.take k)
    (order.getD k 0) (next_in_range n order hperm k hk)
    (next_not_in_prefix n order hperm k hk) f weight hf hw

/-- The ordered path has the same exact endpoint square as any full
permutation of all lower blocks. -/
theorem ordered_end_square (n : Nat) (order : List Nat)
    (hperm : order.Perm (List.range n)) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    HaarCarrierEqv (n+n)
      (polyMul (difference (orderedPrefix n order n f) (orderedPrefix n order 0 f))
        (difference (orderedPrefix n order n f) (orderedPrefix n order 0 f)))
      (polyMul (difference f (liftBoundary n f))
        (difference f (liftBoundary n f))) := by
  have he : HaarCarrierEqv (n+n)
      (difference (orderedPrefix n order n f) (orderedPrefix n order 0 f))
      (difference (liftBoundary n f) f) :=
    HaarCarrierEqv.add (orderedPrefix_full n order hperm f hf)
      (HaarCarrierEqv.neg (orderedPrefix_zero n order f hf))
  exact (HaarCarrierEqv.mul he he).trans
    (RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 1) (.neg (.var 0)))
        (.add (.var 1) (.neg (.var 0))))
      (.mul (.add (.var 0) (.neg (.var 1)))
        (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => f | _ => liftBoundary n f)))

/-- The finite path Cauchy certificate is schedule-independent; only the
polynomial increments depend on the explicit permutation. -/
def ordered_path_cauchy_certificate (n : Nat) (order : List Nat)
    (hperm : order.Perm (List.range n)) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    Certificate (n+n)
      (polyAdd
        (polySmul (Q'.ofNat n)
          (polySum ((increments (orderedPrefix n order · f) n).map
            (fun q => polyMul q q))))
        (polyNeg (polyMul (difference f (liftBoundary n f))
          (difference f (liftBoundary n f))))) := by
  have C := path_cauchy_certificate (orderedPrefix n order · f) n
    (fun j _ => orderedPrefix_supported n order j f)
  exact .transport
    (HaarCarrierEqv.add (.refl _ _)
      (HaarCarrierEqv.neg (ordered_end_square n order hperm f hf).symm)) C

#print axioms selectedPrefix
#print axioms selectedPrefix_supported
#print axioms singletonDifference
#print axioms singletonDifference_supported
#print axioms increment
#print axioms increment_supported
#print axioms increment_pin
#print axioms increment_square_pin
#print axioms weighted_increment_transport
#print axioms weighted_singleton_increment_transport
#print axioms orderedPrefix
#print axioms orderedPrefix_supported
#print axioms orderedPrefix_zero
#print axioms orderedPrefix_full
#print axioms next_not_in_prefix
#print axioms next_in_range
#print axioms ordered_increment_eq
#print axioms ordered_increment_pin
#print axioms ordered_weighted_increment_transport
#print axioms ordered_end_square
#print axioms ordered_path_cauchy_certificate

end YMGap.Continuum.SU2QuaternionOrderedReplicaPath
