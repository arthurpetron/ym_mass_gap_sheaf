/-
# Singleton conditional replica marginal with an independent upper exterior

The selected upper block is the only upper coordinate used by the partially
swapped energy. An upper-slice exterior independent of that block therefore
factors by exact product Haar. The lower exterior remains shared inside the
conditional determinant. No probability normalization or coercivity is used.
-/

import YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
import YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization
import YMGap.Continuum.SU2QuaternionHaarMarkovContraction
import YMGap.Continuum.QuaternionHaarPositiveWindowInverse

namespace YMGap.Continuum.SU2QuaternionConditionalReplicaMarginal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
open YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionHaarMarkovContraction (haar_split_pairing)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (haar_liftBoundary)
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem corrector_independent (j : Nat) (R : RatPoly)
    (hR : QuaternionBlockIndependent j R) :
    ∀ k, QuaternionBlockIndependent j (corrector R k)
  | 0 => by
      intro t ht
      exact False.elim (List.not_mem_nil ht)
  | k+1 => quaternionBlockIndependent_polyAdd
      (quaternionBlockIndependent_polyConst j 1)
      (quaternionBlockIndependent_polyMul
        (quaternionBlockIndependent_polyNeg hR)
        (corrector_independent j R hR k))

/-- Every finite reciprocal polynomial preserves an absent selected block.
This is termwise locality, not an inverse-function regularity assertion. -/
theorem reciprocal_independent (j : Nat) (p : RatPoly)
    (hp : QuaternionBlockIndependent j p) (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    QuaternionBlockIndependent j (reciprocal p u hu k) := by
  have hR : QuaternionBlockIndependent j (remainder p u hu) := by
    change QuaternionBlockIndependent j
      (polyAdd (polySmul (scale u hu) p) (polyNeg polyOne))
    exact quaternionBlockIndependent_polyAdd
      (quaternionBlockIndependent_polySmul _ hp)
      (quaternionBlockIndependent_polyNeg (quaternionBlockIndependent_polyConst j 1))
  exact quaternionBlockIndependent_polySmul _ (corrector_independent j _ hR k)

private theorem blockZero_of_independent {block : Nat} {p : RatPoly}
    (hp : QuaternionBlockIndependent block p) {t : RatTerm} (ht : t ∈ p) :
    BlockZero t.1 block := by
  intro component hc
  have h := exponentAt_clearQuaternionBlock_self t.1 block component hc
  rw [hp t ht] at h
  exact h

private theorem lowerLocal (n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    BlockLocal (n+n) (fun b => b < n) p := by
  intro t ht b hb hnot
  have heq : n + (b-n) = b := by omega
  rw [← heq]
  exact blockZero_of_independent (supported_upper_independent hp (b-n)) ht

private theorem local_mono {n : Nat} {P Q : Nat → Prop} {p : RatPoly}
    (hp : BlockLocal n P p) (h : ∀ b, b < n → P b → Q b) :
    BlockLocal n Q p := by
  intro t ht b hb hq
  exact hp t ht b hb (fun hP => hq (h b hb hP))

private theorem singletonSwapLocal (n j : Nat) (hj : j < n) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    BlockLocal (n+n) (fun b => b < n ∨ b = n+j)
      (replica n [j] p) := by
  apply (lowerLocal n hp).reindex (swap n [j])
  intro b hb hmap
  by_cases hlow : b < n
  · exact Or.inl hlow
  · have hk : b-n < n := by omega
    have heq : b = n+(b-n) := by omega
    rw [heq, swap_upper n [j] (b-n) hk] at hmap
    by_cases hbj : b-n = j
    · exact Or.inr (by omega)
    · simp only [List.mem_singleton, if_neg hbj] at hmap
      omega

private theorem singletonCoreLocal (n j : Nat) (hj : j < n) (A f C : RatPoly)
    (hA : SupportedQuaternionBlocks n A)
    (hf : SupportedQuaternionBlocks n f)
    (hC : SupportedQuaternionBlocks n C) :
    BlockLocal (n+n) (fun b => b < n ∨ b = n+j)
      (polyMul C (mixedEnergy n [j] A f f)) := by
  let hlow := fun {p : RatPoly} (hp : SupportedQuaternionBlocks n p) =>
    local_mono (Q := fun b => b < n ∨ b = n+j) (lowerLocal n hp) (fun _ _ h => Or.inl h)
  have hdiff : BlockLocal (n+n) (fun b => b < n ∨ b = n+j)
      (difference n [j] f) :=
    (hlow hf).add ((singletonSwapLocal n j hj hf).neg)
  exact (hlow hC).mul
    (((hlow hA).mul (singletonSwapLocal n j hj hA)).mul (hdiff.mul hdiff))

private theorem singletonCoreSupported (n j : Nat) (A f C : RatPoly)
    (hA : SupportedQuaternionBlocks n A)
    (hf : SupportedQuaternionBlocks n f)
    (hC : SupportedQuaternionBlocks n C) :
    SupportedQuaternionBlocks (n+n) (polyMul C (mixedEnergy n [j] A f f)) := by
  have hfirst {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
      SupportedQuaternionBlocks (n+n) p :=
    fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (by omega))
  have hneg {p : RatPoly} (hp : SupportedQuaternionBlocks (n+n) p) :
      SupportedQuaternionBlocks (n+n) (polyNeg p) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact hp s hs
  have hrepA := reindex_supported (swap n [j]) A
  have hrepF := reindex_supported (swap n [j]) f
  have hdiff : SupportedQuaternionBlocks (n+n) (difference n [j] f) :=
    supported_add (hfirst hf) (hneg hrepF)
  exact supported_polyMul (hfirst hC)
    (supported_polyMul (supported_polyMul (hfirst hA) hrepA)
      (supported_polyMul hdiff hdiff))

private theorem upperExteriorLocal (n j : Nat) (M : RatPoly)
    (hM : QuaternionBlockIndependent j M) :
    BlockLocal (n+n) (fun b => n ≤ b ∧ b ≠ n+j) (liftBoundary n M) := by
  intro t ht b hb hnot
  by_cases hlow : b < n
  · exact blockZero_of_independent (lift_lower_independent n M b hlow) ht
  · have heq : b = n+j := by
      by_cases h : b = n+j
      · exact h
      · exact False.elim (hnot ⟨by omega, h⟩)
    rw [heq]
    exact blockZero_of_independent (lift_upper_independent n hM) ht

private theorem singletonDisjoint (n j : Nat) (hj : j < n) (A f C M : RatPoly)
    (hA : SupportedQuaternionBlocks n A)
    (hf : SupportedQuaternionBlocks n f)
    (hC : SupportedQuaternionBlocks n C)
    (hM : QuaternionBlockIndependent j M) :
    BlockDisjoint (n+n) (polyMul C (mixedEnergy n [j] A f f))
      (liftBoundary n M) := by
  let hp := singletonCoreLocal n j hj A f C hA hf hC
  let hq := upperExteriorLocal n j M hM
  intro s hs t ht b hb
  by_cases ha : b < n ∨ b = n+j
  · exact Or.inr (hq t ht b hb (by
      intro hqallowed
      rcases ha with hlow | heq
      · exact (Nat.not_le_of_lt hlow) hqallowed.1
      · exact hqallowed.2 heq))
  · exact Or.inl (hp s hs b hb ha)

/-- One upper block is copied, while all exterior variables of the first
copy stay shared. The independent upper exterior factors as a separate
one-copy Haar mass; it is not inserted into the conditional determinant. -/
theorem singleton_conditional_replica_marginal (n j : Nat) (hj : j < n)
    (A f C M : RatPoly)
    (hA : SupportedQuaternionBlocks n A)
    (hf : SupportedQuaternionBlocks n f)
    (hC : SupportedQuaternionBlocks n C)
    (hM : SupportedQuaternionBlocks n M)
    (hCind : QuaternionBlockIndependent j C)
    (hMind : QuaternionBlockIndependent j M) :
    quaternionHaar (n+n)
        (polyMul (polyMul C (mixedEnergy n [j] A f f)) (liftBoundary n M)) ≈
      quaternionHaar n (polyMul C
        (polyAdd (covarianceNumerator [j] A f f)
          (covarianceNumerator [j] A f f))) * quaternionHaar n M := by
  have hcore := singletonCoreSupported n j A f C hA hf hC
  have hfactor := haar_product hcore (lift_supported hM n)
    (singletonDisjoint n j hj A f C M hA hf hC hMind)
  have hconditional := mixed_identity n [j] A f f C hA hf hf hC
    (by intro i hi; have heq := List.mem_singleton.mp hi; subst i; exact hCind)
    (by simp) (by intro i hi; have heq := List.mem_singleton.mp hi; subst i; exact hj)
  exact Q'.eqv_trans _ _ _ hfactor
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hconditional)
      (Q'.mul_eqv_congr_left _ _ _ (haar_liftBoundary n n M)))

#print axioms singleton_conditional_replica_marginal
#print axioms reciprocal_independent

end YMGap.Continuum.SU2QuaternionConditionalReplicaMarginal
