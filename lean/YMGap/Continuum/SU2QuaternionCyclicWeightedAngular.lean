/-
# Weighted angular energy under cyclic coordinate recoding
-/

import YMGap.Continuum.SU2QuaternionCyclicAngularEnergy

namespace YMGap.Continuum.SU2QuaternionCyclicWeightedAngular

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionBlockReversal
open YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
open YMGap.Continuum.SU2QuaternionCyclicRotationPeriod
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Cyclic coordinate rotation is multiplicative as an actual polynomial. -/
theorem cycleRotation_mul (n : Nat) (p q : RatPoly) :
    cycleRotation n (polyMul p q) =
      polyMul (cycleRotation n p) (cycleRotation n q) := by
  simp only [cycleRotation, reindexQuaternionPolynomial_mul]

/-- Every finite cyclic iterate is multiplicative. -/
theorem rotateIterate_mul (n : Nat) : ∀ (m : Nat) (p q : RatPoly),
    rotateIterate n m (polyMul p q) =
      polyMul (rotateIterate n m p) (rotateIterate n m q)
  | 0, _, _ => rfl
  | m+1, p, q => by
      change cycleRotation n (rotateIterate n m (polyMul p q)) = _
      rw [rotateIterate_mul n m, cycleRotation_mul]
      rfl

/-- Iterated cyclic recoding preserves every supported Haar pairing. -/
theorem rotateIterate_pairing_invariant (n m : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q) :
    quaternionHaar n
        (polyMul (rotateIterate n m p) (rotateIterate n m q)) ≈
      quaternionHaar n (polyMul p q) := by
  rw [← rotateIterate_mul]
  induction m with
  | zero => exact Q'.eqv_refl _
  | succ m ih =>
      change quaternionHaar n
          (cycleRotation n (rotateIterate n m (polyMul p q))) ≈ _
      unfold cycleRotation
      exact Q'.eqv_trans _ _ _
        (quaternionHaar_reindex (reverseBlocks n) _ (reindex_supported _ _))
        (Q'.eqv_trans _ _ _
          (quaternionHaar_reindex (reverseTailBlocks n) _
            (rotateIterate_supported n m (supported_polyMul hp hq))) ih)

/-- Appending one cyclic rotation on the right of an iterate. -/
theorem rotateIterate_succ_right (n m : Nat) (p : RatPoly) :
    rotateIterate n (m+1) p = rotateIterate n m (cycleRotation n p) := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
      change cycleRotation n (rotateIterate n (m+1) p) = _
      rw [ih]
      rfl

private theorem six_prefix
    {blocks : Nat} {left right : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 →
      QuaternionPrefixPolynomialEqv blocks (left i j) (right i j)) :
    QuaternionPrefixPolynomialEqv blocks (six left) (six right) := by
  unfold six
  exact (h 0 1 (by decide) (by decide)).append
    ((h 0 2 (by decide) (by decide)).append
      ((h 0 3 (by decide) (by decide)).append
        ((h 1 2 (by decide) (by decide)).append
          ((h 1 3 (by decide) (by decide)).append
            (h 2 3 (by decide) (by decide))))))

private theorem reindex_blockSquare_prefix
    {blocks block : Nat} (s : QuaternionBlockInvolution blocks)
    (hblock : block < blocks) (polynomial : RatPoly) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s
        (blockAngularSquare (s.map block) polynomial))
      (blockAngularSquare block (reindexQuaternionPolynomial s polynomial)) := by
  simpa only [blockAngularSquare, blockAngularDerivative, six,
    reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_mul] using
    (six_prefix (fun i j hi hj =>
      (reindex_blockAngularDerivative_prefix s hblock hi hj polynomial).mul
        (reindex_blockAngularDerivative_prefix s hblock hi hj polynomial)))

private theorem reindex_weighted_blockSquare
    {blocks block : Nat} (s : QuaternionBlockInvolution blocks)
    (hblock : block < blocks) (weight polynomial : RatPoly)
    (hweight : SupportedQuaternionBlocks blocks weight)
    (hpolynomial : SupportedQuaternionBlocks blocks polynomial) :
    quaternionHaar blocks (polyMul (reindexQuaternionPolynomial s weight)
      (blockAngularSquare block (reindexQuaternionPolynomial s polynomial))) ≈
    quaternionHaar blocks
      (polyMul weight (blockAngularSquare (s.map block) polynomial)) := by
  have hp := (QuaternionPrefixPolynomialEqv.refl blocks
      (reindexQuaternionPolynomial s weight)).mul
        (reindex_blockSquare_prefix s hblock polynomial)
  have hforward := quaternionHaar_prefixPolynomialEqv blocks hp
    (supported_polyMul (reindex_supported s weight)
      (reindex_supported s (blockAngularSquare (s.map block) polynomial)))
    (supported_polyMul (reindex_supported s weight)
      (blockAngularSquare_supported hblock (reindex_supported s polynomial)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hforward)
    (by
      simpa only [reindexQuaternionPolynomial_mul] using
        quaternionHaar_reindex s _
          (supported_polyMul hweight
            (blockAngularSquare_supported (s.map_lt block hblock) hpolynomial)))

private theorem one_rotation_weighted (n block : Nat) (hn : 0 < n)
    (hblock : block < n) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks n a)
    (hf : SupportedQuaternionBlocks n f) :
    quaternionHaar n (polyMul
      (polyMul (cycleRotation n a) (cycleRotation n a))
      (blockAngularSquare block (cycleRotation n f))) ≈
    quaternionHaar n (polyMul (polyMul a a)
      (blockAngularSquare ((block+1)%n) f)) := by
  let A := polyMul a a
  let At := reindexQuaternionPolynomial (reverseTailBlocks n) A
  let ft := reindexQuaternionPolynomial (reverseTailBlocks n) f
  have hA : SupportedQuaternionBlocks n A := supported_polyMul ha ha
  have hAt := reindex_supported (reverseTailBlocks n) A
  have hft := reindex_supported (reverseTailBlocks n) f
  have hout := reindex_weighted_blockSquare (reverseBlocks n) hblock At ft hAt hft
  have hb' := (reverseBlocks n).map_lt block hblock
  have hin := reindex_weighted_blockSquare (reverseTailBlocks n) hb' A f hA hf
  have hs := cycle_source n block hn hblock
  rw [← cycleRotation_mul n a a]
  exact Q'.eqv_trans _ _ _ hout
    (Q'.eqv_trans _ _ _ hin
      (Q'.eqv_of_eq (congrArg (fun b => quaternionHaar n
        (polyMul A (blockAngularSquare b f))) hs)))

private theorem rotateIterate_weighted_block (n : Nat) (hn : 0 < n) :
    ∀ (m block : Nat), block < n → ∀ (a f : RatPoly),
      SupportedQuaternionBlocks n a → SupportedQuaternionBlocks n f →
      quaternionHaar n (polyMul
        (polyMul (rotateIterate n m a) (rotateIterate n m a))
        (blockAngularSquare block (rotateIterate n m f))) ≈
      quaternionHaar n (polyMul (polyMul a a)
        (blockAngularSquare ((block+m)%n) f))
  | 0, block, hblock, _, _, _, _ => by
      rw [Nat.add_zero, Nat.mod_eq_of_lt hblock]
      rfl
  | m+1, block, hblock, a, f, ha, hf => by
      have hs := one_rotation_weighted n block hn hblock
        (rotateIterate n m a) (rotateIterate n m f)
        (rotateIterate_supported n m ha) (rotateIterate_supported n m hf)
      have hnext : (block+1)%n < n := Nat.mod_lt _ hn
      have hi := rotateIterate_weighted_block n hn m ((block+1)%n) hnext a f ha hf
      exact Q'.eqv_trans _ _ _ hs
        (Q'.eqv_trans _ _ _ hi
          (Q'.eqv_of_eq (congrArg (fun b => quaternionHaar n
            (polyMul (polyMul a a) (blockAngularSquare b f))) (by
              rw [Nat.add_mod ((block+1)%n) m, Nat.mod_mod, ← Nat.add_mod]
              congr 1
              omega))))

/-- Weighted head angular energy after `m<n` cyclic recodings is the original
weighted angular energy at block `m`. -/
theorem rotateIterate_head_weightedAngularSquare_haar_of_lt
    (tail m : Nat) (hm : m < tail+1) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    quaternionHaar (tail+1) (polyMul
      (polyMul (rotateIterate (tail+1) m a) (rotateIterate (tail+1) m a))
      (blockAngularSquare 0 (rotateIterate (tail+1) m f))) ≈
    quaternionHaar (tail+1)
      (polyMul (polyMul a a) (blockAngularSquare m f)) := by
  exact Q'.eqv_trans _ _ _
    (rotateIterate_weighted_block (tail+1) (by omega) m 0 (by omega) a f ha hf)
    (Q'.eqv_of_eq (congrArg (fun b => quaternionHaar (tail+1)
      (polyMul (polyMul a a) (blockAngularSquare b f))) (by
        simpa only [Nat.zero_add] using Nat.mod_eq_of_lt hm)))

end YMGap.Continuum.SU2QuaternionCyclicWeightedAngular

#print axioms YMGap.Continuum.SU2QuaternionCyclicWeightedAngular.cycleRotation_mul
#print axioms YMGap.Continuum.SU2QuaternionCyclicWeightedAngular.rotateIterate_mul
#print axioms YMGap.Continuum.SU2QuaternionCyclicWeightedAngular.rotateIterate_pairing_invariant
#print axioms YMGap.Continuum.SU2QuaternionCyclicWeightedAngular.rotateIterate_succ_right
#print axioms YMGap.Continuum.SU2QuaternionCyclicWeightedAngular.rotateIterate_head_weightedAngularSquare_haar_of_lt
