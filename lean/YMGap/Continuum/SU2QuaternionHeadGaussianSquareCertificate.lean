/-
# Polynomial-valued Gaussian square certificates

Integrating the four head coordinates of a supported polynomial square gives
an explicit finite nonnegatively weighted sum of supported TAIL polynomial
squares. The channels retain every tail monomial, rather than evaluating the
tail or replacing its Haar functional by a finite-state model.

The weights and vectors are the existing four-coordinate Hermite/Schur Gram
data. The identity is coefficientwise, under every tail coefficient probe.
This is the Gaussian algebraic step only: no sphere homogenization, Haar
certificate preservation, transfer contraction or continuum claim is made.
-/

import YMGap.Continuum.SU2QuaternionArbitraryGaussianPositivity
import YMGap.Continuum.SU2QuaternionHeadGaussianIBP
import YMGap.Continuum.QuaternionHaarSquareCertificate

namespace YMGap.Continuum.SU2QuaternionHeadGaussianSquareCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP
open YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP
open YMGap.Continuum.SU2QuaternionProductGaussianHermiteGram
open YMGap.Continuum.SU2QuaternionArbitraryGaussianPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- A finite polynomial sum in the same order as the rational `finSum`. -/
def polyFinSum (f : Nat → RatPoly) : Nat → RatPoly
  | 0 => polyZero
  | n + 1 => polyAdd (polyFinSum f n) (f n)

private theorem weighted_polyFinSum (weight : List Nat → Q') (f : Nat → RatPoly) :
    ∀ n, ratWeightedSum weight (polyFinSum f n) ≈
      finSum (fun i => ratWeightedSum weight (f i)) n
  | 0 => Q'.eqv_refl _
  | n + 1 =>
      Q'.eqv_trans _ _ _ (ratWeightedSum_add weight _ _)
        (Q'.add_eqv_congr' (weighted_polyFinSum weight f n) (Q'.eqv_refl _))

private theorem weighted_mul_polyFinSum (weight : List Nat → Q')
    (p : RatPoly) (f : Nat → RatPoly) : ∀ n,
    ratWeightedSum weight (polyMul p (polyFinSum f n)) ≈
      finSum (fun i => ratWeightedSum weight (polyMul p (f i))) n
  | 0 => RatPolyCoeffEqv.mul_zero_right p weight
  | n + 1 =>
      Q'.eqv_trans _ _ _ (RatPolyCoeffEqv.mul_add_right p _ _ weight)
        (Q'.eqv_trans _ _ _ (ratWeightedSum_add weight _ _)
          (Q'.add_eqv_congr' (weighted_mul_polyFinSum weight p f n) (Q'.eqv_refl _)))

private theorem weighted_polyFinSum_mul (weight : List Nat → Q')
    (f g : Nat → RatPoly) (n : Nat) : ∀ m,
    ratWeightedSum weight (polyMul (polyFinSum f m) (polyFinSum g n)) ≈
      finSum (fun i => finSum (fun j =>
        ratWeightedSum weight (polyMul (f i) (g j))) n) m
  | 0 => Q'.eqv_refl _
  | m + 1 => by
      change ratWeightedSum weight
        (polyMul (polyAdd (polyFinSum f m) (f m)) (polyFinSum g n)) ≈ _
      rw [polyMul_add_left_exact]
      exact Q'.eqv_trans _ _ _ (ratWeightedSum_add weight _ _)
        (Q'.add_eqv_congr' (weighted_polyFinSum_mul weight f g n m)
          (weighted_mul_polyFinSum weight (f m) g n))

private theorem weighted_singleton (weight : List Nat → Q') (t : RatTerm) :
    ratWeightedSum weight [t] ≈ t.2 * weight t.1 := by
  change t.2 * weight t.1 + 0 ≈ t.2 * weight t.1
  rw [Q'.add_zero']
  exact Q'.eqv_refl _

private theorem weighted_singleton_mul (weight : List Nat → Q') (s t : RatTerm) :
    ratWeightedSum weight (polyMul [s] [t]) ≈
      (s.2 * t.2) * weight (monoMul s.1 t.1) :=
  weighted_singleton weight (monoMul s.1 t.1, s.2 * t.2)

private theorem weighted_indexed (weight : List Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum weight p ≈
      finSum (fun i => (termAt p i).2 * weight (termAt p i).1) p.length
  | [] => Q'.eqv_refl _
  | t :: rest => by
      let f := fun i => (termAt (t :: rest) i).2 * weight (termAt (t :: rest) i).1
      refine Q'.eqv_trans _ (f 0 + finSum (fun i => f (i + 1)) rest.length) _ ?_
        (Q'.eqv_symm (finSum_head f rest.length))
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (by simpa [f, termAt] using weighted_indexed weight rest)

private theorem indexed_coeff (p : RatPoly) :
    RatPolyCoeffEqv p (polyFinSum (fun i => [termAt p i]) p.length) := by
  intro weight
  refine Q'.eqv_trans _ _ _ (weighted_indexed weight p) ?_
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (weighted_polyFinSum weight _ _)
    (finSum_eqv_congr _ _ (fun i => weighted_singleton weight (termAt p i)) _))

private theorem monoMul_right_nil : ∀ m : List Nat, monoMul m [] = m
  | [] => rfl
  | _ :: _ => rfl

private theorem drop_monoMul : ∀ (n : Nat) (m l : List Nat),
    (monoMul m l).drop n = monoMul (m.drop n) (l.drop n)
  | 0, _, _ => by simp
  | n + 1, [], l => by simp [monoMul]
  | n + 1, m, [] => by rw [monoMul_right_nil, List.drop_nil, monoMul_right_nil]
  | n + 1, _ :: m, _ :: l => by
      simp only [monoMul, List.drop_succ_cons]
      exact drop_monoMul n m l

private theorem headGaussianMoment_eq_arbitrary (m : List Nat) :
    headGaussianMoment m ≈ arbitraryGaussianMono 4 m := by
  refine Q'.eqv_trans _ _ _
    (gaussianMoment4_eq_tensor (exponentAt m 0) (exponentAt m 1)
      (exponentAt m 2) (exponentAt m 3)) ?_
  change _ ≈ gaussianMoment1 (exponentAt m 0) *
    (gaussianMoment1 (exponentAt m 1) *
      (gaussianMoment1 (exponentAt m 2) * (gaussianMoment1 (exponentAt m 3) * 1)))
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv _))))

/-- The actual four-coordinate Gram data, with no tail-support zeroing. -/
def headGram (p : RatPoly) : GramRep (fun i j =>
    headGaussianMoment (monoMul (termAt p i).1 (termAt p j).1)) where
  r := (arbitraryGaussianGramRep p 4).r
  d := (arbitraryGaussianGramRep p 4).d
  hd := (arbitraryGaussianGramRep p 4).hd
  v := (arbitraryGaussianGramRep p 4).v
  hM := fun i j => Q'.eqv_trans _ _ _ (headGaussianMoment_eq_arbitrary _)
    ((arbitraryGaussianGramRep p 4).hM i j)

/-- A Hermite/Schur channel, retaining the complete tail of every source term. -/
def channel (p : RatPoly) (k : Nat) : RatPoly :=
  polyFinSum (fun i => [((termAt p i).1.drop 4,
    (termAt p i).2 * (headGram p).v k i)]) p.length

/-- Explicit rationally weighted polynomial squares, with computable rank. -/
def squareSum (p : RatPoly) : RatPoly :=
  polyFinSum (fun k => polySmul ((headGram p).d k)
    (polyMul (channel p k) (channel p k))) (headGram p).r

private theorem partial_square_probe (p : RatPoly) (weight : List Nat → Q') :
    ratWeightedSum weight (partialGaussianHead (polyMul p p)) ≈
      finSum (fun i => finSum (fun j =>
        ((termAt p i).2 * (termAt p j).2) *
          headGaussianMoment (monoMul (termAt p i).1 (termAt p j).1) *
          weight (monoMul ((termAt p i).1.drop 4) ((termAt p j).1.drop 4)))
        p.length) p.length := by
  refine Q'.eqv_trans _ _ _ (partialGaussianHead_probe weight _) ?_
  refine Q'.eqv_trans _ _ _ ((indexed_coeff p).mul (indexed_coeff p) (gaussianHeadProbe weight)) ?_
  refine Q'.eqv_trans _ _ _ (weighted_polyFinSum_mul (gaussianHeadProbe weight) _ _ _ _) ?_
  refine finSum_eqv_congr _ _ (fun i => ?_) _
  refine finSum_eqv_congr _ _ (fun j => ?_) _
  refine Q'.eqv_trans _ _ _ (weighted_singleton_mul (gaussianHeadProbe weight) _ _) ?_
  unfold gaussianHeadProbe
  rw [drop_monoMul]
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

private theorem channel_square_probe (p : RatPoly) (weight : List Nat → Q') (k : Nat) :
    ratWeightedSum weight (polyMul (channel p k) (channel p k)) ≈
      finSum (fun i => finSum (fun j =>
        (((termAt p i).2 * (headGram p).v k i) *
          ((termAt p j).2 * (headGram p).v k j)) *
          weight (monoMul ((termAt p i).1.drop 4) ((termAt p j).1.drop 4)))
        p.length) p.length := by
  refine Q'.eqv_trans _ _ _ (weighted_polyFinSum_mul weight _ _ _ _) ?_
  exact finSum_eqv_congr _ _ (fun i =>
    finSum_eqv_congr _ _ (fun j => weighted_singleton_mul weight _ _) _) _

/-- Exact polynomial-valued SOS identity. No support restriction is needed
for the algebraic identity; support enters only its certificate below. -/
theorem partialGaussianHead_square_coeff (p : RatPoly) :
    RatPolyCoeffEqv (partialGaussianHead (polyMul p p)) (squareSum p) := by
  intro weight
  let g := headGram p
  let c := fun i => (termAt p i).2
  let w := fun i j => weight (monoMul ((termAt p i).1.drop 4) ((termAt p j).1.drop 4))
  let u := fun i j k => (g.d k * ((c i * g.v k i) * (c j * g.v k j))) * w i j
  have hentry (i j : Nat) :
      (c i * c j) * headGaussianMoment (monoMul (termAt p i).1 (termAt p j).1) * w i j ≈
        finSum (fun k => u i j k) g.r := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left _ _ _ (g.hM i j))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (const_mul_finSum _ (c i * c j) g.r)) ?_
    refine Q'.eqv_trans _ _ _ (finSum_mul_const _ (w i j) g.r) ?_
    exact finSum_eqv_congr _ _ (fun k => Q'.mul_eqv_congr_right _ _ _
      (mul6_rearrange (c i) (c j) (g.d k) (g.v k i) (g.v k j))) _
  have hleft : ratWeightedSum weight (partialGaussianHead (polyMul p p)) ≈
      finSum (fun k => finSum (fun i => finSum (fun j => u i j k) p.length) p.length) g.r := by
    refine Q'.eqv_trans _ _ _ (partial_square_probe p weight) ?_
    refine Q'.eqv_trans _ _ _ (finSum_eqv_congr _ _ (fun i =>
      finSum_eqv_congr _ _ (hentry i) p.length) p.length) ?_
    refine Q'.eqv_trans _ _ _ (finSum_eqv_congr _ _ (fun i =>
      finSum_swap (fun j k => u i j k) p.length g.r) p.length) ?_
    exact finSum_swap (fun i k => finSum (fun j => u i j k) p.length) p.length g.r
  have hright : ratWeightedSum weight (squareSum p) ≈
      finSum (fun k => finSum (fun i => finSum (fun j => u i j k) p.length) p.length) g.r := by
    refine Q'.eqv_trans _ _ _ (weighted_polyFinSum weight _ _) ?_
    refine finSum_eqv_congr _ _ (fun k => ?_) _
    refine Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight (g.d k) _) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (channel_square_probe p weight k)) ?_
    refine Q'.eqv_trans _ _ _ (const_mul_finSum _ (g.d k) p.length) ?_
    refine finSum_eqv_congr _ _ (fun i => ?_) _
    refine Q'.eqv_trans _ _ _ (const_mul_finSum _ (g.d k) p.length) ?_
    exact finSum_eqv_congr _ _ (fun j => Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) _
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)

private theorem termAt_supported (blocks : Nat) : ∀ p : RatPoly,
    SupportedQuaternionBlocks blocks p → ∀ i, (termAt p i).1.length ≤ 4 * blocks
  | [], _, i => by simp [termAt]
  | t :: rest, hp, 0 => by simpa [termAt] using hp t List.mem_cons_self
  | t :: rest, hp, i + 1 => by
      simpa [termAt] using termAt_supported blocks rest
        (fun t' ht' => hp t' (List.mem_cons_of_mem t ht')) i

private theorem supported_polyFinSum (blocks : Nat) (f : Nat → RatPoly) : ∀ n,
    (∀ i, i < n → SupportedQuaternionBlocks blocks (f i)) →
      SupportedQuaternionBlocks blocks (polyFinSum f n)
  | 0, _ => by intro t ht; cases ht
  | n + 1, hf => supported_add
      (supported_polyFinSum blocks f n (fun i hi => hf i (Nat.lt_trans hi (Nat.lt_succ_self n))))
      (hf n (Nat.lt_succ_self n))

/-- Every actual channel fits in the retained tail blocks. -/
theorem channel_supported (tailBlocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks + 1) p) (k : Nat) :
    SupportedQuaternionBlocks tailBlocks (channel p k) := by
  apply supported_polyFinSum
  intro i _ t ht
  have ht' := List.mem_singleton.mp ht
  subst t
  change ((termAt p i).1.drop 4).length ≤ 4 * tailBlocks
  rw [List.length_drop]
  have h := termAt_supported (tailBlocks + 1) p hp i
  omega

private def certificate_polyFinSum (blocks : Nat) (f : Nat → RatPoly) :
    ∀ n, (∀ i, i < n → Certificate blocks (f i)) → Certificate blocks (polyFinSum f n)
  | 0, _ => .square [] (by intro t ht; cases ht)
  | n + 1, hf => .add
      (certificate_polyFinSum blocks f n (fun i hi => hf i (Nat.lt_trans hi (Nat.lt_succ_self n))))
      (hf n (Nat.lt_succ_self n))

/-- The displayed SOS has a certificate built solely from its explicit
supported channels and the actual rational Hermite/Schur weights. -/
def squareSum_certificate (tailBlocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks + 1) p) :
    Certificate tailBlocks (squareSum p) :=
  certificate_polyFinSum tailBlocks _ _ (fun k _ =>
    .smul ((headGram p).d k) ((headGram p).hd k)
      (.square (channel p k) (channel_supported tailBlocks p hp k)))

/-- Partial Gaussian integration compiles any supported square to the
existing ORIGINAL-tail Haar square-certificate language. -/
def partialGaussianHead_square_certificate (tailBlocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks + 1) p) :
    Certificate tailBlocks (partialGaussianHead (polyMul p p)) :=
  Certificate.ofCoeff (partialGaussianHead_square_coeff p) (squareSum_certificate tailBlocks p hp)

end YMGap.Continuum.SU2QuaternionHeadGaussianSquareCertificate

#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianSquareCertificate.polyFinSum
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianSquareCertificate.headGram
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianSquareCertificate.channel
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianSquareCertificate.squareSum
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianSquareCertificate.partialGaussianHead_square_coeff
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianSquareCertificate.channel_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianSquareCertificate.squareSum_certificate
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianSquareCertificate.partialGaussianHead_square_certificate
