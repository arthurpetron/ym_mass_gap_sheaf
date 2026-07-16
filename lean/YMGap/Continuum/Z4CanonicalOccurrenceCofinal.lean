/-
# Cofinal thermodynamic-volume modulus for canonical local occurrences

The two-volume boundary estimate becomes a genuine cofinal Cauchy modulus
once canonical transport is shown to compose literally.  This module proves
that coherence, records that a transported polymer remains inside its source
geometry, and packages the resulting estimate for every pair of sufficiently
large finite boxes.

Everything remains at the exact cutoff-one SU(2) anchor.  In particular this
is a thermodynamic-volume statement, not a cutoff-removal or continuum-limit
claim.
-/

import YMGap.Constructive.CRealAbs
import YMGap.Continuum.Z4CanonicalOccurrenceStability

namespace YMGap.Continuum.Z4CanonicalOccurrenceCofinal

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalOccurrenceStability
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.TsumDeriv (abs_add_le)
open YMGap.Continuum.TsumDeriv.Q' (abs_eqv_congr abs_mul_le abs_of_nonneg)

/-! ## 1. Coherence of canonical transport -/

/-- Re-encoding a canonical polymer through an intermediate box agrees
literally with direct re-encoding in the outer box. -/
theorem transportPolymer_trans
    {base middle outer : Nat}
    (hbaseMiddle : base ≤ middle)
    (hmiddleOuter : middle ≤ outer)
    {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers base) :
    transportPolymer middle outer
        (transportPolymer base middle polymer) =
      transportPolymer base outer polymer := by
  have hmiddlePolymer :=
    transportPolymer_mem_canonicalSurfacePolymers hbaseMiddle hpolymer
  have hnested :=
    transportPolymer_mem_canonicalSurfacePolymers hmiddleOuter hmiddlePolymer
  have hdirect :=
    transportPolymer_mem_canonicalSurfacePolymers
      (Nat.le_trans hbaseMiddle hmiddleOuter) hpolymer
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport hnested hdirect
  have hbaseMiddleSupport :=
    transportPolymer_sameSupport hbaseMiddle
      (canonicalSurfacePolymer_mem_faceSupports hpolymer)
  have hmiddleOuterSupport :=
    transportPolymer_sameSupport hmiddleOuter
      (canonicalSurfacePolymer_mem_faceSupports hmiddlePolymer)
  have hbaseOuterSupport :=
    transportPolymer_sameSupport
      (Nat.le_trans hbaseMiddle hmiddleOuter)
      (canonicalSurfacePolymer_mem_faceSupports hpolymer)
  exact sameSupport_trans
    (sameSupport_symm
      (sameSupport_trans hbaseMiddleSupport hmiddleOuterSupport))
    hbaseOuterSupport

/-- A canonical polymer transported out of box `base` remains geometrically
inside box `base`, independently of the larger numerical encoding. -/
theorem transportPolymer_inside_source_box
    {base outer : Nat} (hbaseOuter : base ≤ outer)
    {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers base) :
    PolymerInsideBox base outer
      (transportPolymer base outer polymer) := by
  intro plaquette hplaquette
  have hsource :=
    (transportPolymer_sameSupport hbaseOuter
      (canonicalSurfacePolymer_mem_faceSupports hpolymer)).2
      plaquette hplaquette
  exact geometricPolymer_subset_box
    (canonicalSurfacePolymer_mem_faceSupports hpolymer)
    plaquette hsource

/-! ## 2. Pairwise cofinal modulus -/

/-- For a fixed canonical local polymer, the occurrence probabilities in
any two boxes beyond `n` differ by the explicit boundary tail measured from
the original box to `n`. -/
theorem anchorPolymerOccurrenceProbability_cofinal_abs_sub_le
    {base n m : Nat}
    (hbaseN : base ≤ n)
    (hnm : n ≤ m)
    {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers base) :
    Q'.abs
        (anchorPolymerOccurrenceProbability m
            (transportPolymer base m polymer) -
          anchorPolymerOccurrenceProbability n
            (transportPolymer base n polymer)) ≤
      occurrenceBoundaryEpsilon (n - base) := by
  have hnPolymer :=
    transportPolymer_mem_canonicalSurfacePolymers hbaseN hpolymer
  have hnInside :=
    transportPolymer_inside_source_box hbaseN hpolymer
  have hbox : base + (n - base) = n := Nat.add_sub_of_le hbaseN
  have hbound :=
    anchorPolymerOccurrenceProbability_abs_sub_le_boundaryEpsilon_of_inside
      hnm hnPolymer hnInside hbox
  rw [transportPolymer_trans hbaseN hnm hpolymer] at hbound
  exact hbound

private theorem pow_le_pow_base_local
    (a b : Q') (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    ∀ exponent : Nat, a ^ exponent ≤ b ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ ha hab
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right a b (a ^ exponent) hab
          (Q'.pow_nonneg a ha exponent))
        (Q'.mul_le_mul_of_nonneg_left (a ^ exponent) (b ^ exponent) b
          (pow_le_pow_base_local a b ha hab exponent) hb)

/-- The model-specific boundary tail is bounded by a standard dyadic tail.
The two spare carrier faces exactly pay for the leading factor `2`. -/
theorem occurrenceBoundaryEpsilon_le_half_pow_succ (distance : Nat) :
    occurrenceBoundaryEpsilon distance ≤
      HalfPow.half ^ (distance + 1) := by
  have hpow :
      anchorEffectiveRatio ^ (distance + 2) ≤
        HalfPow.half ^ (distance + 2) :=
    pow_le_pow_base_local anchorEffectiveRatio HalfPow.half
      anchorEffectiveRatio_nonnegative anchorEffectiveRatio_le_half
      (distance + 2)
  have hmul := Q'.mul_le_mul_of_nonneg_right
    (anchorEffectiveRatio ^ (distance + 2))
    (HalfPow.half ^ (distance + 2)) (Q'.ofNat 2) hpow (by decide)
  have hcollapse :
      (HalfPow.half ^ (distance + 2) * Q'.ofNat 2).eqv
        (HalfPow.half ^ (distance + 1)) := by
    have hexponent : distance + 2 = (distance + 1) + 1 := by omega
    rw [hexponent]
    have hpone : (HalfPow.half ^ 1).eqv HalfPow.half := by
      change (HalfPow.half * 1).eqv HalfPow.half
      exact Q'.mul_one_eqv HalfPow.half
    have hhalfTwo :
        (HalfPow.half * Q'.ofNat 2).eqv (1 : Q') := by decide
    have hinner :
        (HalfPow.half ^ 1 * Q'.ofNat 2).eqv (1 : Q') :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (HalfPow.half ^ 1) HalfPow.half
          (Q'.ofNat 2) hpone)
        hhalfTwo
    refine Q'.eqv_trans _
      ((HalfPow.half ^ (distance + 1) * HalfPow.half ^ 1) *
        Q'.ofNat 2) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ (Q'.ofNat 2)
        (Q'.pow_add_eqv HalfPow.half (distance + 1) 1)
    · refine Q'.eqv_trans _
        (HalfPow.half ^ (distance + 1) *
          (HalfPow.half ^ 1 * Q'.ofNat 2)) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _
        (HalfPow.half ^ (distance + 1) * 1) _
        (Q'.mul_eqv_congr_left _ _ _ hinner) ?_
      exact Q'.mul_one_eqv _
  unfold occurrenceBoundaryEpsilon
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hcollapse)

theorem occurrenceBoundaryEpsilon_le_half_pow (distance : Nat) :
    occurrenceBoundaryEpsilon distance ≤ HalfPow.half ^ distance := by
  exact Q'.le_trans' _ _ _
    (occurrenceBoundaryEpsilon_le_half_pow_succ distance)
    (ExpNeg.pow_half_antitone distance 1)

/-- Standard dyadic Cauchy form: once the inner volume is at least
`precision` layers beyond the base support, the discrepancy is at most
`2⁻ᵖʳᵉᶜᶦˢᶦᵒⁿ`. -/
theorem anchorPolymerOccurrenceProbability_cofinal_abs_sub_le_half_pow
    {base precision n m : Nat}
    (hprecision : base + precision ≤ n)
    (hnm : n ≤ m)
    {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers base) :
    Q'.abs
        (anchorPolymerOccurrenceProbability m
            (transportPolymer base m polymer) -
          anchorPolymerOccurrenceProbability n
            (transportPolymer base n polymer)) ≤
      HalfPow.half ^ precision := by
  have hbaseN : base ≤ n :=
    Nat.le_trans (Nat.le_add_right base precision) hprecision
  have hraw :=
    anchorPolymerOccurrenceProbability_cofinal_abs_sub_le
      hbaseN hnm hpolymer
  have htail := occurrenceBoundaryEpsilon_le_half_pow (n - base)
  have hprecisionSub : precision ≤ n - base :=
    Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hprecision)
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hprecisionSub
  have hhalf : HalfPow.half ^ (n - base) ≤
      HalfPow.half ^ precision := by
    rw [hoffset]
    exact ExpNeg.pow_half_antitone precision offset
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ htail hhalf)

/-! ## 3. Finite signed local occurrence observables -/

/-- One finitely supported local occurrence observable term.  Its canonical
polymer is fixed in the base box; the rational coefficient may have either
sign. -/
structure LocalOccurrenceTerm (base : Nat) where
  coefficient : Q'
  polymer : List Nat
  canonical : polymer ∈ canonicalSurfacePolymers base

/-- Evaluation of one local term after canonical transport to `volume`. -/
def localOccurrenceTermValue {base : Nat} (volume : Nat)
    (term : LocalOccurrenceTerm base) : Q' :=
  term.coefficient *
    anchorPolymerOccurrenceProbability volume
      (transportPolymer base volume term.polymer)

/-- Exact finite signed sum of transported occurrence probabilities. -/
def localOccurrenceObservable {base : Nat} (volume : Nat) :
    List (LocalOccurrenceTerm base) → Q'
  | [] => 0
  | term :: rest =>
      localOccurrenceTermValue volume term +
        localOccurrenceObservable volume rest

/-- Constructive `ℓ1` norm of the rational coefficients. -/
def localOccurrenceCoefficientL1 {base : Nat} :
    List (LocalOccurrenceTerm base) → Q'
  | [] => 0
  | term :: rest =>
      Q'.abs term.coefficient + localOccurrenceCoefficientL1 rest

private theorem add_sub_add_eqv (a b c d : Q') :
    ((a + b) + (-(c + d))).eqv
      ((a + (-c)) + (b + (-d))) := by
  refine Q'.eqv_trans _ ((a + b) + ((-c) + (-d))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (a + b) _ _ (Q'.neg_add_eqv c d)
  · exact Q'.add_swap_inner a b (-c) (-d)

private theorem mul_sub_eqv_local (a b c : Q') :
    (a * (b + (-c))).eqv (a * b + (-(a * c))) := by
  refine Q'.eqv_trans _ (a * b + a * (-c)) _
    (Q'.mul_add_eqv a b (-c)) ?_
  exact Q'.add_eqv_congr_left (a * b) _ _ (Q'.mul_neg_eqv a c)

/-- The singleton cofinal modulus is stable under an arbitrary exact rational
coefficient, with the coefficient entering through its absolute value. -/
theorem localOccurrenceTermValue_cofinal_abs_sub_le
    {base n m : Nat}
    (hbaseN : base ≤ n)
    (hnm : n ≤ m)
    (term : LocalOccurrenceTerm base) :
    Q'.abs
        (localOccurrenceTermValue m term -
          localOccurrenceTermValue n term) ≤
      Q'.abs term.coefficient * occurrenceBoundaryEpsilon (n - base) := by
  have hsingle :=
    anchorPolymerOccurrenceProbability_cofinal_abs_sub_le
      hbaseN hnm term.canonical
  let pm := anchorPolymerOccurrenceProbability m
    (transportPolymer base m term.polymer)
  let pn := anchorPolymerOccurrenceProbability n
    (transportPolymer base n term.polymer)
  have hfactor :
      (term.coefficient * pm + (-(term.coefficient * pn))).eqv
        (term.coefficient * (pm + (-pn))) :=
    Q'.eqv_symm (mul_sub_eqv_local term.coefficient pm pn)
  change Q'.abs
      (term.coefficient * pm + (-(term.coefficient * pn))) ≤
        Q'.abs term.coefficient * occurrenceBoundaryEpsilon (n - base)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_eqv_congr hfactor)) ?_
  refine Q'.le_trans' _ _ _ (abs_mul_le term.coefficient (pm + (-pn))) ?_
  exact Q'.mul_le_mul_of_nonneg_left
    (Q'.abs (pm + (-pn))) (occurrenceBoundaryEpsilon (n - base))
    (Q'.abs term.coefficient) hsingle (Q'.abs_nonneg term.coefficient)

/-- Finite signed local occurrence observables inherit the same cofinal
boundary modulus, multiplied by the exact `ℓ1` norm of their coefficients. -/
theorem localOccurrenceObservable_cofinal_abs_sub_le
    {base n m : Nat}
    (hbaseN : base ≤ n)
    (hnm : n ≤ m) :
    ∀ terms : List (LocalOccurrenceTerm base),
      Q'.abs
          (localOccurrenceObservable m terms -
            localOccurrenceObservable n terms) ≤
        localOccurrenceCoefficientL1 terms *
          occurrenceBoundaryEpsilon (n - base)
  | [] => by
      change Q'.abs ((0 : Q') + (-0)) ≤
        (0 : Q') * occurrenceBoundaryEpsilon (n - base)
      have hleft : Q'.abs ((0 : Q') + (-0)) ≤ (0 : Q') := by
        refine Q'.le_of_eqv (Q'.eqv_trans _ (Q'.abs (0 : Q')) _ ?_ ?_)
        · exact abs_eqv_congr (Q'.add_neg_self_eqv 0)
        · exact abs_of_nonneg (Q'.le_refl' 0)
      exact Q'.le_trans' _ _ _ hleft
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.zero_mul_eqv (occurrenceBoundaryEpsilon (n - base)))))
  | term :: rest => by
      change Q'.abs
          ((localOccurrenceTermValue m term +
              localOccurrenceObservable m rest) +
            (-(localOccurrenceTermValue n term +
              localOccurrenceObservable n rest))) ≤
        (Q'.abs term.coefficient +
            localOccurrenceCoefficientL1 rest) *
          occurrenceBoundaryEpsilon (n - base)
      have hsplit := add_sub_add_eqv
        (localOccurrenceTermValue m term)
        (localOccurrenceObservable m rest)
        (localOccurrenceTermValue n term)
        (localOccurrenceObservable n rest)
      have hterm :=
        localOccurrenceTermValue_cofinal_abs_sub_le hbaseN hnm term
      have hrest :=
        localOccurrenceObservable_cofinal_abs_sub_le hbaseN hnm rest
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_eqv_congr hsplit)) ?_
      refine Q'.le_trans' _ _ _
        (abs_add_le
          (localOccurrenceTermValue m term +
            (-localOccurrenceTermValue n term))
          (localOccurrenceObservable m rest +
            (-localOccurrenceObservable n rest))) ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add hterm hrest) ?_
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (YMGap.Constructive.ExpNeg.add_mul_eqv
            (Q'.abs term.coefficient)
            (localOccurrenceCoefficientL1 rest)
            (occurrenceBoundaryEpsilon (n - base))))

theorem localOccurrenceCoefficientL1_nonnegative {base : Nat} :
    ∀ terms : List (LocalOccurrenceTerm base),
      (0 : Q') ≤ localOccurrenceCoefficientL1 terms
  | [] => Q'.le_refl' 0
  | term :: rest =>
      Q'.zero_le_add _ _ (Q'.abs_nonneg term.coefficient)
        (localOccurrenceCoefficientL1_nonnegative rest)

/-- Dyadic form of the finite-observable modulus. -/
theorem localOccurrenceObservable_cofinal_abs_sub_le_half_pow
    {base precision n m : Nat}
    (hprecision : base + precision ≤ n)
    (hnm : n ≤ m)
    (terms : List (LocalOccurrenceTerm base)) :
    Q'.abs
        (localOccurrenceObservable m terms -
          localOccurrenceObservable n terms) ≤
      localOccurrenceCoefficientL1 terms * HalfPow.half ^ precision := by
  have hbaseN : base ≤ n :=
    Nat.le_trans (Nat.le_add_right base precision) hprecision
  have hraw := localOccurrenceObservable_cofinal_abs_sub_le
    hbaseN hnm terms
  have hcoefficient := localOccurrenceCoefficientL1_nonnegative terms
  have htail := occurrenceBoundaryEpsilon_le_half_pow (n - base)
  have hscaledTail := Q'.mul_le_mul_of_nonneg_left
    (occurrenceBoundaryEpsilon (n - base)) (HalfPow.half ^ (n - base))
    (localOccurrenceCoefficientL1 terms) htail hcoefficient
  have hprecisionSub : precision ≤ n - base :=
    Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hprecision)
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hprecisionSub
  have hhalf : HalfPow.half ^ (n - base) ≤
      HalfPow.half ^ precision := by
    rw [hoffset]
    exact ExpNeg.pow_half_antitone precision offset
  have hscaledHalf := Q'.mul_le_mul_of_nonneg_left
    (HalfPow.half ^ (n - base)) (HalfPow.half ^ precision)
    (localOccurrenceCoefficientL1 terms) hhalf hcoefficient
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ hscaledTail hscaledHalf)

/-! ## 4. Constructive thermodynamic limits -/

private theorem two_sided_add_of_abs_sub_le {a b epsilon : Q'}
    (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (TsumDeriv.Q'.abs_sub_comm b a)) h

/-- Cofinal finite-volume sequence for a fixed base-box polymer. -/
def anchorPolymerOccurrenceCofinalSequence
    (base : Nat) (polymer : List Nat) (stage : Nat) : Q' :=
  anchorPolymerOccurrenceProbability (base + stage)
    (transportPolymer base (base + stage) polymer)

/-- The constructive-real thermodynamic-volume limit of one canonical
cutoff-one local occurrence.  Its approximation at stage `k` is literally
the probability in box `base + k`. -/
def anchorPolymerOccurrenceCofinalLimit
    {base : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers base) : CReal where
  approx := anchorPolymerOccurrenceCofinalSequence base polymer
  cauchy := by
    intro epsilon hepsilon
    refine ⟨epsilon.den, fun m n hm hn => ?_⟩
    rcases Nat.le_total m n with hmn | hnm
    · have hdyadic :=
        anchorPolymerOccurrenceProbability_cofinal_abs_sub_le_half_pow
          (base := base) (precision := epsilon.den)
          (n := base + m) (m := base + n)
          (by omega) (by omega) hpolymer
      have habs : Q'.abs
          (anchorPolymerOccurrenceCofinalSequence base polymer n -
            anchorPolymerOccurrenceCofinalSequence base polymer m) ≤
          epsilon :=
        Q'.le_trans' _ _ _ hdyadic
          (HalfPow.pow_half_le epsilon hepsilon)
      have hpair := two_sided_add_of_abs_sub_le habs
      exact ⟨hpair.2, hpair.1⟩
    · have hdyadic :=
        anchorPolymerOccurrenceProbability_cofinal_abs_sub_le_half_pow
          (base := base) (precision := epsilon.den)
          (n := base + n) (m := base + m)
          (by omega) (by omega) hpolymer
      have habs : Q'.abs
          (anchorPolymerOccurrenceCofinalSequence base polymer m -
            anchorPolymerOccurrenceCofinalSequence base polymer n) ≤
          epsilon :=
        Q'.le_trans' _ _ _ hdyadic
          (HalfPow.pow_half_le epsilon hepsilon)
      exact two_sided_add_of_abs_sub_le habs

@[simp] theorem anchorPolymerOccurrenceCofinalLimit_approx
    {base stage : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers base) :
    (anchorPolymerOccurrenceCofinalLimit hpolymer).approx stage =
      anchorPolymerOccurrenceCofinalSequence base polymer stage := rfl

theorem anchorPolymerOccurrenceCofinalSequence_converges
    {base : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers base) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        (anchorPolymerOccurrenceCofinalSequence base polymer stage))
      (anchorPolymerOccurrenceCofinalLimit hpolymer) :=
  CReal.convergesTo_self (anchorPolymerOccurrenceCofinalLimit hpolymer)

/-- Cofinal finite-volume sequence for a finite signed local occurrence
observable. -/
def localOccurrenceObservableCofinalSequence {base : Nat}
    (terms : List (LocalOccurrenceTerm base)) (stage : Nat) : Q' :=
  localOccurrenceObservable (base + stage) terms

/-- Every finite signed rational combination of local cutoff-one occurrences
has a constructive-real thermodynamic-volume limit with an explicit modulus.
The modulus rescales the requested tolerance by the exact coefficient
`ℓ1` norm; no boundedness constant is postulated. -/
def localOccurrenceObservableCofinalLimit {base : Nat}
    (terms : List (LocalOccurrenceTerm base)) : CReal where
  approx := localOccurrenceObservableCofinalSequence terms
  cauchy := by
    intro epsilon hepsilon
    let coefficientNorm := localOccurrenceCoefficientL1 terms
    let scaledTolerance :=
      epsilon * Q'.invSucc coefficientNorm.num.toNat
    have hcoefficient : (0 : Q') ≤ coefficientNorm :=
      localOccurrenceCoefficientL1_nonnegative terms
    have hscaledPositive : (0 : Q') < scaledTolerance :=
      Q'.mul_pos hepsilon (Q'.invSucc_pos coefficientNorm.num.toNat)
    refine ⟨scaledTolerance.den, fun m n hm hn => ?_⟩
    have hscaledFinal : coefficientNorm * scaledTolerance ≤ epsilon :=
      ExpNeg.mul_le_of_mul_invSucc_toNat coefficientNorm epsilon
        hcoefficient (Q'.le_of_lt hepsilon)
    rcases Nat.le_total m n with hmn | hnm
    · have hdyadic :=
        localOccurrenceObservable_cofinal_abs_sub_le_half_pow
          (base := base) (precision := scaledTolerance.den)
          (n := base + m) (m := base + n)
          (by omega) (by omega) terms
      have hhalf := HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaledHalf := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ scaledTolerance.den) scaledTolerance
        coefficientNorm hhalf hcoefficient
      have habs : Q'.abs
          (localOccurrenceObservableCofinalSequence terms n -
            localOccurrenceObservableCofinalSequence terms m) ≤ epsilon :=
        Q'.le_trans' _ _ _ hdyadic
          (Q'.le_trans' _ _ _ hscaledHalf hscaledFinal)
      have hpair := two_sided_add_of_abs_sub_le habs
      exact ⟨hpair.2, hpair.1⟩
    · have hdyadic :=
        localOccurrenceObservable_cofinal_abs_sub_le_half_pow
          (base := base) (precision := scaledTolerance.den)
          (n := base + n) (m := base + m)
          (by omega) (by omega) terms
      have hhalf := HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaledHalf := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ scaledTolerance.den) scaledTolerance
        coefficientNorm hhalf hcoefficient
      have habs : Q'.abs
          (localOccurrenceObservableCofinalSequence terms m -
            localOccurrenceObservableCofinalSequence terms n) ≤ epsilon :=
        Q'.le_trans' _ _ _ hdyadic
          (Q'.le_trans' _ _ _ hscaledHalf hscaledFinal)
      exact two_sided_add_of_abs_sub_le habs

@[simp] theorem localOccurrenceObservableCofinalLimit_approx
    {base stage : Nat} (terms : List (LocalOccurrenceTerm base)) :
    (localOccurrenceObservableCofinalLimit terms).approx stage =
      localOccurrenceObservableCofinalSequence terms stage := rfl

theorem localOccurrenceObservableCofinalSequence_converges
    {base : Nat} (terms : List (LocalOccurrenceTerm base)) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        (localOccurrenceObservableCofinalSequence terms stage))
      (localOccurrenceObservableCofinalLimit terms) :=
  CReal.convergesTo_self (localOccurrenceObservableCofinalLimit terms)

end YMGap.Continuum.Z4CanonicalOccurrenceCofinal

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalOccurrenceCofinal.transportPolymer_trans
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceCofinal.transportPolymer_inside_source_box
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceCofinal.anchorPolymerOccurrenceProbability_cofinal_abs_sub_le
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceCofinal.occurrenceBoundaryEpsilon_le_half_pow
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceCofinal.anchorPolymerOccurrenceProbability_cofinal_abs_sub_le_half_pow
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceCofinal.localOccurrenceTermValue_cofinal_abs_sub_le
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceCofinal.localOccurrenceObservable_cofinal_abs_sub_le
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceCofinal.localOccurrenceObservable_cofinal_abs_sub_le_half_pow
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceCofinal.anchorPolymerOccurrenceCofinalLimit
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceCofinal.anchorPolymerOccurrenceCofinalSequence_converges
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceCofinal.localOccurrenceObservableCofinalLimit
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceCofinal.localOccurrenceObservableCofinalSequence_converges
