/-
# Actual reconstructed-section endpoint transpose

The raw first-pair exchange acts on coefficient rows.  The concrete
`fixedRightSection` is a synthesis vector, so the operator acting on it is
the finite-box matrix transpose, including the boundary guards.  Applying
the raw pointwise operator itself is a normalization error: the asymmetric
`(2,2,1,1)` block gives `5/6`, while the finite transpose gives the physical
Jacobi coefficient `1/3`.

This file makes the section-side coefficient an explicit expression involving
the actual checked analysis and reconstruction maps.  The fundamental and
mixed endpoint blocks then satisfy the exact Gram-transpose equation and the
pinned `CandidateJacobiAt` equation with no abstract coefficient hypothesis.
-/

import YMGap.Continuum.SU2OrderedRacahEndpointGramTranspose

namespace YMGap.Continuum.SU2OrderedRacahEndpointReconstructedSection

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality
open YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
open YMGap.Continuum.SU2OrderedRacahEndpointCasimirAction
open YMGap.Continuum.SU2OrderedRacahEndpointCasimirAllOrder
open YMGap.Continuum.SU2OrderedRacahEndpointGramTranspose
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted

local infix:50 " ≈ " => Q'.eqv

/-! ## Finite-box transpose and the wrong-operator fence -/

/-- Literal application of the raw coefficient-row exchange to a source
tensor.  This is retained only to state the normalization fence below. -/
def firstPairRawExchangeTensor (a b : Nat) (x : TriForm) : TriForm :=
  fun i j l => pairExchange a b (fun u v => x u v l) i j

/-- Ordinary finite-box matrix transpose of `pairExchange`.  The two guarded
incoming terms are the transposes of the two raw shifts; the diagonal term is
unchanged. -/
def pairExchangeFiniteTranspose (a b : Nat)
    (x : Nat → Nat → Q') (i j : Nat) : Q' :=
  (if 0 < i ∧ j < b then
      (Q'.ofNat (a - (i - 1)) * Q'.ofNat (j + 1)) * x (i - 1) (j + 1)
    else 0) +
  (if i < a ∧ 0 < j then
      (Q'.ofNat (i + 1) * Q'.ofNat (b - (j - 1))) * x (i + 1) (j - 1)
    else 0) +
  (-((Q'.ofNat (a - i) * Q'.ofNat j) +
      (Q'.ofNat i * Q'.ofNat (b - j))) * x i j)

/-- Finite transpose acting on the first two coordinates of an actual
three-factor synthesis tensor. -/
def firstPairExchangeTransposeTensor (a b : Nat) (x : TriForm) : TriForm :=
  fun i j l => pairExchangeFiniteTranspose a b (fun u v => x u v l) i j

/-! ## Arbitrary-label endpoint sections -/

/-- Endpoint right channel with inner order zero and outer order `q`. -/
def endpointRightZero (a b c q : Nat)
    (hqa : q ≤ a) (hqf : q ≤ b + c) :
    FixedRightCGChannel a b c (endpointFinalLabel a b c q) where
  p := 0
  p_le := by omega
  r := q
  r_le := by omega
  degree_eq := by unfold endpointFinalLabel; omega

/-- Neighboring endpoint right channel with inner order one. -/
def endpointRightOne (a b c q : Nat)
    (hb : 0 < b) (hc : 0 < c) (hq0 : 0 < q)
    (hqa : q ≤ a) (hqf : q ≤ b + c - 1) :
    FixedRightCGChannel a b c (endpointFinalLabel a b c q) where
  p := 1
  p_le := by omega
  r := q - 1
  r_le := by omega
  degree_eq := by unfold endpointFinalLabel; omega

/-- The incorrect same-operator coefficient on the actual reconstructed
section.  It is useful only as a machine-checkable fence. -/
def endpointRawOperatorSectionForward (a b c q : Nat)
    (hb : 0 < b) (hc : 0 < c) (hq0 : 0 < q)
    (hqa : q ≤ a) (hqf : q ≤ b + c - 1) : Q' :=
  fixedRightAnalysis (endpointRightOne a b c q hb hc hq0 hqa hqf)
    (firstPairRawExchangeTensor a b
      (fixedRightSection
        (endpointRightZero a b c q hqa (by omega)) (mono 0))) 0

/-- **Actual reconstructed-section endpoint coefficient.**  Analyze the
finite-transpose image of the checked order-zero synthesis section in the
neighboring order-one channel. -/
def endpointReconstructedSectionForward (a b c q : Nat)
    (hb : 0 < b) (hc : 0 < c) (hq0 : 0 < q)
    (hqa : q ≤ a) (hqf : q ≤ b + c - 1) : Q' :=
  fixedRightAnalysis (endpointRightOne a b c q hb hc hq0 hqa hqf)
    (firstPairExchangeTransposeTensor a b
      (fixedRightSection
        (endpointRightZero a b c q hqa (by omega)) (mono 0))) 0

/-! ## Complete finite endpoint blocks -/

/-- In the asymmetric mixed block, applying the raw row operator to the
synthesis section gives `5/6`. -/
theorem mixed221_raw_operator_section_forward_eq_fiveSixths :
    endpointRawOperatorSectionForward 2 2 1 2
      (by omega) (by omega) (by omega) (by omega) (by omega) ≈
        Q'.mkPos 5 6 (by decide) := by
  decide

/-- The same-operator lift is not the Jacobi action.  This prevents the raw
and dual operators from being silently identified. -/
theorem mixed221_raw_operator_is_not_section_transpose :
    ¬ (endpointRawOperatorSectionForward 2 2 1 2
      (by omega) (by omega) (by omega) (by omega) (by omega) ≈
        jacobiForward 2 2 1 1 0) := by
  decide

/-- The actual fundamental reconstructed-section coefficient is `1/2`. -/
theorem fundamental_reconstructed_section_forward_eq_jacobi :
    endpointReconstructedSectionForward 1 1 1 1
      (by omega) (by omega) (by omega) (by omega) (by omega) ≈
        jacobiForward 1 1 1 1 0 := by
  decide

/-- The actual mixed reconstructed-section coefficient is `1/3`. -/
theorem mixed221_reconstructed_section_forward_eq_jacobi :
    endpointReconstructedSectionForward 2 2 1 2
      (by omega) (by omega) (by omega) (by omega) (by omega) ≈
        jacobiForward 2 2 1 1 0 := by
  decide

/-- The full mixed endpoint raw identity, including every source-coordinate
boundary.  This distinguishes the finite-transpose issue from a boundary
failure in this block. -/
theorem mixed221_raw_endpoint_identity_full_box :
    ∀ i, i < 3 → ∀ j, j < 3 → ∀ l, l < 2 →
      Q'.ofNat 3 *
          pairExchange 2 2
            (fun x y => endpointZeroCarrier 2 2 1 2 x y l) i j ≈
        Q'.ofNat 8 *
          (Q'.ofNat 1 * endpointOneCarrier 2 2 1 2 i j l +
            -(Q'.ofNat 2 * endpointZeroCarrier 2 2 1 2 i j l)) := by
  decide

/-- Full invariant pairing of the fundamental raw endpoint action. -/
def triMapFirstPairExchangeInner (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm) : Q' :=
  finSum (fun i => finSum (fun j => finSum (fun l => finSum (fun s =>
    tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
      symMonomialNormSq d s *
        (pairExchange a b
          (fun u v => L (mono u) (mono v) (mono l) s) i j *
          R (mono i) (mono j) (mono l) s)) (d + 1)) (c + 1))
            (b + 1)) (a + 1)

theorem fundamental_full_gram_raw_endpoint :
    triMapFirstPairExchangeInner 1 1 1 1
      (triRight 1 1 1 1 2) (triRight 1 1 1 1 0) ≈
      rawEndpointForward 1 1 1 1 * triRightChannelWeight 1 1 1 1 0 := by
  decide

theorem mixed221_full_gram_raw_endpoint :
    triMapFirstPairExchangeInner 2 2 1 1
      (triRight 2 2 1 1 3) (triRight 2 2 1 1 1) ≈
      rawEndpointForward 2 2 1 2 * triRightChannelWeight 2 2 1 1 1 := by
  decide

/-! ## Actual section-side Gram transpose and pinned endpoint equations -/

/-- The fundamental Gram-transpose equation is satisfied by the explicit
coefficient extracted from `fixedRightSection`. -/
theorem fundamental_reconstructed_section_gram_transpose :
    SectionForwardGramTranspose
      (triRightChannelWeight 1 1 1 1 2)
      (triRightChannelWeight 1 1 1 1 0)
      (rawEndpointForward 1 1 1 1)
      (endpointReconstructedSectionForward 1 1 1 1
        (by omega) (by omega) (by omega) (by omega) (by omega)) := by
  unfold SectionForwardGramTranspose
  decide

/-- The mixed Gram-transpose equation is likewise inhabited by the explicit
`fixedRightSection` coefficient, not by an abstract variable. -/
theorem mixed221_reconstructed_section_gram_transpose :
    SectionForwardGramTranspose
      (triRightChannelWeight 2 2 1 1 3)
      (triRightChannelWeight 2 2 1 1 1)
      (rawEndpointForward 2 2 1 2)
      (endpointReconstructedSectionForward 2 2 1 2
        (by omega) (by omega) (by omega) (by omega) (by omega)) := by
  unfold SectionForwardGramTranspose
  decide

/-- Actual fundamental endpoint package: reconstructed coefficient, Gram
transpose, and both candidate rows at `p=0`. -/
theorem fundamental_reconstructed_endpoint_candidate_package :
    endpointReconstructedSectionForward 1 1 1 1
        (by omega) (by omega) (by omega) (by omega) (by omega) ≈
      jacobiForward 1 1 1 1 0 ∧
    SectionForwardGramTranspose
      (triRightChannelWeight 1 1 1 1 2)
      (triRightChannelWeight 1 1 1 1 0)
      (rawEndpointForward 1 1 1 1)
      (endpointReconstructedSectionForward 1 1 1 1
        (by omega) (by omega) (by omega) (by omega) (by omega)) ∧
    CandidateJacobiAt 1 1 1 1 0 0 ∧
    CandidateJacobiAt 1 1 1 1 2 0 := by
  exact ⟨fundamental_reconstructed_section_forward_eq_jacobi,
    fundamental_reconstructed_section_gram_transpose,
    fundamental_candidate_jacobi_audit.1,
    fundamental_candidate_jacobi_audit.2.2.1⟩

/-- Actual mixed endpoint package with both signed candidate rows. -/
theorem mixed221_reconstructed_endpoint_candidate_package :
    endpointReconstructedSectionForward 2 2 1 2
        (by omega) (by omega) (by omega) (by omega) (by omega) ≈
      jacobiForward 2 2 1 1 0 ∧
    SectionForwardGramTranspose
      (triRightChannelWeight 2 2 1 1 3)
      (triRightChannelWeight 2 2 1 1 1)
      (rawEndpointForward 2 2 1 2)
      (endpointReconstructedSectionForward 2 2 1 2
        (by omega) (by omega) (by omega) (by omega) (by omega)) ∧
    CandidateJacobiAt 2 2 1 1 0 0 ∧
    CandidateJacobiAt 2 2 1 1 2 0 := by
  exact ⟨mixed221_reconstructed_section_forward_eq_jacobi,
    mixed221_reconstructed_section_gram_transpose,
    mixed221_candidate_jacobi_audit.1,
    mixed221_candidate_jacobi_audit.2.2.1⟩

end YMGap.Continuum.SU2OrderedRacahEndpointReconstructedSection

#print axioms YMGap.Continuum.SU2OrderedRacahEndpointReconstructedSection.mixed221_raw_operator_is_not_section_transpose
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointReconstructedSection.fundamental_reconstructed_section_forward_eq_jacobi
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointReconstructedSection.mixed221_reconstructed_section_forward_eq_jacobi
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointReconstructedSection.mixed221_raw_endpoint_identity_full_box
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointReconstructedSection.fundamental_reconstructed_section_gram_transpose
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointReconstructedSection.mixed221_reconstructed_section_gram_transpose
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointReconstructedSection.fundamental_reconstructed_endpoint_candidate_package
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointReconstructedSection.mixed221_reconstructed_endpoint_candidate_package
