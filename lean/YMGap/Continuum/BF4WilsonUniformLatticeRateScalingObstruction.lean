/-
# Uniform lattice contraction extinguishes bounded Wilson responses in scaling

Allow the nome, completed carrier and excitation to vary with scale. If the
ACTUAL Wilson two-step bounds admit one q<1 and the squared norms have one
finite cap, the original even-time autocorrelation at floor(t/a_j) two-step
intervals tends to zero for each positive integer physical time t. The scale
modulus is the spacing modulus composed with the existing geometric cutoff.

Here a_j is explicitly the physical duration of TWO original lattice time
steps (2 times the one-step spacing). No physical normalization is inferred
from a bare scalar assignment. The fixed-nome norm-one original Wilson
excitation supplies a concrete instance of the hypotheses.

This is a same-correlator obstruction to retaining a uniformly strict lattice
rate and uniformly bounded states in a nonzero positive-time scaling channel.
It is not a Yang--Mills counterexample, an assertion that arbitrary changing
couplings obey this rate, or a construction of the missing continuum theory.
-/

import YMGap.Continuum.PhysicalSeparationSamplingEscape
import YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
import YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
import YMGap.Continuum.RCDistBridge

namespace YMGap.Continuum.BF4WilsonUniformLatticeRateScalingObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PhysicalSeparatorLogRate (PhysicalSpacing)
open YMGap.Continuum.PhysicalSeparatorLinearTail (SpacingToZero)
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero (floorLatticeSteps)
open YMGap.Continuum.PhysicalSeparationSamplingEscape
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation (even_autocorrelation_decay)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Computed scale threshold, retaining rate, amplitude, physical time and tolerance. -/
def physicalDecayModulus {A : PhysicalSpacing} (Z : SpacingToZero A)
    (q C : Q') (t : Nat) (epsilon : Q') : Nat :=
  stepEscapeModulus A Z t (geometricCutoff q C epsilon)

section VaryingNome

variable {w : Nat → Q'} (hw0 : ∀ j, (0 : Q') < w j) (hw1 : ∀ j, w j < (1 : Q'))
  (hsmall : ∀ j, heatRatio (w j) ≤ HalfPow.half)
  (hd : ∀ j, heatRemainderBound (w j) < 1)
  (hs : ∀ j, entropyRate 625 (adjustedCoreRate (w j) (hd j)) < 1)

local notation:max "B" j:arg => completedInner (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j)
local notation:max "T" j:arg => completedTime (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j)
local notation:max "U" j:arg => completedUnit (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j)

variable (x : (j : Nat) → UnionCompletion (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j))

/-- Literal original even-time pairing at the sampled physical separation. -/
def sampledAutocorrelation (A : PhysicalSpacing) (t j : Nat) : RC :=
  B j (x j) (T j (2 * floorLatticeSteps A j t) (x j))

theorem sampledAutocorrelation_nonnegative (A : PhysicalSpacing) (t j : Nat) :
    RCnonneg (sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j) := by
  unfold sampledAutocorrelation
  rw [completedInner_even_diagonal]
  exact completedInner_nonnegative (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j) _

/-- A common rate is a hypothesis about this family, not a claim of all-coupling uniformity. -/
theorem sampledAutocorrelation_geometric
    (hx : ∀ j, B j (x j) (U j) = RCzero)
    (q C : Q') (hC : (0 : Q') ≤ C)
    (hq : ∀ j, twoStepRate (w j) (hd j) ≤ q)
    (hcap : ∀ j, RCle (B j (x j) (x j)) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (t j : Nat) :
    RCle (sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)
      (Quotient.mk crealSetoid (ofQ' (q ^ floorLatticeSteps A j t * C))) := by
  let n := floorLatticeSteps A j t
  have h := RCle_trans
    (even_autocorrelation_decay (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j) (x j) (hx j) n)
    (RCscale_mono (Q'.pow_nonneg _ (Q'.le_of_lt (twoStepRate_positive (hw0 j) (hd j))) n)
      (hcap j))
  exact RCle_trans h (leEv_le_ofQ'_of_approx_le (fun _ =>
    Q'.mul_le_mul_of_nonneg_right _ _ C
      (HKConv.pow_le_pow_base (Q'.le_of_lt (twoStepRate_positive (hw0 j) (hd j))) (hq j) n) hC))

/-- An entire late tail of the SAME correlation is bounded by the requested tolerance. -/
theorem sampledAutocorrelation_small
    (hx : ∀ j, B j (x j) (U j) = RCzero)
    (q C : Q') (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q')) (hC : (0 : Q') ≤ C)
    (hq : ∀ j, twoStepRate (w j) (hd j) ≤ q)
    (hcap : ∀ j, RCle (B j (x j) (x j)) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t)
    (epsilon : Q') (he : (0 : Q') < epsilon) (j : Nat)
    (hj : physicalDecayModulus Z q C t epsilon ≤ j) :
    RCle (sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hn := floorLatticeSteps_ge_stepEscapeModulus A Z ht hj
  exact RCle_trans (sampledAutocorrelation_geometric hw0 hw1 hsmall hd hs x hx q C hC hq hcap A t j)
    (leEv_le_ofQ'_of_approx_le (fun _ => geometric_bound hq0 hq1 hC he _ hn))

/-- A surviving response forces the ACTUAL certified lattice rate above every
fixed test q<1 once the computed spacing threshold is reached. This is a
necessary condition, not a proof of a surviving channel or a sufficient mass calibration. -/
theorem rate_gt_of_response_floor
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t)
    (q C floor : Q') (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor) (j : Nat)
    (hj : physicalDecayModulus Z q C t (HalfPow.half * floor) ≤ j)
    (hx : B j (x j) (U j) = RCzero)
    (hcap : RCle (B j (x j) (x j)) (Quotient.mk crealSetoid (ofQ' C)))
    (hfloor : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)) :
    q < twoStepRate (w j) (hd j) := by
  apply Int.lt_of_not_ge
  intro hbound
  have hdecay := sampledAutocorrelation_small
    (fun _ => hw0 j) (fun _ => hw1 j) (fun _ => hsmall j) (fun _ => hd j) (fun _ => hs j)
    (fun _ => x j) (fun _ => hx) q C hq0 hq1 hC
    (fun _ => hbound) (fun _ => hcap) A Z t ht
    (HalfPow.half * floor) (ExpNeg.half_mul_pos floor hf) j hj
  have hbad := GNSQuotient.GNSData.RCofQ'_le_reflect (RCle_trans hfloor hdecay)
  have hstrict : HalfPow.half * floor < floor :=
    ClusteringImpliesGap.lt_of_lt_of_le (ClusteringImpliesGap.mul_lt_mul_of_pos_right hf
      (by decide : HalfPow.half < (1 : Q')))
      (Q'.le_of_eqv (Q'.one_mul_eqv floor))
  exact Int.not_lt.mpr hbad hstrict

/-- Representative-level convergence requires a supplied same-scalar pin, not choice. -/
theorem sampledRepresentative_converges_zero
    (hx : ∀ j, B j (x j) (U j) = RCzero)
    (q C : Q') (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q')) (hC : (0 : Q') ≤ C)
    (hq : ∀ j, twoStepRate (w j) (hd j) ≤ q)
    (hcap : ∀ j, RCle (B j (x j) (x j)) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t)
    (f : Nat → CReal)
    (hpin : ∀ j, Quotient.mk crealSetoid (f j) =
      sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j) :
    ConvergesTo f czero := by
  intro epsilon he
  let delta := HalfPow.half * epsilon
  have hdelta : (0 : Q') < delta := ExpNeg.half_mul_pos epsilon he
  refine ⟨physicalDecayModulus Z q C t delta, fun j hj => ?_⟩
  have hu := sampledAutocorrelation_small hw0 hw1 hsmall hd hs x hx q C hq0 hq1 hC hq hcap
    A Z t ht delta hdelta j hj
  have hl := sampledAutocorrelation_nonnegative hw0 hw1 hsmall hd hs x A t j
  rw [← hpin j] at hu hl
  obtain ⟨N, hN⟩ := hu delta hdelta
  obtain ⟨M, hM⟩ := hl epsilon he
  refine ⟨max N M, fun n hn => ⟨?_, hM n (by omega)⟩⟩
  exact Q'.le_trans' _ _ _ (hN n (by omega))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (ExpNeg.two_halves epsilon)
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))

/-- Any supplied limit of these same scalar representatives is necessarily zero. -/
theorem sampledLimit_zero
    (hx : ∀ j, B j (x j) (U j) = RCzero)
    (q C : Q') (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q')) (hC : (0 : Q') ≤ C)
    (hq : ∀ j, twoStepRate (w j) (hd j) ≤ q)
    (hcap : ∀ j, RCle (B j (x j) (x j)) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t)
    (f : Nat → CReal)
    (hpin : ∀ j, Quotient.mk crealSetoid (f j) =
      sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)
    (l : CReal) (hlimit : ConvergesTo f l) : Equiv l czero :=
  Equiv_of_limit_of_equal (fun j => Equiv.refl (f j)) hlimit
    (sampledRepresentative_converges_zero hw0 hw1 hsmall hd hs x hx q C hq0 hq1 hC hq hcap
      A Z t ht f hpin)

end VaryingNome

/-- A computed violating scale beyond any requested tail start. -/
def survivalCounterexampleScale {A : PhysicalSpacing} (Z : SpacingToZero A)
    (q C : Q') (t : Nat) (floor : Q') (start : Nat) : Nat :=
  max start (physicalDecayModulus Z q C t (HalfPow.half * floor))

theorem survivalCounterexampleScale_ge_start {A : PhysicalSpacing} (Z : SpacingToZero A)
    (q C : Q') (t : Nat) (floor : Q') (start : Nat) :
    start ≤ survivalCounterexampleScale Z q C t floor start := Nat.le_max_left _ _

section CurrentExcitation

open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs

/-- The original, already constructed norm-one Wilson excitation; no supplied analytic guard. -/
def currentSampledAutocorrelation (A : PhysicalSpacing) (t j : Nat) : RC :=
  B unitExcitation (T (2 * floorLatticeSteps A j t) unitExcitation)

/-- The positive zero-time norm survives identically; it does not ensure a positive-time response. -/
theorem currentSampledAutocorrelation_zero (A : PhysicalSpacing) (j : Nat) :
    currentSampledAutocorrelation A 0 j = Quotient.mk crealSetoid cone := by
  simp only [currentSampledAutocorrelation, floorLatticeSteps, Nat.zero_mul, Nat.zero_div,
    Nat.mul_zero, completedTime_zero, unitExcitation_norm]

theorem currentSampledAutocorrelation_small
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t)
    (epsilon : Q') (he : (0 : Q') < epsilon) (j : Nat)
    (hj : physicalDecayModulus Z rayleighCeiling 1 t epsilon ≤ j) :
    RCle (currentSampledAutocorrelation A t j) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  exact sampledAutocorrelation_small
    (fun _ => nome_pos) (fun _ => nome_lt_one) (fun _ => hsmall) (fun _ => hd) (fun _ => hs)
    (fun _ => unitExcitation) (fun _ => unitExcitation_orthogonal)
    rayleighCeiling 1 (Q'.le_of_lt (twoStepRate_positive nome_pos hd))
    rayleighCeiling_lt_one Q'.zero_le_one (fun _ => Q'.le_refl' _)
    (fun _ => by rw [unitExcitation_norm]; exact RCle_refl _)
    A Z t ht epsilon he j hj

/-- Relabelling a fixed lattice theory with shrinking spacing cannot preserve a positive
late-tail response of its actual normalized excitation at positive sampled physical time. -/
theorem currentResponse_not_above_floor
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t)
    (floor : Q') (hf : (0 : Q') < floor) (start : Nat) :
    ¬ RCle (Quotient.mk crealSetoid (ofQ' floor))
      (currentSampledAutocorrelation A t
        (survivalCounterexampleScale Z rayleighCeiling 1 t floor start)) := by
  intro hfloor
  have hdecay := currentSampledAutocorrelation_small A Z t ht
    (HalfPow.half * floor) (ExpNeg.half_mul_pos floor hf)
    (survivalCounterexampleScale Z rayleighCeiling 1 t floor start) (Nat.le_max_right _ _)
  have hbad := GNSQuotient.GNSData.RCofQ'_le_reflect (RCle_trans hfloor hdecay)
  have hstrict : HalfPow.half * floor < floor :=
    ClusteringImpliesGap.lt_of_lt_of_le (ClusteringImpliesGap.mul_lt_mul_of_pos_right hf
      (by decide : HalfPow.half < (1 : Q')))
      (Q'.le_of_eqv (Q'.one_mul_eqv floor))
  exact Int.not_lt.mpr hbad hstrict

#print axioms physicalDecayModulus
#print axioms sampledAutocorrelation
#print axioms sampledAutocorrelation_nonnegative
#print axioms sampledAutocorrelation_geometric
#print axioms sampledAutocorrelation_small
#print axioms rate_gt_of_response_floor
#print axioms sampledRepresentative_converges_zero
#print axioms sampledLimit_zero
#print axioms survivalCounterexampleScale
#print axioms survivalCounterexampleScale_ge_start
#print axioms currentSampledAutocorrelation
#print axioms currentSampledAutocorrelation_zero
#print axioms currentSampledAutocorrelation_small
#print axioms currentResponse_not_above_floor

end CurrentExcitation

end YMGap.Continuum.BF4WilsonUniformLatticeRateScalingObstruction
