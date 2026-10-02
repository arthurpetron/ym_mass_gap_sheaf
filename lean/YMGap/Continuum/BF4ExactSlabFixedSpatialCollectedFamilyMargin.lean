/-
# Coalesced ORIGINAL terminal iteration and signed-margin evaluation

Collect equal monomials during every finite terminal step, not only after
constructing the original raw expansion. The deterministic rational collector
preserves every coefficient probe. Both endpoint terminal factors, all spatial
weights, the joint spectator projection and both OWN means remain present.

At fixed cutoff and width, terminal representation length is bounded at every
depth. At fixed cutoff and family length, each collected margin numerator has
a depth/width-independent length ceiling from the existing exponent universe.
These are representation bounds, not coefficient-bit-size, runtime, positive-
margin, scaling-family, continuum or physical mass claims.
-/

import YMGap.Continuum.SU2QuaternionSparseCoefficientCollector
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointDegree

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCollectedFamilyMargin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.SU2QuaternionSparseCoefficientCollector
open YMGap.Continuum.SU2QuaternionBlockDegreeBound
open YMGap.Continuum.SU2QuaternionBoundedMonomials
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_coeff)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
  (supported_upper_independent lift_lower_independent)
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
  (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticDegree
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDegree
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointDegree
  (step_degree_reset liftBoundary_degree compress_degree marginInsertions
    marginInsertions_degree marginMonomials)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (edgeDensity jump)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointDensity
  (observableCopies observableCopies_length spectatorCopies footprintEmbedding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyExpression family_within)
open YMGap.Continuum.BF4WilsonAllNomeFiniteReferenceMargin (referenceMargin referenceCutoff)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- Equal keys are combined BEFORE the next terminal step is evaluated. -/
def iterate (blocks : Nat) (kernel weight : RatPoly) : Nat → RatPoly → RatPoly
  | 0, input => collect input
  | count+1, input =>
      iterate blocks kernel weight count (collect (step blocks kernel weight input))

/-- Full coefficient equality, not merely equality of one Haar integral. -/
theorem iterate_coeff (blocks : Nat) {kernel weight kernel' weight' : RatPoly}
    (hk : RatPolyCoeffEqv kernel kernel') (hw : RatPolyCoeffEqv weight weight')
    (count : Nat) {input input' : RatPoly} (hi : RatPolyCoeffEqv input input') :
    RatPolyCoeffEqv (iterate blocks kernel weight count input)
      (iterateStep blocks kernel' weight' count input') := by
  induction count generalizing input input' with
  | zero => exact (collect_coeff input).trans hi
  | succ count ih =>
      exact ih ((collect_coeff _).trans
        (partialHaarHeads_congr blocks (hk.mul (hw.mul hi))))

theorem iterate_supported {blocks : Nat} {kernel weight : RatPoly}
    (hk : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hw : SupportedQuaternionBlocks blocks weight) (count : Nat)
    {input : RatPoly} (hi : SupportedQuaternionBlocks blocks input) :
    SupportedQuaternionBlocks blocks (iterate blocks kernel weight count input) := by
  induction count generalizing input with
  | zero => exact collect_supported hi
  | succ count ih => exact ih (collect_supported (step_supported hk hw hi))

theorem iterate_degree {blocks i d : Nat} {kernel weight : RatPoly}
    (hk : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hw : SupportedQuaternionBlocks blocks weight)
    (hd : DegreeLE (blocks+i) d kernel) (count : Nat)
    {input : RatPoly} (hi : SupportedQuaternionBlocks blocks input)
    (hdi : DegreeLE i d input) :
    DegreeLE i d (iterate blocks kernel weight count input) := by
  induction count generalizing input with
  | zero => exact collect_degree hdi
  | succ count ih =>
      exact ih (collect_supported (step_supported hk hw hi))
        (collect_degree (step_degree_reset hd hw hi))

theorem iterate_nodup (blocks : Nat) (kernel weight : RatPoly)
    (count : Nat) (input : RatPoly) :
    ((iterate blocks kernel weight count input).map Prod.fst).Nodup := by
  induction count generalizing input with
  | zero => exact collect_nodup input
  | succ count ih => exact ih _

/-- The original kinetic/spatial polynomials are collected once as inputs to
the recursive evaluator. No terminal message is supplied as a hypothesis. -/
def terminal (w : Q') (K width depth : Nat) : RatPoly :=
  iterate (N width) (collect (kineticWeight w K width))
    (collect (spatialWeight w K width)) depth polyOne

theorem terminal_coeff (w : Q') (K width depth : Nat) :
    RatPolyCoeffEqv (terminal w K width depth) (terminalMessage w K width depth) :=
  iterate_coeff (N width) (collect_coeff _) (collect_coeff _) depth (.refl _)

theorem terminal_supported (w : Q') (K width depth : Nat) :
    SupportedQuaternionBlocks (N width) (terminal w K width depth) :=
  iterate_supported (collect_supported (kineticWeight_supported w K width))
    (collect_supported (spatialWeight_supported w K width)) depth (supported_one _)

theorem terminal_degree (w : Q') (K width depth i : Nat) (hi : i < N width) :
    DegreeLE i K (terminal w K width depth) :=
  iterate_degree (collect_supported (kineticWeight_supported w K width))
    (collect_supported (spatialWeight_supported w K width))
    (collect_degree (kineticWeight_upper_degree w K width i hi)) depth
    (supported_one _) (DegreeLE.one i K)

/-- Actual terminal term-list length, independent of depth and nome at fixed
cutoff/width; coefficient sizes and cost of one step are not bounded here. -/
theorem terminal_length (w : Q') (K width depth : Nat) :
    (terminal w K width depth).length ≤
      (monomials (N width) (fun _ => K)).length := by
  apply length_le_cover _ (iterate_nodup _ _ _ _ _) _
  intro m hm
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  exact mem_monomials_of_degree _ _ _ (terminal_supported w K width depth t ht)
    (fun i hi => terminal_degree w K width depth i hi t ht)

private theorem edge_coeff (w : Q') (K width depth : Nat) :
    RatPolyCoeffEqv (edgeDensity w K width (terminal w K width depth))
      (edgeDensity w K width (terminalMessage w K width depth)) := by
  have hv := (RatPolyCoeffEqv.refl (spatialWeight w K width)).mul
    (terminal_coeff w K width depth)
  exact ((RatPolyCoeffEqv.refl _).mul hv).mul (lift_coeff (N width) hv)

/-- The SAME joint spectator projection, with the constructed collected
terminal evaluator at BOTH endpoints. Equal keys are coalesced afterwards. -/
def density (w : Q') (K width depth : Nat) (qs : List Z4Plaq) : RatPoly :=
  collect (familyProject (spectatorCopies width qs)
    (edgeDensity w K width (terminal w K width depth)))

theorem density_coeff (w : Q') (K width depth : Nat) (qs : List Z4Plaq) :
    RatPolyCoeffEqv (density w K width depth qs)
      (BF4ExactSlabFixedSpatialFamilyJointDensity.density w K width depth qs) :=
  (collect_coeff _).trans (familyProject_congr _ (edge_coeff w K width depth))

private theorem edge_lower_degree (w : Q') (K width depth i : Nat) (hi : i < N width) :
    DegreeLE i (8*K) (edgeDensity w K width (terminal w K width depth)) := by
  have hl := (kineticWeight_lower_degree w K width i hi).mul
    ((spatialWeight_degree w K width i hi).mul (terminal_degree w K width depth i hi))
  have hu := DegreeLE.of_independent (lift_lower_independent (N width)
    (polyMul (spatialWeight w K width) (terminal w K width depth)) i hi)
  simpa only [edgeDensity, Nat.add_zero, show K+(6*K+K) = 8*K by omega] using hl.mul hu

private theorem edge_upper_degree (w : Q') (K width depth i : Nat) (hi : i < N width) :
    DegreeLE (N width+i) (8*K) (edgeDensity w K width (terminal w K width depth)) := by
  have hs := supported_polyMul (spatialWeight_supported w K width)
    (terminal_supported w K width depth)
  have hl := (kineticWeight_upper_degree w K width i hi).mul
    (DegreeLE.of_independent (supported_upper_independent hs i))
  have hu := liftBoundary_degree (N width) i _
    ((spatialWeight_degree w K width i hi).mul (terminal_degree w K width depth i hi))
  simpa only [edgeDensity, Nat.add_zero, show K+(6*K+K) = 8*K by omega] using hl.mul hu

theorem density_degree (w : Q') (K width depth : Nat) (qs : List Z4Plaq)
    (i : Nat) (hi : i < N width+N width) : DegreeLE i (8*K) (density w K width depth qs) := by
  apply collect_degree
  apply familyProject_degree
  by_cases h : i < N width
  · exact edge_lower_degree w K width depth i h
  · have he : N width+(i-N width) = i := by omega
    simpa only [he] using edge_upper_degree w K width depth (i-N width) (by omega)

private theorem weighted_compress {source target : Nat} (E : BlockEmbedding source target)
    (weight : List Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum weight (E.compress p) ≈
      ratWeightedSum (fun m => weight (E.compressExponents m)) p
  | [] => Q'.eqv_refl _
  | _t::p => Q'.add_eqv_congr' (Q'.eqv_refl _) (weighted_compress E weight p)

/-- Arbitrary coefficient probes commute with the literal exponent map. -/
theorem compress_coeff {source target : Nat} (E : BlockEmbedding source target)
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (E.compress p) (E.compress q) := by
  intro weight
  exact Q'.eqv_trans _ _ _ (weighted_compress E weight p)
    (Q'.eqv_trans _ _ _ (h (fun m => weight (E.compressExponents m)))
      (Q'.eqv_symm (weighted_compress E weight q)))

/-- Computed collected numerator; the input signed polynomial is unchanged. -/
def numerator (w : Q') (K width depth : Nat) (qs : List Z4Plaq) (p : RatPoly) : RatPoly :=
  collect ((footprintEmbedding width qs).compress (polyMul (density w K width depth qs) p))

theorem numerator_coeff (w : Q') (K width depth : Nat) (qs : List Z4Plaq) (p : RatPoly) :
    RatPolyCoeffEqv (numerator w K width depth qs p)
      ((footprintEmbedding width qs).compress
        (polyMul (BF4ExactSlabFixedSpatialFamilyJointDensity.density w K width depth qs) p)) :=
  (collect_coeff _).trans (compress_coeff _ ((density_coeff w K width depth qs).mul (.refl p)))

/-- This bounds the ACTUAL collected representation, not the raw expansion.
All six insertions include OWN means and the COMPLETE signed increment. -/
theorem numerator_length (w : Q') (K width depth : Nat) (coeff : Z4Plaq → Q')
    (qs : List Z4Plaq) (hqs : ∀ q, q ∈ qs → q ∈ spatialFaces width)
    (p : RatPoly) (hp : p ∈ marginInsertions width coeff qs) :
    (numerator w K width depth qs p).length ≤ (marginMonomials K qs.length).length := by
  apply collect_length_le_cover
  intro m hm
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  have hs := (footprintEmbedding width qs).compress_supported
    (polyMul (density w K width depth qs) p)
  apply mem_monomials_of_degree _ _ _
    (Nat.le_trans (hs t ht) (Nat.mul_le_mul_left 4 (observableCopies_length width qs)))
  intro i _hi
  by_cases h : i < (observableCopies width qs).length
  · have hd := compress_degree (footprintEmbedding width qs) i h (8*K+2)
      ((density_degree w K width depth qs _ ((footprintEmbedding width qs).block_lt h)).mul
        (marginInsertions_degree width coeff qs hqs p hp _
          ((footprintEmbedding width qs).block_lt h)))
    exact hd t ht
  · have he : (observableCopies width qs).length+
        (i-(observableCopies width qs).length) = i := by omega
    have hz := DegreeLE.of_independent
      (supported_upper_independent hs (i-(observableCopies width qs).length))
    have hz' : DegreeLE i 0 ((footprintEmbedding width qs).compress
        (polyMul (density w K width depth qs) p)) := by simpa only [he] using hz
    exact Nat.le_trans (hz' t ht) (Nat.zero_le _)

def pairing (w : Q') (K width depth : Nat) (qs : List Z4Plaq) (p : RatPoly) : Q' :=
  quaternionHaar (observableCopies width qs).length (numerator w K width depth qs p)

/-- The alternative recurrence evaluates the original compressed pairing. -/
theorem pairing_pin (w : Q') (K width depth : Nat) (qs : List Z4Plaq) (p : RatPoly) :
    pairing w K width depth qs p ≈
      BF4ExactSlabFixedSpatialFamilyJointDensity.compressedPairing w K width depth qs p :=
  haar_of_coeff (numerator_coeff w K width depth qs p)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (qs : List Z4Plaq)

include hw0 hw1 hK in
theorem mass_positive : (0 : Q') < pairing w K width depth qs polyOne :=
  HeatKernelRGStep.lt_of_lt_of_le
    (BF4ExactSlabFixedSpatialFamilyJointDensity.compressedMass_positive hw0 hw1 K width hK depth qs)
    (Q'.ge_of_eqv (pairing_pin w K width depth qs polyOne))

def moment (p : RatPoly) : Q' :=
  pairing w K width depth qs p * Q'.recipPos (pairing w K width depth qs polyOne)
    (mass_positive hw0 hw1 K width hK depth qs)

theorem moment_pin (p : RatPoly) : moment hw0 hw1 K width hK depth qs p ≈
    BF4ExactSlabFixedSpatialFamilyJointDensity.moment hw0 hw1 K width hK depth qs p :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (pairing_pin w K width depth qs p))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.recipPos_eqv_congr _ _
      (mass_positive hw0 hw1 K width hK depth qs)
      (BF4ExactSlabFixedSpatialFamilyJointDensity.compressedMass_positive hw0 hw1 K width hK depth qs)
      (pairing_pin w K width depth qs polyOne)))

/-- The executable signed margin keeps OWN centering and the whole jump. -/
def margin (coeff : Z4Plaq → Q') (c : Q') : Q' :=
  let f := spatialSpan width coeff qs
  let j := jump width f
  c*(moment hw0 hw1 K width hK depth qs (polyMul f f) +
    -(moment hw0 hw1 K width hK depth qs f * moment hw0 hw1 K width hK depth qs f)) +
    -(HalfPow.half * moment hw0 hw1 K width hK depth qs (polyMul j j))

theorem margin_pin (coeff : Z4Plaq → Q') (c : Q') :
    margin hw0 hw1 K width hK depth qs coeff c ≈
      BF4ExactSlabFixedSpatialFamilyJointDensity.margin hw0 hw1 K width hK depth qs coeff c :=
  Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left c _ _ (Q'.add_eqv_congr'
      (moment_pin hw0 hw1 K width hK depth qs _)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (moment_pin hw0 hw1 K width hK depth qs _))
        (Q'.mul_eqv_congr_left _ _ _ (moment_pin hw0 hw1 K width hK depth qs _))))))
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left HalfPow.half _ _
      (moment_pin hw0 hw1 K width hK depth qs _)))

/-- Direct pin to the existing finite reference checker input, at its actual
cutoff pivot and padded original physical family. No margin is assumed. -/
theorem finite_margin_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base width : Nat} (hwidth : base < width) (qs : List Z4Plaq)
    (coeff : Z4Plaq → Q') (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)
    (stage t : Nat) (c : Q') :
    margin hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) t qs coeff c ≈
      referenceMargin hw0 hw1
        (familyExpression width qs coeff
          (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))) c stage t :=
  Q'.eqv_trans _ _ _
    (margin_pin hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) t qs coeff c)
    (BF4ExactSlabFixedSpatialFamilyJointDensity.finite_margin_pin
      hw0 hw1 width qs hwidth coeff hqs stage t c)

section Checker

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {base width : Nat} (hwidth : base < width) (qs : List Z4Plaq)
  (coeff : Z4Plaq → Q') (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)

local notation "wideFaces" =>
  (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
local notation "e" => familyExpression width qs coeff wideFaces
local notation "he" => family_within width qs coeff wideFaces

/-- The original acceptance conditions, evaluated through the collected
recurrence. The original cutoff modulus and required slack are UNCHANGED. -/
def check (s : Nat) (c epsilon : Q') (pivot : Nat) : Bool :=
  decide ((0 : Q') ≤ c ∧ (0 : Q') < epsilon ∧
    referenceCutoff hw0 hw1 e he c (s+1) epsilon ≤ pivot ∧
    epsilon+epsilon ≤ margin hw0 hw1 (headCutoff w+pivot) width
      (Nat.le_add_right _ _) (s+1) qs coeff c)

/-- Collection accepts exactly the same finite data as the original checker.
No successful input or changing-family estimate is supplied here. -/
theorem check_correct (s : Nat) (c epsilon : Q') (pivot : Nat) :
    check hw0 hw1 hwidth qs coeff hqs s c epsilon pivot = true ↔
      BF4WilsonAllNomeFiniteReferenceMargin.check hw0 hw1 e he s c epsilon pivot = true := by
  have pin := finite_margin_pin hw0 hw1 hwidth qs coeff hqs pivot (s+1) c
  constructor
  · intro h
    have H := of_decide_eq_true h
    apply decide_eq_true
    exact ⟨H.1, H.2.1, H.2.2.1, Q'.le_trans' _ _ _ H.2.2.2 (Q'.le_of_eqv pin)⟩
  · intro h
    have H := of_decide_eq_true h
    apply decide_eq_true
    exact ⟨H.1, H.2.1, H.2.2.1, Q'.le_trans' _ _ _ H.2.2.2 (Q'.ge_of_eqv pin)⟩

/-- A genuine executable certificate producer: failure returns none;
success carries the EXISTING original finite certificate as data. -/
def certify (s : Nat) (c epsilon : Q') (pivot : Nat) :
    Option (BF4WilsonAllNomeFiniteReferenceMargin.Certificate hw0 hw1 e he s c) :=
  if h : check hw0 hw1 hwidth qs coeff hqs s c epsilon pivot = true then
    some {
      tolerance := epsilon
      pivot := pivot
      accepted := (check_correct hw0 hw1 hwidth qs coeff hqs s c epsilon pivot).mp h
    }
  else none

end Checker

#print axioms iterate
#print axioms iterate_coeff
#print axioms iterate_supported
#print axioms iterate_degree
#print axioms iterate_nodup
#print axioms terminal
#print axioms terminal_coeff
#print axioms terminal_supported
#print axioms terminal_degree
#print axioms terminal_length
#print axioms density
#print axioms density_coeff
#print axioms density_degree
#print axioms compress_coeff
#print axioms numerator
#print axioms numerator_coeff
#print axioms numerator_length
#print axioms pairing
#print axioms pairing_pin
#print axioms mass_positive
#print axioms moment
#print axioms moment_pin
#print axioms margin
#print axioms margin_pin
#print axioms finite_margin_pin
#print axioms check
#print axioms check_correct
#print axioms certify

end YMGap.Continuum.BF4ExactSlabFixedSpatialCollectedFamilyMargin
