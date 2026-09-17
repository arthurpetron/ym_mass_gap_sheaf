/-
# Signed spatial plaquette families on the original one-step window

The source is a literal rational linear combination of fundamental spatial
plaquette characters. The schedule places its positive coefficients at offset
zero and their negatives at offset one. It is coefficientwise the original
jump polynomial. Its literal placed polynomial is the boundary-family span on
the existing doubled time labels, with exactly the same coefficients.

These pins retain every signed cross term when squared. No positivity of the
coefficients, common private link, variance estimate, or spectral gap is assumed
or proved. The consumer is the original normalized temporal-energy identity.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyLabels
import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily
import YMGap.Continuum.PolynomialWeightedSumBounds

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (sourceSpan placedSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (jump)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyLabels
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (supported_smul)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary liftHead)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_add lift_smul lift_coeff)
open YMGap.Continuum.PolynomialWeightedSumBounds (sum_append sum_map)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_add)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] plaquette correctedSlabPlaquettePolynomial baseLinks

/-- The original fixed-slice character polynomial with every signed coefficient. -/
def spatialSpan (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) : RatPoly :=
  finitePolySum (fun p => polySmul (c p) (characterPolynomial (plaquette width p).scalar 1)) qs

/-- Two chronological slices, with no rearrangement of any internal word. -/
def differenceSchedule (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    List (Q' × List (Nat × List FaceFactor)) :=
  qs.map (fun p => (c p, [(0, [(p, [(1, 1)])])])) ++
    qs.map (fun p => (-c p, [(1, [(p, [(1, 1)])])]))

/-- Support alone needs no physical-membership premise: the original source
plaquette definition already includes its literal identity fallback. -/
theorem spatialSpan_supported (width : Nat) (c : Z4Plaq → Q') :
    ∀ qs : List Z4Plaq, SupportedQuaternionBlocks (N width) (spatialSpan width c qs)
  | [] => fun _ ht => False.elim (List.not_mem_nil ht)
  | p :: qs => supported_add
      (supported_smul (SU2QuaternionRelativeHeatPairGeometry.character_supported
        (plaquette_supported width (N width) (Nat.le_refl _) p).scalar 1) (c p))
      (spatialSpan_supported width c qs)

theorem schedule_within (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    ∀ x, x ∈ differenceSchedule c qs → ∀ e, e ∈ x.2 → e.1 ≤ 1 := by
  intro x hx e he
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    have h := List.mem_singleton.mp he
    subst e
    exact Nat.zero_le _
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    have h := List.mem_singleton.mp he
    subst e
    exact Nat.le_refl _

theorem schedule_faces {width : Nat} (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    ∀ x, x ∈ differenceSchedule c qs → ∀ e, e ∈ x.2 →
      ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width := by
  intro x hx e he f hf
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have h := List.mem_singleton.mp he
    subst e
    have h := List.mem_singleton.mp hf
    subst f
    exact hqs p hp
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have h := List.mem_singleton.mp he
    subst e
    have h := List.mem_singleton.mp hf
    subst f
    exact hqs p hp

private theorem sum_congr {A : Type} (f g : A → RatPoly) :
    (xs : List A) → (∀ a, a ∈ xs → RatPolyCoeffEqv (f a) (g a)) →
      RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => RatPolyCoeffEqv.refl _
  | a :: xs, h => (h a List.mem_cons_self).add
      (sum_congr f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem singleton_product (C : Z4Plaq → Nat → RatPoly) (p : Z4Plaq) :
    RatPolyCoeffEqv (product C [(p, [(1, 1)])]) (C p 1) :=
  ((((RatPolyCoeffEqv.one_smul (C p 1)).add (RatPolyCoeffEqv.refl polyZero)).trans
    (RatPolyCoeffEqv.add_zero (C p 1))).mul (RatPolyCoeffEqv.refl polyOne)).trans
      (RatPolyCoeffEqv.mul_one _)

private theorem single_source (width offset : Nat) (p : Z4Plaq) :
    RatPolyCoeffEqv (windowProbe width [(offset, [(p, [(1, 1)])])])
      (liftBoundary (offset*(N width)) (characterPolynomial (plaquette width p).scalar 1)) :=
  ((lift_coeff (offset*(N width))
    (singleton_product (fun f spin => characterPolynomial (plaquette width f).scalar spin) p)).mul
      (RatPolyCoeffEqv.refl polyOne)).trans (RatPolyCoeffEqv.mul_one _)

private theorem single_placed (extent start offset : Nat) (p : Z4Plaq) :
    RatPolyCoeffEqv (sweptProduct extent 0
      (placeWindowProbes start [(offset, [(p, [(1, 1)])])]))
      (faceCharacter extent (timeShiftPlaquette (start+offset) p)) := by
  rw [swept_zero]
  exact singleton_product
    (fun f spin => characterPolynomial (correctedSlabPlaquettePolynomial extent f).scalar spin)
    (timeShiftPlaquette (start+offset) p)

private theorem lift_zero : ∀ n : Nat, liftBoundary n polyZero = polyZero
  | 0 => rfl
  | n+1 => by
      change liftHead (liftBoundary n polyZero) = polyZero
      rw [lift_zero n]
      rfl

private theorem lift_neg (n : Nat) (p : RatPoly) :
    liftBoundary n (polyNeg p) = polyNeg (liftBoundary n p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [liftBoundary, ih, liftBoundary]
      simp only [liftHead, polyNeg, List.map_map]
      rfl

private theorem lift_weighted_sum {A : Type} (n : Nat) (c : A → Q') (f : A → RatPoly) :
    ∀ xs : List A,
      liftBoundary n (finitePolySum (fun a => polySmul (c a) (f a)) xs) =
        finitePolySum (fun a => polySmul (c a) (liftBoundary n (f a))) xs
  | [] => lift_zero n
  | a :: xs => by
      simp only [finitePolySum, lift_add, lift_smul, lift_weighted_sum n c f xs]

private theorem source_slice (width offset : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    RatPolyCoeffEqv
      (sourceSpan width (qs.map (fun p => (c p, [(offset, [(p, [(1, 1)])])]))))
      (liftBoundary (offset*(N width)) (spatialSpan width c qs)) := by
  unfold sourceSpan spatialSpan
  rw [sum_map, lift_weighted_sum]
  exact sum_congr _ _ qs (fun p _ => (single_source width offset p).smul (c p))

private theorem neg_smul (a : Q') : ∀ p : RatPoly,
    RatPolyCoeffEqv (polySmul (-a) p) (polyNeg (polySmul a p))
  | [] => RatPolyCoeffEqv.refl _
  | t :: p => by
      intro weight
      change ((-a)*t.2)*weight t.1 + _ ≈ (-(a*t.2))*weight t.1 + _
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (Q'.neg_mul_eqv a t.2)) (neg_smul a p weight)

private theorem span_neg (width : Nat) (c : Z4Plaq → Q') : ∀ qs : List Z4Plaq,
    RatPolyCoeffEqv (spatialSpan width (fun p => -c p) qs)
      (polyNeg (spatialSpan width c qs))
  | [] => RatPolyCoeffEqv.refl _
  | p :: qs => by
      change RatPolyCoeffEqv (polyAdd _ _) (polyNeg (polyAdd _ _))
      rw [show ∀ a b : RatPoly, polyNeg (polyAdd a b) = polyAdd (polyNeg a) (polyNeg b)
        from fun a b => by simp only [polyNeg, polyAdd, List.map_append]]
      exact (neg_smul (c p) _).add (span_neg width c qs)

/-- The literal finite signed schedule is the original temporal jump, before
any Haar integration or square expansion. No physical guard is needed here. -/
theorem difference_source (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    RatPolyCoeffEqv (sourceSpan width (differenceSchedule c qs))
      (jump width (spatialSpan width c qs)) := by
  have h0 := source_slice width 0 c qs
  have h1 := source_slice width 1 (fun p => -c p) qs
  simp only [Nat.zero_mul, Nat.one_mul, liftBoundary] at h0 h1
  have hn := lift_coeff (N width) (span_neg width c qs)
  rw [lift_neg] at hn
  unfold sourceSpan differenceSchedule
  rw [sum_append]
  exact h0.add (h1.trans hn)

/-- The same signed schedule is the family theorem's actual placed source,
with lower and upper labels and coefficients supplied by the checked geometry.
No distinctness is needed for this algebraic identity. -/
theorem difference_placed {width : Nat} (extent n : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    RatPolyCoeffEqv (placedSpan extent n (differenceSchedule c qs))
      (BF4ExactSlabPlaquetteBoundaryDualFamily.sourceSpan extent (doubledCoeff n c)
        (doubledLabels n qs)) := by
  simp only [placedSpan, differenceSchedule,
    BF4ExactSlabPlaquetteBoundaryDualFamily.sourceSpan,
    BF4ExactSlabPlaquetteBoundaryDualPairing.faceSpan, doubledLabels,
    List.map_append, sum_append, sum_map]
  apply RatPolyCoeffEqv.add
  · apply sum_congr
    intro p hp
    rw [doubledCoeff_lower n c (hqs p hp)]
    simpa only [Nat.add_zero] using (single_placed extent n 0 p).smul (c p)
  · apply sum_congr
    intro p hp
    rw [doubledCoeff_upper n c (hqs p hp)]
    exact (single_placed extent n 1 p).smul (-c p)

#print axioms spatialSpan
#print axioms differenceSchedule
#print axioms spatialSpan_supported
#print axioms schedule_within
#print axioms schedule_faces
#print axioms difference_source
#print axioms difference_placed

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
