/-
# Collar-local source entropy payment in the ORIGINAL full action

The actual incident collar contains every face meeting a selected physical
link, including crossing faces. Its complement is independent of the literal
selected Haar slots. Only the collar is identity-normalized and charged an
entropy error; every detached original heat factor remains multiplicatively
in the background. The source may depend on selected and exterior variables.

The finite payment is derived from the existing original source theorem, not
assumed. The exact arbitrary-insertion pin rejoins it to the full original
action before any normalization by a partition. The local count is the
existing collar count, bounded by six times the number of supplied links.
No logarithmic limit, uniform source moment estimate, warmed-response pin,
H1, OS, physical gap, or continuum claim is made.
-/

import YMGap.Continuum.BF4ExactSlabOriginalSourceEntropyCoercivity
import YMGap.Continuum.BF4ExactSlabBlockNormalizer

namespace YMGap.Continuum.BF4ExactSlabCollarSourceEntropyCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.ClusterCount4DProgress (Z4Link)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.RingNormaliser (evalMono)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy (familyProject_smul_eval)
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
  (collar detached background fullWeight)
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
  (slots collarHeat insertedNormalizer full_inserted_marginal_pin)
open YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds
open YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor
  (productFloor productFloor_pos productFloor_le_eval_heatProduct)
open YMGap.Continuum.BF4ExactSlabOriginalHeatHaarOrder (faceScalar_box)
open YMGap.Continuum.SU2PointwiseHeatStrictFloor (finiteCutoff)
open YMGap.Continuum.QuaternionHaarFamilySourceConcentration
open YMGap.Continuum.RegularizedLogPolynomial (partialSum)
open YMGap.Continuum.RegularizedLogPolynomialLowerTangent (ell)
open YMGap.Continuum.RegularizedLogFiniteCoercivity (third)
open YMGap.Continuum.RegularizedLogFiniteProductCoercivity (selectedCount)
open YMGap.Continuum.SU2HeatJacobiOriginalCoercivity (coercivityCutoff)
open YMGap.Continuum.SU2HeatJacobiActiveFactorCount (activeFactorCount)
open YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarEntropyCoercivity
  (selectedFaceDefectPolynomial)
open YMGap.Continuum.BF4ExactSlabOriginalSourceEntropyCoercivity

local infix:50 " ≈ " => Q'.eqv

private theorem tc {a b c : Q'} (h : a ≈ b) (k : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ h k

private theorem weighted_eval (rho : Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum (evalMono rho) p = evalRatPoly rho p
  | [] => rfl
  | t::p => congrArg (fun z => t.2*evalMono rho t.1+z) (weighted_eval rho p)

private theorem eval_congr (rho : Nat → Q') {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    evalRatPoly rho p ≈ evalRatPoly rho q := by
  simpa only [weighted_eval] using h (evalMono rho)

private theorem mul_swap (a b c : Q') : a*(b*c) ≈ b*(a*c) :=
  tc (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))
    (tc (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b))
      (Q'.mul_assoc_eqv b a c))

/-- Collar-only normalization of an arbitrary full-action insertion. The
insertion is NOT required to be independent of the selected slots. -/
theorem normalized_full_insertion_pin {q : Q'} (hq0 : (0 : Q') < q)
    (K extent : Nat) (links : List Z4Link)
    (hlinks : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (p : RatPoly) (qs : Nat → UnitNorm) :
    normalizingFactor q hq0 K (collar extent links)*
        evalRatPoly (environment qs) (familyProject (slots extent links)
          (polyMul (fullWeight q K extent) p)) ≈
      evalRatPoly (environment qs) (background q K extent links)*
        evalRatPoly (environment qs) (familyProject (slots extent links)
          (polyMul (normalizedHeatProduct q hq0 K extent (collar extent links)) p)) := by
  let rho := environment qs
  let alpha := normalizingFactor q hq0 K (collar extent links)
  let A := collarHeat q K extent links
  have hf : evalRatPoly rho (familyProject (slots extent links)
        (polyMul (fullWeight q K extent) p)) ≈
      evalRatPoly rho (background q K extent links)*
        evalRatPoly rho (familyProject (slots extent links) (polyMul p A)) :=
    tc (eval_congr rho (familyProject_congr _ (RatPolyCoeffEqv.mul_comm _ _)))
      (tc (eval_congr rho (full_inserted_marginal_pin q K extent links hlinks p))
        (evalRatPoly_mul rho _ _))
  have hlocalPoly : RatPolyCoeffEqv
      (polyMul (normalizedHeatProduct q hq0 K extent (collar extent links)) p)
      (polySmul alpha (polyMul p A)) :=
    (RatPolyCoeffEqv.polyMul_smul_left alpha A p).trans
      ((RatPolyCoeffEqv.mul_comm A p).smul alpha)
  have hl : evalRatPoly rho (familyProject (slots extent links)
        (polyMul (normalizedHeatProduct q hq0 K extent (collar extent links)) p)) ≈
      alpha*evalRatPoly rho (familyProject (slots extent links) (polyMul p A)) :=
    tc (eval_congr rho (familyProject_congr _ hlocalPoly))
      (familyProject_smul_eval _ alpha (polyMul p A) rho)
  exact tc (Q'.mul_eqv_congr_left alpha _ _ hf)
    (tc (mul_swap alpha (evalRatPoly rho (background q K extent links)) _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hl)))

/-- Positivity of the retained ORIGINAL background is constructed from the
same finite-prefix floor. No background sign premise is supplied. -/
theorem background_nonnegative {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K extent : Nat) (links : List Z4Link) (hK : finiteCutoff q ≤ K+1)
    (qs : Nat → UnitNorm) :
    (0 : Q') ≤ evalRatPoly (environment qs) (background q K extent links) :=
  Q'.le_trans' _ _ _ (Q'.le_of_lt (productFloor_pos hq0 hq1 (detached extent links)))
    (productFloor_le_eval_heatProduct hq0 hq1 K extent (environment qs) hK
      (detached extent links) (fun id _ => faceScalar_box extent id qs))

/-- Raw full-action source defect, with paid faces selected ONLY from the
actual incident collar. Crossing action faces remain in the full weight. -/
def originalCollarSourceDefect (q : Q') (K extent : Nat) (links : List Z4Link)
    (selected : Nat → Bool) (g : RatPoly) (qs : Nat → UnitNorm) : Q' :=
  evalRatPoly (environment qs) (familyProject (slots extent links)
    (polyMul (polyMul (fullWeight q K extent) g)
      (selectedFaceDefectPolynomial extent selected (collar extent links))))

/-- Exact rejoin of the local source payment to the original complete action. -/
theorem normalized_full_source_pin {q : Q'} (hq0 : (0 : Q') < q)
    (K extent : Nat) (links : List Z4Link)
    (hlinks : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (selected : Nat → Bool) (g : RatPoly) (qs : Nat → UnitNorm) :
    normalizingFactor q hq0 K (collar extent links)*
        originalCollarSourceDefect q K extent links selected g qs ≈
      evalRatPoly (environment qs) (background q K extent links)*
        originalSourceDefect q hq0 K extent (collar extent links) (slots extent links) selected g qs := by
  let D := selectedFaceDefectPolynomial extent selected (collar extent links)
  have hleft := eval_congr (environment qs) (familyProject_congr (slots extent links)
    (RatPolyCoeffEqv.mul_assoc (fullWeight q K extent) g D))
  have hright := eval_congr (environment qs) (familyProject_congr (slots extent links)
    (RatPolyCoeffEqv.mul_assoc
      (normalizedHeatProduct q hq0 K extent (collar extent links)) g D).symm)
  exact tc (Q'.mul_eqv_congr_left _ _ _ hleft)
    (tc (normalized_full_insertion_pin hq0 K extent links hlinks (polyMul g D) qs)
      (Q'.mul_eqv_congr_left _ _ _ hright))

/-- Full ORIGINAL action payment with retained local source entropy credit.
Only length(collar), not the detached action count, occurs in the error. -/
theorem original_collar_source_entropy_payment {q : Q'}
    (hq0 : (0 : Q') < q) (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (K extent : Nat) (links : List Z4Link)
    (hlinks : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (selected : Nat → Bool) (g : RatPoly)
    (hg : ∀ heads : Nat → UnitNorm,
      (0 : Q') ≤ evalRatPoly (environment heads) g ∧ evalRatPoly (environment heads) g ≤ 1)
    (qs : Nat → UnitNorm) (hK : coercivityCutoff q ≤ K+1) (N : Nat) (hN : 1 ≤ N) :
    normalizingFactor q hq0 K (collar extent links)*
        originalCollarSourceDefect q K extent links selected g qs ≤
      evalRatPoly (environment qs) (background q K extent links)*
        ((256*(1-q))*(
          partialSum (sourceMass (slots extent links)
            (normalizedHeatProduct q hq0 K extent (collar extent links)) g qs) N-
          sourceEntropy (slots extent links)
            (normalizedHeatProduct q hq0 K extent (collar extent links)) g qs N+
          ((3*partialSum third N)*Q'.ofNat (selectedCount selected (collar extent links))*
              sourceMass (slots extent links)
                (normalizedHeatProduct q hq0 K extent (collar extent links)) g qs+
            (Q'.ofNat (collar extent links).length+3*Q'.ofNat (activeFactorCount q-1)*
              Q'.ofNat (selectedCount selected (collar extent links))+1)*Q'.invSucc N))) := by
  have hKf : finiteCutoff q ≤ K+1 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hK
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (normalized_full_source_pin hq0 K extent links hlinks selected g qs))
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (original_source_entropy_payment hq0 hq hq1 K extent
        (collar extent links) (slots extent links) selected g hg qs hK N hN)
      (background_nonnegative hq0 hq1 K extent links hKf qs))

/-- Computed local biased moments pay the source credit, while the entire
detached original background stays multiplicative. Source positivity is only
required for its OWN local moment quotient. No source independence is assumed. -/
theorem original_collar_source_moment_payment {q : Q'}
    (hq0 : (0 : Q') < q) (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (K extent : Nat) (links : List Z4Link)
    (hlinks : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (selected : Nat → Bool) (g : RatPoly)
    (hg : ∀ heads : Nat → UnitNorm,
      (0 : Q') ≤ evalRatPoly (environment heads) g ∧ evalRatPoly (environment heads) g ≤ 1)
    (qs : Nat → UnitNorm) (hK : coercivityCutoff q ≤ K+1)
    (ha : (0 : Q') < sourceMass (slots extent links)
      (normalizedHeatProduct q hq0 K extent (collar extent links)) g qs)
    (N : Nat) (hN : 1 ≤ N) :
    normalizingFactor q hq0 K (collar extent links)*
        originalCollarSourceDefect q K extent links selected g qs ≤
      evalRatPoly (environment qs) (background q K extent links)*
        ((256*(1-q))*(
          partialSum (sourceMass (slots extent links)
            (normalizedHeatProduct q hq0 K extent (collar extent links)) g qs) N-
          sourceMass (slots extent links)
            (normalizedHeatProduct q hq0 K extent (collar extent links)) g qs*
            ell (sourceMean (slots extent links)
              (normalizedHeatProduct q hq0 K extent (collar extent links)) g qs ha) N+
          ((3*partialSum third N)*Q'.ofNat (selectedCount selected (collar extent links))*
              sourceMass (slots extent links)
                (normalizedHeatProduct q hq0 K extent (collar extent links)) g qs+
            (Q'.ofNat (collar extent links).length+3*Q'.ofNat (activeFactorCount q-1)*
              Q'.ofNat (selectedCount selected (collar extent links))+1)*Q'.invSucc N))) := by
  have hKf : finiteCutoff q ≤ K+1 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hK
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (normalized_full_source_pin hq0 K extent links hlinks selected g qs))
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (original_source_moment_payment hq0 hq hq1 K extent
        (collar extent links) (slots extent links) selected g hg qs hK ha N hN)
      (background_nonnegative hq0 hq1 K extent links hKf qs))

end YMGap.Continuum.BF4ExactSlabCollarSourceEntropyCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabCollarSourceEntropyCoercivity.normalized_full_insertion_pin
#print axioms YMGap.Continuum.BF4ExactSlabCollarSourceEntropyCoercivity.background_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabCollarSourceEntropyCoercivity.originalCollarSourceDefect
#print axioms YMGap.Continuum.BF4ExactSlabCollarSourceEntropyCoercivity.normalized_full_source_pin
#print axioms YMGap.Continuum.BF4ExactSlabCollarSourceEntropyCoercivity.original_collar_source_entropy_payment
#print axioms YMGap.Continuum.BF4ExactSlabCollarSourceEntropyCoercivity.original_collar_source_moment_payment
