/-
# Quantitative density of the actual centered physical image

For every supplied Cauchy representative of a vector orthogonal to the
constructed sector vacuum, center its finite cube approximants using the
EXISTING moving-head centering. Their errors in the SAME completed reflected
form have an explicit rate. The fixed constants are computed from the vacuum
and root representatives; no representatives are chosen from quotient points.

Scope: w=1/400, extent one, full reflected vacuum complement. No strict gap,
geometric-time identification, varying-coupling uniformity or continuum claim.
-/

import YMGap.Continuum.BF4PhysicalCubeCenteringControl
import YMGap.Continuum.ScaledGNSCompletionEstimates

namespace YMGap.Continuum.BF4PhysicalCubeCenteredDensity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ScaledGNSCompletion
open YMGap.Continuum.ScaledGNSCompletionEstimates
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeSectorVacuum
open YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm
open YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage
open YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalCubeCenteringPairing
open YMGap.Continuum.BF4PhysicalCubeCenteringControl
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "j" => cubeReflectedEmbed
local notation "B" => cubeReflectedInner
local notation "Omega" => reflectedSectorVacuum
private abbrev Rq (q : Q') : RC := Quotient.mk CReal.crealSetoid (CReal.ofQ' q)

private theorem rq_nonnegative {q : Q'} (hq : (0 : Q') ≤ q) : RCnonneg (Rq q) :=
  CReal.leEv_of_le (CReal.ofQ'_le_ofQ' hq)

private theorem rq_mul (a b : Q') : RCmul (Rq a) (Rq b) = Rq (a * b) := rfl

private theorem rq_eqv {a b : Q'} (h : Q'.eqv a b) : Rq a = Rq b :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => h))

private theorem mul_assoc (a b c : RC) :
    RCmul (RCmul a b) c = RCmul a (RCmul b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro repA repB repC
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_assoc_eqv _ _ _))

private theorem sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro repA
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-(0 : Q')) 0))
    (Q'.eqv_of_eq (Q'.add_zero' _))

private theorem cancel_q (q : Q') (hq : (0 : Q') < q) (a b : RC)
    (h : RCle (RCmul (Rq q) a) (RCmul (Rq q) b)) : RCle a b := by
  rw [RCmul_comm (Rq q) a, RCmul_comm (Rq q) b] at h
  refine Quotient.inductionOn₂ a b ?_ h
  intro repA repB hab
  exact RCBilinearDifference.cancel_positive_factor q hq (fun _ => Q'.le_refl' _) hab

def vacuumRepresentative : CauchyGNS D :=
  toRawCauchy D anchorNormalization (sectorCauchyToReflected sectorVacuumCauchy)

theorem vacuumRepresentative_realizes :
    rawToReflected (Quotient.mk (cauchySetoid D) vacuumRepresentative) = Omega :=
  reflected_raw_inverse Omega

/-- These bounds are data from two fixed representatives, not from the input. -/
def vacuumCeiling : Q' := Q'.ofNat ((D).normCeil vacuumRepresentative)

def rootCeiling : Q' := Q'.ofNat ((D).normCeil (constCauchy D rootVector))

private theorem normCeil_pos (data : GNSData) (rep : CauchyGNS data) :
    (0 : Q') < Q'.ofNat (data.normCeil rep) := Q'.ofNat_succ_pos _

theorem vacuumCeiling_pos : (0 : Q') < vacuumCeiling := normCeil_pos D vacuumRepresentative

theorem rootCeiling_pos : (0 : Q') < rootCeiling := normCeil_pos D (constCauchy D rootVector)

theorem vacuum_norm_bound : RCle (B Omega Omega) (Rq vacuumCeiling) := by
  rw [← vacuumRepresentative_realizes]
  exact scaledInner_normCeil D anchorNormalization vacuumRepresentative

theorem root_norm_bound : RCle (B (j rootVector) (j rootVector)) (Rq rootCeiling) := by
  have h := scaledInner_normCeil D anchorNormalization (constCauchy D rootVector)
  change RCle (scaledCompletedInner D anchorNormalization
    (toScaledCompletion D anchorNormalization (embedV D rootVector))
    (toScaledCompletion D anchorNormalization (embedV D rootVector))) (Rq rootCeiling) at h
  rw [toScaledCompletion_embed] at h
  exact h

def centeringFactor : Q' := Q'.divPos (vacuumCeiling * rootCeiling)
  (denominatorFloor * denominatorFloor) (Q'.mul_pos denominatorFloor_pos denominatorFloor_pos)

theorem centeringFactor_pos : (0 : Q') < centeringFactor :=
  Q'.divPos_pos _ _ _ (Q'.mul_pos vacuumCeiling_pos rootCeiling_pos)

theorem centeringFactor_exact :
    Q'.eqv ((denominatorFloor * denominatorFloor) * centeringFactor) (vacuumCeiling * rootCeiling) :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv _ _ _)

def errorSq (x y : CubeReflectedCompletion) : RC := B (cubeReflectedSub x y) (cubeReflectedSub x y)

private theorem mean_error (x : CubeSectorVacuumComplement) (p : SectorPresentation) :
    B Omega (j (presentationToCube p)) = B Omega (cubeReflectedSub (j (presentationToCube p)) x.val) := by
  rw [cubeReflectedInner_symm Omega (cubeReflectedSub _ _), cubeReflectedInner_sub_left,
    cubeReflectedInner_symm (j (presentationToCube p)) Omega,
    cubeReflectedInner_symm x.val Omega, x.property, sub_zero]

private theorem mean_square_error_bound (x : CubeSectorVacuumComplement) (p : SectorPresentation) :
    RCle (RCmul (B Omega (j (presentationToCube p))) (B Omega (j (presentationToCube p))))
      (RCmul (Rq vacuumCeiling) (errorSq (j (presentationToCube p)) x.val)) := by
  rw [mean_error x p]
  exact RCle_trans (scaledInner_cauchySchwarz D anchorNormalization Omega _)
    (mul_mono_right (scaledInner_nonnegative D anchorNormalization _) vacuum_norm_bound)

/-- The centering cost is bounded in the actual E norm, uniformly in the
presentation base and the target vector in the FULL vacuum complement. -/
theorem centeringResidual_error_bound (x : CubeSectorVacuumComplement) (p : SectorPresentation) :
    RCle (B (centeringResidual p) (centeringResidual p))
      (RCmul (Rq centeringFactor) (errorSq (j (presentationToCube p)) x.val)) := by
  apply cancel_q (denominatorFloor * denominatorFloor)
    (Q'.mul_pos denominatorFloor_pos denominatorFloor_pos)
  rw [← mul_assoc, rq_mul, rq_eqv centeringFactor_exact]
  have hroot := mul_mono_left (square_nonnegative (B Omega (j (presentationToCube p)))) root_norm_bound
  have hmean := mul_mono_right (rq_nonnegative (Q'.le_of_lt rootCeiling_pos))
    (mean_square_error_bound x p)
  have h := RCle_trans (centeringResidual_mean_bound p) (RCle_trans hroot hmean)
  rw [mul_assoc, RCmul_comm (errorSq _ _) (Rq rootCeiling), ← mul_assoc, rq_mul] at h
  exact h

/-- The quadratic triangle inequality costs two copies of each error. -/
def approximationFactor : Q' := (centeringFactor + centeringFactor) + ((1 : Q') + 1)

theorem approximationFactor_pos : (0 : Q') < approximationFactor :=
  Q'.add_pos (Q'.add_pos centeringFactor_pos centeringFactor_pos) (by decide)

private theorem double_error (a : Q') (e : RC) :
    RCadd (RCadd (RCmul (Rq a) e) (RCmul (Rq a) e)) (RCadd e e) =
      RCmul (Rq ((a + a) + ((1 : Q') + 1))) e := by
  refine Quotient.inductionOn e ?_
  intro repE
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_symm (Q'.one_mul_eqv _)) (Q'.eqv_symm (Q'.one_mul_eqv _)))
        (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))))
    (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))

/-- Centering an approximant to ANY vacuum-orthogonal target preserves its
error up to this single fixed, computed factor. -/
theorem centered_error_bound (x : CubeSectorVacuumComplement) (p : SectorPresentation) :
    RCle (errorSq (centeredCubeVector p.base p.coefficient).val x.val)
      (RCmul (Rq approximationFactor) (errorSq (j (presentationToCube p)) x.val)) := by
  have htriangle := scaledInner_triangle D anchorNormalization
    (centeredCubeVector p.base p.coefficient).val (j (presentationToCube p)) x.val
  have hres := centeringResidual_error_bound x p
  have h := RCle_trans htriangle (RCadd_le_add (RCadd_le_add hres hres)
    (RCle_refl (RCadd (errorSq (j (presentationToCube p)) x.val)
      (errorSq (j (presentationToCube p)) x.val))))
  rw [double_error] at h
  exact h

/-- Input squared-error tolerance, given as rational data. -/
def approximationTolerance (epsilon : Q') : Q' :=
  Q'.divPos epsilon approximationFactor approximationFactor_pos

theorem approximationTolerance_pos {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < approximationTolerance epsilon := Q'.divPos_pos _ _ _ hepsilon

theorem approximationTolerance_exact (epsilon : Q') :
    Q'.eqv (approximationFactor * approximationTolerance epsilon) epsilon :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv _ _ _)

def approximationPresentation (X : CauchyGNS D) (n : Nat) : SectorPresentation :=
  spanPresentation (X.seq n)

def approximationVector (X : CauchyGNS D) (n : Nat) : CubeSectorVacuumComplement :=
  centeredCubeVector (approximationPresentation X n).base (approximationPresentation X n).coefficient

/-- The existing centering also supplies each approximant's Cauchy data. -/
def approximationRepresentative (X : CauchyGNS D) (n : Nat) : cubeReflectedSeminorm.Cauchy :=
  centeredCauchy (approximationPresentation X n)

theorem approximationRepresentative_realizes (X : CauchyGNS D) (n : Nat) :
    Quotient.mk cubeReflectedSeminorm.completionSetoid (approximationRepresentative X n) =
      (approximationVector X n).val := rfl

def approximationRate (X : CauchyGNS D) (epsilon : Q') : Nat :=
  X.modulus (approximationTolerance epsilon)

private theorem approximationPresentation_realizes (X : CauchyGNS D) (n : Nat) :
    j (presentationToCube (approximationPresentation X n)) = j (X.seq n) :=
  spanPresentation_reflected (X.seq n)

/-- Explicit density rate in the SAME completed reflected norm. A supplied
representative is input data, never chosen from the quotient by an axiom. -/
theorem approximation_bound (x : CubeSectorVacuumComplement) (X : CauchyGNS D)
    (hX : rawToReflected (Quotient.mk (cauchySetoid D) X) = x.val)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (n : Nat) (hn : approximationRate X epsilon ≤ n) :
    RCle (errorSq (approximationVector X n).val x.val) (Rq epsilon) := by
  have hinput := scaledInner_approximation D anchorNormalization X
    (approximationTolerance epsilon) (approximationTolerance_pos hepsilon) n hn
  change RCle (errorSq (j (X.seq n)) (rawToReflected (Quotient.mk (cauchySetoid D) X)))
    (Rq (approximationTolerance epsilon)) at hinput
  rw [hX] at hinput
  have hcenter := centered_error_bound x (approximationPresentation X n)
  rw [approximationPresentation_realizes] at hcenter
  have h := mul_mono_left (rq_nonnegative (Q'.le_of_lt approximationFactor_pos)) hinput
  rw [rq_mul, rq_eqv (approximationTolerance_exact epsilon)] at h
  exact RCle_trans hcenter h

/-- Witness-bearing approximation of a target in the full complement. The
finite presentations determine the already constructed centered Cauchy vectors. -/
structure CenteredApproximation (x : CubeSectorVacuumComplement) where
  presentation : Nat → SectorPresentation
  modulus : Q' → Nat
  bound : ∀ epsilon, (0 : Q') < epsilon → ∀ n, modulus epsilon ≤ n →
    RCle (errorSq (centeredCubeVector (presentation n).base (presentation n).coefficient).val x.val)
      (Rq epsilon)

/-- No smaller source subtype is assumed: the only target property is its
orthogonality to the actual stationary sector vacuum. -/
def centeredDensity (x : CubeSectorVacuumComplement) (X : CauchyGNS D)
    (hX : rawToReflected (Quotient.mk (cauchySetoid D) X) = x.val) : CenteredApproximation x where
  presentation := approximationPresentation X
  modulus := approximationRate X
  bound := approximation_bound x X hX

end YMGap.Continuum.BF4PhysicalCubeCenteredDensity

#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.vacuumRepresentative
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.vacuumRepresentative_realizes
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.vacuumCeiling
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.rootCeiling
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.vacuumCeiling_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.rootCeiling_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.vacuum_norm_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.root_norm_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.centeringFactor
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.centeringFactor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.centeringFactor_exact
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.errorSq
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.centeringResidual_error_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.approximationFactor
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.approximationFactor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.centered_error_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.approximationTolerance
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.approximationTolerance_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.approximationTolerance_exact
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.approximationPresentation
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.approximationVector
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.approximationRepresentative
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.approximationRepresentative_realizes
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.approximationRate
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.approximation_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.CenteredApproximation
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredDensity.centeredDensity
