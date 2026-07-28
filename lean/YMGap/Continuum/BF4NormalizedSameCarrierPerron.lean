/-
# Vacuum-removed BF4 same-carrier HS convergence and Perron identification

A normalized Markov transfer has the constant vacuum eigenvector with
eigenvalue one.  Therefore an absolute Rayleigh bound by `1/4` cannot hold
on the raw normalized matrix.  The nonlinear/Mehler comparison must be made
after removing the same vacuum projector from both operators (or,
equivalently, on the mean-zero carrier).

This file builds that missing analytic layer constructively:

* the exact uniform vacuum projector on every successor-size rational
  function-space carrier;
* its unit row mass and its annihilation of mean-zero vectors;
* transport of raw mean-zero eigenmodes to the vacuum-removed matrix;
* a cutoff-indexed, same-carrier nonlinear/Mehler HS convergence datum;
* eventual specialization of that convergence to the proved `7/100`
  BF4 perturbation theorem; and
* a genuine Perron identification retaining both an eigenmode and a proof
  that it dominates every other nonnegative eigenmode.

The last section specializes the construction to a literal square section
of the matched BF4 physical kernel.  Row normalization of that square
section, the Mehler entries, HS convergence, and Perron dominance remain
mathematical obligations; none is replaced by the scalar Haar square.

## Axiom gate

Finite rational sums and intuitionistic quantifiers only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4MatchedPhysicalKernelBridge

namespace YMGap.Continuum.BF4NormalizedSameCarrierPerron

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4GaussianPerronRatio
open YMGap.Continuum.BF4MatchedPhysicalKernelBridge
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FiniteCarrierHSPerronPerturbation

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact uniform vacuum removal -/

/-- Sum of the coordinates displayed by a finite rational vector. -/
def vectorSum (vector : RationalVector) (N : Nat) : Q' :=
  fsum vector N

/-- Mean-zero condition on a successor-size carrier. -/
def UniformMeanZero
    (vector : RationalVector) (predecessor : Nat) : Prop :=
  vectorSum vector (predecessor + 1) ≈ 0

/-- The rank-one uniform vacuum projector on a carrier of size `N+1`.
Every displayed entry is exactly `1/(N+1)`. -/
def uniformVacuumProjector (predecessor : Nat) : RationalMatrix :=
  fun _row _column => Q'.invSucc predecessor

/-- Remove the uniform constant mode from a matrix on the same carrier. -/
def vacuumRemovedMatrix
    (matrix : RationalMatrix) (predecessor : Nat) : RationalMatrix :=
  matrixDifference matrix (uniformVacuumProjector predecessor)

/-- `Σ_{i<N} c = N*c`, stated in the project's rational equivalence. -/
private theorem fsum_const
    (constant : Q') :
    ∀ N : Nat,
      fsum (fun _ => constant) N ≈
        Q'.ofNat N * constant
  | 0 => by
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (Q'.ofNat 0) 0 constant
            Q'.ofNat_zero_eqv)
          (Q'.zero_mul_eqv constant))
  | N + 1 => by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ constant
          (fsum_const constant N)) ?_
      refine Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (Q'.ofNat (N + 1))
            (Q'.ofNat N + Q'.ofNat 1)
            constant
            (Q'.ofNat_add_eqv N 1)) ?_)
      refine Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv
          (Q'.ofNat N) (Q'.ofNat 1) constant) ?_
      exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (Q'.ofNat 1) 1 constant
            (by decide))
          (Q'.one_mul_eqv constant))

/-- Every row of the uniform projector has exact mass one. -/
theorem uniformVacuumProjector_row_normalized
    (predecessor row : Nat) :
    fsum
        (uniformVacuumProjector predecessor row)
        (predecessor + 1) ≈
      1 := by
  exact Q'.eqv_trans _ _ _
    (fsum_const (Q'.invSucc predecessor) (predecessor + 1))
    (Q'.ofNat_succ_mul_invSucc predecessor)

/-- The projector maps every row to the uniform coordinate mean. -/
theorem uniformVacuumProjector_rowApply
    (vector : RationalVector) (predecessor row : Nat) :
    rowApply
        (uniformVacuumProjector predecessor)
        vector (predecessor + 1) row ≈
      Q'.invSucc predecessor *
        vectorSum vector (predecessor + 1) := by
  unfold rowApply uniformVacuumProjector vectorSum
  exact Q'.eqv_symm
    (fsum_const_mul
      (Q'.invSucc predecessor) vector (predecessor + 1))

/-- Hence the vacuum projector vanishes on the mean-zero carrier. -/
theorem uniformVacuumProjector_annihilates_meanZero
    (vector : RationalVector) (predecessor row : Nat)
    (hmean : UniformMeanZero vector predecessor) :
    rowApply
        (uniformVacuumProjector predecessor)
        vector (predecessor + 1) row ≈
      0 := by
  exact Q'.eqv_trans _ _ _
    (uniformVacuumProjector_rowApply vector predecessor row)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        (Q'.invSucc predecessor)
        (vectorSum vector (predecessor + 1)) 0 hmean)
      (Q'.mul_zero_eqv (Q'.invSucc predecessor)))

/-- A raw eigenmode together with its exact mean-zero certificate. -/
structure MeanZeroFiniteCarrierEigenmode
    (matrix : RationalMatrix) (predecessor : Nat) : Type where
  mode : FiniteCarrierEigenmode matrix (predecessor + 1)
  mean_zero : UniformMeanZero mode.vector predecessor

/-- Vacuum removal leaves every mean-zero eigenmode unchanged. -/
def MeanZeroFiniteCarrierEigenmode.toVacuumRemoved
    {matrix : RationalMatrix} {predecessor : Nat}
    (mode :
      MeanZeroFiniteCarrierEigenmode matrix predecessor) :
    FiniteCarrierEigenmode
      (vacuumRemovedMatrix matrix predecessor)
      (predecessor + 1) where
  ratio := mode.mode.ratio
  vector := mode.mode.vector
  ratio_nonnegative := mode.mode.ratio_nonnegative
  vectorNorm_pos := mode.mode.vectorNorm_pos
  eigen_equation := by
    intro row hrow
    have hdecompose :=
      rowApply_difference
        matrix (uniformVacuumProjector predecessor)
        mode.mode.vector (predecessor + 1) row
    have hprojector :=
      uniformVacuumProjector_annihilates_meanZero
        mode.mode.vector predecessor row mode.mean_zero
    have hrawCentered :
        rowApply matrix mode.mode.vector (predecessor + 1) row ≈
          rowApply
            (vacuumRemovedMatrix matrix predecessor)
            mode.mode.vector (predecessor + 1) row := by
      exact Q'.eqv_trans _ _ _ hdecompose
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right
            (rowApply
              (uniformVacuumProjector predecessor)
              mode.mode.vector (predecessor + 1) row)
            0
            (rowApply
              (vacuumRemovedMatrix matrix predecessor)
              mode.mode.vector (predecessor + 1) row)
            hprojector)
          (QPoly.q_zero_add_eqv
            (rowApply
              (vacuumRemovedMatrix matrix predecessor)
              mode.mode.vector (predecessor + 1) row)))
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm hrawCentered)
      (mode.mode.eigen_equation row hrow)

/-! ## 2. Normalized same-carrier nonlinear/Mehler convergence -/

/-- Exact row normalization on a successor-size rational carrier. -/
structure UniformNormalizedMatrix
    (matrix : RationalMatrix) (predecessor : Nat) : Prop where
  row_normalized :
    ∀ row, row < predecessor + 1 →
      fsum (matrix row) (predecessor + 1) ≈ 1
  symmetric :
    ∀ row, row < predecessor + 1 →
      ∀ column, column < predecessor + 1 →
        matrix row column ≈ matrix column row

/-- A cutoff-indexed nonlinear/Mehler pair on one common carrier at each
cutoff, compared only after removal of their common uniform vacuum.

`hs_error` is the genuine Hilbert--Schmidt convergence estimate.  Its
carrier size may grow with the cutoff. -/
structure NormalizedSameCarrierMehlerHSConvergence : Type where
  predecessor : Nat → Nat
  nonlinear : Nat → RationalMatrix
  mehler : Nat → RationalMatrix
  approximation : Nat → Nat
  nonlinear_normalized :
    ∀ cutoff,
      UniformNormalizedMatrix
        (nonlinear cutoff) (predecessor cutoff)
  mehler_normalized :
    ∀ cutoff,
      UniformNormalizedMatrix
        (mehler cutoff) (predecessor cutoff)
  mehler_quadratic :
    ∀ cutoff vector,
      Q'.abs
          (matrixQuadratic
            (vacuumRemovedMatrix
              (mehler cutoff) (predecessor cutoff))
            vector (predecessor cutoff + 1)) ≤
        gaussianPerronRatio.approx (approximation cutoff) *
          vectorNormSq vector (predecessor cutoff + 1)
  epsilon : Nat → Q'
  epsilon_nonnegative :
    ∀ cutoff, (0 : Q') ≤ epsilon cutoff
  hs_error :
    ∀ cutoff,
      matrixHSSq
          (matrixDifference
            (vacuumRemovedMatrix
              (nonlinear cutoff) (predecessor cutoff))
            (vacuumRemovedMatrix
              (mehler cutoff) (predecessor cutoff)))
          (predecessor cutoff + 1) ≤
        epsilon cutoff * epsilon cutoff
  epsilon_tends_zero :
    ∀ tolerance : Q', (0 : Q') < tolerance →
      { threshold : Nat //
        ∀ cutoff, threshold ≤ cutoff →
          epsilon cutoff ≤ tolerance }

namespace NormalizedSameCarrierMehlerHSConvergence

variable (convergence : NormalizedSameCarrierMehlerHSConvergence)

/-- Eventually the constructive HS convergence lies inside the exact
`7/100` BF4 buffer. -/
def eventually_sevenHundredths :
    { threshold : Nat //
      ∀ cutoff, threshold ≤ cutoff →
        convergence.epsilon cutoff ≤ sevenHundredths } :=
  convergence.epsilon_tends_zero
    sevenHundredths (by decide)

/-- At every sufficiently large cutoff, the normalized, vacuum-removed
nonlinear/Mehler pair instantiates the already-proved BF4 finite-carrier HS
perturbation theorem. -/
def bufferedPerturbation
    (threshold cutoff : Nat)
    (hbuffer :
      ∀ index, threshold ≤ index →
        convergence.epsilon index ≤ sevenHundredths)
    (hcutoff : threshold ≤ cutoff) :
    BF4BufferedFiniteCarrierHSPerturbation
      (vacuumRemovedMatrix
        (convergence.nonlinear cutoff)
        (convergence.predecessor cutoff))
      (vacuumRemovedMatrix
        (convergence.mehler cutoff)
        (convergence.predecessor cutoff))
      (convergence.predecessor cutoff + 1)
      (convergence.approximation cutoff) where
  gaussianRate_nonnegative :=
    Q'.le_trans' _ _ _
      (by decide : (0 : Q') ≤ oneTwentieth)
      (oneTwentieth_le_ratio_approx
        (convergence.approximation cutoff))
  epsilon_pos := by decide
  gaussian_quadratic :=
    convergence.mehler_quadratic cutoff
  nonlinear_gaussian_hs := by
    have hepsilon0 :=
      convergence.epsilon_nonnegative cutoff
    have hbuffer0 :
        (0 : Q') ≤ sevenHundredths := by decide
    have hfirst :
        convergence.epsilon cutoff *
            convergence.epsilon cutoff ≤
          convergence.epsilon cutoff *
            sevenHundredths :=
      Q'.mul_le_mul_of_nonneg_left
        (convergence.epsilon cutoff)
        sevenHundredths
        (convergence.epsilon cutoff)
        (hbuffer cutoff hcutoff) hepsilon0
    have hsecond :
        convergence.epsilon cutoff *
            sevenHundredths ≤
          sevenHundredths * sevenHundredths :=
      Q'.mul_le_mul_of_nonneg_right
        (convergence.epsilon cutoff)
        sevenHundredths
        sevenHundredths
        (hbuffer cutoff hcutoff) hbuffer0
    exact Q'.le_trans' _ _ _
      (convergence.hs_error cutoff)
      (Q'.le_trans' _ _ _ hfirst hsecond)

/-! ## 3. Genuine finite Perron identification -/

/-- A genuine finite Perron identification on the vacuum-removed carrier.
Unlike a free scalar `qS`, this retains an actual nonzero eigenmode and a
proof that its ratio dominates every other nonnegative eigenmode. -/
structure PerronIdentification
    (matrix : RationalMatrix) (N : Nat) : Type where
  perronMode : FiniteCarrierEigenmode matrix N
  dominates :
    ∀ mode : FiniteCarrierEigenmode matrix N,
      mode.ratio ≤ perronMode.ratio

namespace PerronIdentification

variable {matrix : RationalMatrix} {N : Nat}
    (identification : PerronIdentification matrix N)

def qS : Q' :=
  identification.perronMode.ratio

theorem qS_nonnegative :
    (0 : Q') ≤ identification.qS :=
  identification.perronMode.ratio_nonnegative

end PerronIdentification

/-- **Eventually normalized nonlinear BF4 Perron ratio `≤ 1/4`.**

The conclusion is about the actual dominant eigenmode retained by the
Perron identification, and the comparison is between the nonlinear and
Mehler operators on exactly the same vacuum-removed carrier. -/
theorem perronRatio_le_quarter
    (threshold cutoff : Nat)
    (hbuffer :
      ∀ index, threshold ≤ index →
        convergence.epsilon index ≤ sevenHundredths)
    (hcutoff : threshold ≤ cutoff)
    (identification :
      PerronIdentification
        (vacuumRemovedMatrix
          (convergence.nonlinear cutoff)
          (convergence.predecessor cutoff))
        (convergence.predecessor cutoff + 1)) :
    identification.qS ≤ oneQuarter := by
  exact bf4_nonlinear_eigenmode_ratio_le_quarter
    (convergence.bufferedPerturbation
      threshold cutoff hbuffer hcutoff)
    identification.perronMode

/-- Computational packaging of the eventual quarter theorem: the threshold
is retained in `Type`, and no proof-erased existential or excluded-middle
choice is used. -/
def eventually_perronRatio_le_quarter :
    { threshold : Nat //
      ∀ cutoff, threshold ≤ cutoff →
        ∀ identification :
          PerronIdentification
            (vacuumRemovedMatrix
              (convergence.nonlinear cutoff)
              (convergence.predecessor cutoff))
            (convergence.predecessor cutoff + 1),
          identification.qS ≤ oneQuarter } := by
  obtain ⟨threshold, hthreshold⟩ :=
    convergence.eventually_sevenHundredths
  exact ⟨threshold, fun cutoff hcutoff identification =>
    convergence.perronRatio_le_quarter
      threshold cutoff hthreshold hcutoff identification⟩

end NormalizedSameCarrierMehlerHSConvergence

/-! ## 4. Literal matched-BF4 fixed-scale specialization -/

/-- A common matched physical square section whose selected rows retain
their full unit mass.  This is strictly stronger than the existing
rectangular-kernel row normalization: it certifies that the chosen common
target list is a complete row carrier. -/
structure MatchedUniformNormalizedSameCarrier
    {family :
      BF4MatchedPhysicalAFBridge.MatchedBlockFamily}
    {g : Q'} : Type 1 where
  carrierData : MatchedSameCarrierSection family g
  row_normalized :
    ∀ row, row < carrierData.carrierSize →
      fsum (carrierData.rationalMatrix row)
        carrierData.carrierSize ≈ 1
  symmetric :
    ∀ row, row < carrierData.carrierSize →
      ∀ column, column < carrierData.carrierSize →
        carrierData.rationalMatrix row column ≈
          carrierData.rationalMatrix column row

namespace MatchedUniformNormalizedSameCarrier

variable
    {family :
      BF4MatchedPhysicalAFBridge.MatchedBlockFamily}
    {g : Q'}
    (physical : MatchedUniformNormalizedSameCarrier
      (family := family) (g := g))

/-- The predecessor of the definitionally nonempty physical carrier. -/
def predecessor : Nat :=
  physical.carrierData.tail.length

theorem carrierSize_eq :
    physical.carrierData.carrierSize =
      physical.predecessor + 1 := by
  unfold MatchedSameCarrierSection.carrierSize
    MatchedSameCarrierSection.states predecessor
  simp

/-- The exact matched BF4 square matrix with its uniform vacuum removed. -/
def centeredPhysicalMatrix : RationalMatrix :=
  vacuumRemovedMatrix
    physical.carrierData.rationalMatrix physical.predecessor

/-- The raw matched physical matrix is normalized on its literal common
carrier, now expressed in successor-size form. -/
def normalizedMatrix :
    UniformNormalizedMatrix
      physical.carrierData.rationalMatrix physical.predecessor where
  row_normalized := by
    intro row hrow
    rw [← physical.carrierSize_eq] at hrow ⊢
    exact physical.row_normalized row hrow
  symmetric := by
    intro row hrow column hcolumn
    rw [← physical.carrierSize_eq] at hrow hcolumn
    exact physical.symmetric row hrow column hcolumn

end MatchedUniformNormalizedSameCarrier

/-- Fixed-scale normalized nonlinear/Mehler comparison on a literal matched
BF4 carrier.  The HS theorem consumes the centered matrices, so the unit
vacuum is not incorrectly bounded by `1/4`. -/
structure MatchedCenteredMehlerComparison
    {family :
      BF4MatchedPhysicalAFBridge.MatchedBlockFamily}
    {g : Q'}
    (physical :
      MatchedUniformNormalizedSameCarrier
        (family := family) (g := g))
    (approximation : Nat) : Type 1 where
  mehler : RationalMatrix
  mehler_normalized :
    UniformNormalizedMatrix mehler physical.predecessor
  perturbation :
    BF4BufferedFiniteCarrierHSPerturbation
      physical.centeredPhysicalMatrix
      (vacuumRemovedMatrix mehler physical.predecessor)
      (physical.predecessor + 1)
      approximation

/-- The corrected fixed-scale nonlinear quarter theorem on the literal
matched physical carrier. -/
theorem matchedCentered_perronRatio_le_quarter
    {family :
      BF4MatchedPhysicalAFBridge.MatchedBlockFamily}
    {g : Q'}
    {physical :
      MatchedUniformNormalizedSameCarrier
        (family := family) (g := g)}
    {approximation : Nat}
    (comparison :
      MatchedCenteredMehlerComparison physical approximation)
    (identification :
      NormalizedSameCarrierMehlerHSConvergence.PerronIdentification
        physical.centeredPhysicalMatrix
        (physical.predecessor + 1)) :
    identification.qS ≤ oneQuarter := by
  exact bf4_nonlinear_eigenmode_ratio_le_quarter
    comparison.perturbation identification.perronMode

#print axioms uniformVacuumProjector_row_normalized
#print axioms uniformVacuumProjector_rowApply
#print axioms uniformVacuumProjector_annihilates_meanZero
#print axioms MeanZeroFiniteCarrierEigenmode.toVacuumRemoved
#print axioms NormalizedSameCarrierMehlerHSConvergence.bufferedPerturbation
#print axioms NormalizedSameCarrierMehlerHSConvergence.perronRatio_le_quarter
#print axioms NormalizedSameCarrierMehlerHSConvergence.eventually_perronRatio_le_quarter
#print axioms MatchedUniformNormalizedSameCarrier.normalizedMatrix
#print axioms matchedCentered_perronRatio_le_quarter

end YMGap.Continuum.BF4NormalizedSameCarrierPerron
