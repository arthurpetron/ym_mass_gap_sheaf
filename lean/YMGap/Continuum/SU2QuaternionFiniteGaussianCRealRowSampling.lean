/-
# Witness-bearing rational samples of finite CReal Gaussian rows

This leaf turns an arbitrary constructive-real coefficient row, together with
Type-level inner regularity for every coefficient, into a rational row at each
explicit outer stage.  Stage `n` uses tolerance `1/(n+1)`.  Every coefficient
comes with an `ExplicitConvergenceCertificate` whose outer modulus is
`epsilon.den` and whose inner approximation modulus is the supplied coefficient
rate at that stage.

The sampled rational rows feed the already checked disjoint three-color lift
and radial sixth-moment identity without any new independence, covariance,
square-root or Gaussian-pullback premise.  At every stage the exact covariance
is therefore

  Cov(S_B^2,S_D) = 60 * sigma_n * rho_n^2.

Consumer: rational approximations to the one-color open-cube transverse rows in
the retained FREE-reference trace-source quartic.  This file pays the generic
row-sampling and Type-level modulus obligation only.  It does not construct the
open-cube sine/cosine modes or prove their transverse, orthogonality, dispersion
or boundary identities.  In particular, the Machin-`Pi.pi` to trig-series
identity needed for `sin(pi)=0` remains separate, as do compact-Haar comparison,
the ORIGINAL signed response and every continuum or Clay-facing conclusion.
-/

import YMGap.Constructive.CRealConvergenceCertificate
import YMGap.Constructive.CRealStableSampling
import YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianCRealRowSampling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-- The rational coefficient row sampled at tolerance `1/(stage+1)` using the
supplied Type-level inner regularity of each coefficient. -/
def sampledRow
    (row : Nat → CReal)
    (regularity : ∀ coordinate, InnerRegularity (row coordinate))
    (stage coordinate : Nat) : Q' :=
  sample (row coordinate) (regularity coordinate) (Q'.invSucc stage)

/-- A sampled coefficient is within the displayed outer-stage tolerance of
every sufficiently late approximation of the same constructive real. -/
theorem sampledRow_error_bound
    (row : Nat → CReal)
    (regularity : ∀ coordinate, InnerRegularity (row coordinate))
    (stage coordinate approximation : Nat)
    (hlate :
      (regularity coordinate).rate (Q'.invSucc stage) ≤ approximation) :
    Q'.abs
        (sampledRow row regularity stage coordinate +
          -((row coordinate).approx approximation)) ≤
      Q'.invSucc stage := by
  exact sample_error_bound
    (row coordinate) (regularity coordinate) (Q'.invSucc stage)
    (Q'.invSucc_pos stage) approximation hlate

/-- Sound coefficient cap for the computed rational row.  No bound on early
raw approximations is assumed. -/
theorem sampledRow_abs_le
    (row : Nat → CReal)
    (regularity : ∀ coordinate, InnerRegularity (row coordinate))
    (stage coordinate : Nat) (bound : Q')
    (hbound : leRat (CReal.abs (row coordinate)) bound) :
    Q'.abs (sampledRow row regularity stage coordinate) ≤
      bound + Q'.invSucc stage := by
  exact sample_abs_le
    (row coordinate) (regularity coordinate) bound (Q'.invSucc stage)
    hbound (Q'.invSucc_pos stage)

/-- Explicit convergence of one rationally sampled row coefficient to the
actual constructive-real coefficient.  Both moduli are data:

* outer row stage: `epsilon.den`;
* inner approximation stage at row stage `n`:
  `regularity.rate (1/(n+1))`.
-/
def sampledRowCoefficientCertificate
    (row : Nat → CReal)
    (regularity : ∀ coordinate, InnerRegularity (row coordinate))
    (coordinate : Nat) :
    ExplicitConvergenceCertificate
      (fun stage =>
        CReal.ofQ' (sampledRow row regularity stage coordinate))
      (row coordinate) where
  modulus := fun epsilon => epsilon.den
  approximationModulus := fun _epsilon stage =>
    (regularity coordinate).rate (Q'.invSucc stage)
  bound := by
    intro epsilon hepsilon stage hstage approximation happroximation
    have htolerance : Q'.invSucc stage ≤ epsilon :=
      Q'.le_trans' _ _ _
        (ExpNeg.invSucc_le_of_le hstage)
        (HalfPow.invSucc_den_le epsilon hepsilon)
    have hsample :
        Q'.abs
            (sampledRow row regularity stage coordinate +
              -((row coordinate).approx approximation)) ≤
          epsilon :=
      Q'.le_trans' _ _ _
        (sampledRow_error_bound row regularity stage coordinate approximation
          happroximation)
        htolerance
    refine ⟨ExpNeg.le_add_of_abs_sub_le hsample, ?_⟩
    exact ExpNeg.le_add_of_abs_sub_le
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (ExpNeg.abs_sub_comm
            ((row coordinate).approx approximation)
            (sampledRow row regularity stage coordinate)))
        hsample)

/-- Every finite row coordinate receives the same explicit outer modulus and
its own supplied inner coefficient rate. -/
def finiteSampledRowCertificates
    (coordinateCount : Nat)
    (row : Nat → CReal)
    (regularity : ∀ coordinate, InnerRegularity (row coordinate)) :
    ∀ coordinate, coordinate < coordinateCount →
      ExplicitConvergenceCertificate
        (fun stage =>
          CReal.ofQ' (sampledRow row regularity stage coordinate))
        (row coordinate) :=
  fun coordinate _ =>
    sampledRowCoefficientCertificate row regularity coordinate

/-- The existing exact three-color radial covariance applies at every rational
sampling stage of two constructive-real one-color rows.  This is the literal
consumer of `sampledRow`; no limit identity is hidden in the statement. -/
theorem finiteGaussianRadialCovariance_sampledCRealRows
    (coordinateCount stage : Nat)
    (b d : Nat → CReal)
    (bRegularity : ∀ coordinate, InnerRegularity (b coordinate))
    (dRegularity : ∀ coordinate, InnerRegularity (d coordinate)) :
    finiteGaussianCovariance
        (coordinateCount + (coordinateCount + coordinateCount))
        (polyMul
          (finiteGaussianRadialSquare
            (coordinateCount + (coordinateCount + coordinateCount)) 3
            (threeColorRows coordinateCount
              (sampledRow b bRegularity stage)))
          (finiteGaussianRadialSquare
            (coordinateCount + (coordinateCount + coordinateCount)) 3
            (threeColorRows coordinateCount
              (sampledRow b bRegularity stage))))
        (finiteGaussianRadialSquare
          (coordinateCount + (coordinateCount + coordinateCount)) 3
          (threeColorRows coordinateCount
            (sampledRow d dRegularity stage))) ≈
      60 *
        finiteRowNorm2 coordinateCount
          (sampledRow b bRegularity stage) *
        (finiteRowGram coordinateCount
            (sampledRow b bRegularity stage)
            (sampledRow d dRegularity stage) *
          finiteRowGram coordinateCount
            (sampledRow b bRegularity stage)
            (sampledRow d dRegularity stage)) := by
  exact finiteGaussianRadialCovariance_threeColorRows
    coordinateCount
    (sampledRow b bRegularity stage)
    (sampledRow d dRegularity stage)

end YMGap.Continuum.SU2QuaternionFiniteGaussianCRealRowSampling

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianCRealRowSampling.sampledRow_error_bound
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianCRealRowSampling.sampledRowCoefficientCertificate
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianCRealRowSampling.finiteGaussianRadialCovariance_sampledCRealRows
