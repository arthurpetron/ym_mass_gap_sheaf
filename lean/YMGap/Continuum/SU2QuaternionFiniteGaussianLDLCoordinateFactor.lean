/-
# Rational Heron factors for LDL-certified finite Gaussian covariance

An exact rational covariance matrix can have irrational square-root entries.
This leaf avoids choosing those roots.  Given a checked rational `L D L^T`
certificate with positive pivots, it replaces each `sqrt(D_k)` by the explicit
rational Heron iterate at a requested stage.  The induced covariance factor is
the checked matrix plus a literal residual, and the absolute residual has a
geometrically decaying rational envelope.  Every stage feeds the existing
finite coordinate-pullback and three-color covariance theorem.

Consumer: a coordinate-space construction of finite FREE-reference Gaussian
rows without sine/cosine eigenvectors.  An actual precision matrix, its exact
rational inverse, and the LDL tables still have to be supplied and checked.
This module proves no density/Jacobian or pushforward-law identity, no
cutoff-uniform estimate, no compact-Haar/ORIGINAL comparison, and no continuum
or physical mass-gap statement.
-/

import YMGap.Constructive.Sqrt
import YMGap.Continuum.FiniteRationalLDLCertificate
import YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_map_eq_listQSum {A : Type} (f : A → Q') :
    ∀ ids : List A, qListSum (ids.map f) = listQSum f ids
  | [] => rfl
  | _ :: ids => by
      simp only [List.map, qListSum, listQSum]
      rw [qListSum_map_eq_listQSum f ids]

private theorem listQSum_add {A : Type} (f g : A → Q') :
    ∀ ids : List A,
      listQSum (fun i => f i + g i) ids ≈
        listQSum f ids + listQSum g ids
  | [] => Q'.eqv_symm (QPoly.q_zero_add_eqv 0)
  | i :: ids =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (listQSum_add f g ids))
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
          (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
          (by decide) (fun
            | 0 => f i
            | 1 => g i
            | 2 => listQSum f ids
            | _ => listQSum g ids))

private theorem abs_listQSum_le {A : Type} (f bound : A → Q') :
    ∀ ids : List A,
      (∀ i, i ∈ ids → Q'.abs (f i) ≤ bound i) →
      Q'.abs (listQSum f ids) ≤ listQSum bound ids
  | [], _ => by
      exact Q'.le_of_eqv (Q'.eqv_refl _)
  | i :: ids, h => by
      refine Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) ?_
      exact Q'.add_le_add
        (h i List.mem_cons_self)
        (abs_listQSum_le f bound ids
          (fun j hj => h j (List.mem_cons_of_mem i hj)))

/-- Executable strict positivity check for the pivots used by the Heron
residual estimate. -/
def finiteLDLPositiveDiagonalCheck (n : Nat) (diagonal : Nat → Q') : Bool :=
  (List.range n).all fun k => decide ((0 : Q') < diagonal k)

theorem finiteLDLPositiveDiagonalCheck_pos
    {n : Nat} {diagonal : Nat → Q'}
    (hcheck : finiteLDLPositiveDiagonalCheck n diagonal = true)
    {k : Nat} (hk : k < n) :
    (0 : Q') < diagonal k := by
  unfold finiteLDLPositiveDiagonalCheck at hcheck
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck k (List.mem_range.mpr hk))

/-- Rational factor at one Heron stage: `L_ik * sqrt(D_k)` with the square
root replaced by its explicit rational iterate. -/
def heronLDLTransform (lower : Nat → Nat → Q')
    (diagonal : Nat → Q') (stage row column : Nat) : Q' :=
  lower row column * heronSeq (diagonal column) stage

/-- Exact signed entry residual of the staged factor covariance relative to
the rational `L D L^T` Gram. -/
def ldlFactorResidual (n : Nat) (lower : Nat → Nat → Q')
    (diagonal : Nat → Q') (stage left right : Nat) : Q' :=
  listQSum
    (fun k => errAt (diagonal k) stage * (lower left k * lower right k))
    (List.range n)

/-- Rational absolute envelope for the staged factor residual. -/
def ldlFactorResidualEnvelope (n : Nat) (lower : Nat → Nat → Q')
    (diagonal : Nat → Q') (stage left right : Nat) : Q' :=
  listQSum
    (fun k =>
      (errAt (diagonal k) 0 * HalfPow.half ^ stage) *
        Q'.abs (lower left k * lower right k))
    (List.range n)

private theorem heronLDLTerm_split
    (lower : Nat → Nat → Q') (diagonal : Nat → Q')
    (stage left right k : Nat) :
    heronLDLTransform lower diagonal stage left k *
        heronLDLTransform lower diagonal stage right k ≈
      diagonal k * (lower left k * lower right k) +
        errAt (diagonal k) stage * (lower left k * lower right k) := by
  unfold heronLDLTransform errAt
  exact poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
    (.add (.mul (.var 3) (.mul (.var 0) (.var 1)))
      (.mul (.add (.mul (.var 2) (.var 2)) (.neg (.var 3)))
        (.mul (.var 0) (.var 1))))
    (by decide) (fun
      | 0 => lower left k
      | 1 => lower right k
      | 2 => heronSeq (diagonal k) stage
      | _ => diagonal k)

/-- Exact staged covariance: the rational Heron factor reconstructs the LDL
Gram plus its explicit signed residual. -/
theorem factorCovariance_heronLDLTransform
    (n stage left right : Nat) (lower : Nat → Nat → Q')
    (diagonal : Nat → Q') :
    factorCovariance n (heronLDLTransform lower diagonal stage) left right ≈
      finiteLDLGram n lower diagonal left right +
        ldlFactorResidual n lower diagonal stage left right := by
  unfold factorCovariance finiteLDLGram ldlFactorResidual
  rw [qListSum_map_eq_listQSum]
  exact Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun k => heronLDLTerm_split lower diagonal stage left right k)
      (List.range n))
    (listQSum_add
      (fun k => diagonal k * (lower left k * lower right k))
      (fun k => errAt (diagonal k) stage *
        (lower left k * lower right k))
      (List.range n))

/-- A successful exact LDL check identifies the staged covariance with the
checked matrix plus the same explicit residual. -/
theorem factorCovariance_heronLDLTransform_checked
    {n stage left right : Nat} {matrix lower : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hcheck : finiteLDLCheck n matrix lower diagonal = true)
    (hleft : left < n) (hright : right < n) :
    factorCovariance n (heronLDLTransform lower diagonal stage) left right ≈
      matrix left right +
        ldlFactorResidual n lower diagonal stage left right := by
  exact Q'.eqv_trans _ _ _
    (factorCovariance_heronLDLTransform n stage left right lower diagonal)
    (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm
        (finiteLDLCheck_entries hcheck hleft hright)))

private theorem heronLDLResidualTerm_abs_le
    (lower : Nat → Nat → Q') (diagonal : Nat → Q')
    (stage left right k : Nat) (hpositive : (0 : Q') < diagonal k) :
    Q'.abs
        (errAt (diagonal k) stage * (lower left k * lower right k)) ≤
      (errAt (diagonal k) 0 * HalfPow.half ^ stage) *
        Q'.abs (lower left k * lower right k) := by
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le (errAt (diagonal k) stage)
      (lower left k * lower right k)) ?_
  rw [ExpNeg.abs_of_nonneg (errAt_nonneg (diagonal k) hpositive stage)]
  exact Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.abs (lower left k * lower right k))
    (errAt_le_geom (diagonal k) hpositive stage)
    (Q'.abs_nonneg _)

/-- The staged factor residual is bounded by a fully explicit geometric
rational envelope whenever the checked pivots are strictly positive. -/
theorem ldlFactorResidual_abs_le
    {n stage left right : Nat} {lower : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hpositive : finiteLDLPositiveDiagonalCheck n diagonal = true) :
    Q'.abs (ldlFactorResidual n lower diagonal stage left right) ≤
      ldlFactorResidualEnvelope n lower diagonal stage left right := by
  unfold ldlFactorResidual ldlFactorResidualEnvelope
  exact abs_listQSum_le _ _ (List.range n) (fun k hk =>
    heronLDLResidualTerm_abs_le lower diagonal stage left right k
      (finiteLDLPositiveDiagonalCheck_pos hpositive (List.mem_range.mp hk)))

/-- Entrywise error of the rational staged factor from the exact checked
covariance matrix. -/
theorem factorCovariance_heronLDLTransform_error
    {n stage left right : Nat} {matrix lower : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hcheck : finiteLDLCheck n matrix lower diagonal = true)
    (hpositive : finiteLDLPositiveDiagonalCheck n diagonal = true)
    (hleft : left < n) (hright : right < n) :
    Q'.abs
        (factorCovariance n (heronLDLTransform lower diagonal stage)
          left right + -matrix left right) ≤
      ldlFactorResidualEnvelope n lower diagonal stage left right := by
  have hfactor := factorCovariance_heronLDLTransform_checked
    (stage := stage) hcheck hleft hright
  have hcancel :
      factorCovariance n (heronLDLTransform lower diagonal stage) left right +
          -matrix left right ≈
        ldlFactorResidual n lower diagonal stage left right :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hfactor)
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
        (.var 1) (by decide) (fun
          | 0 => matrix left right
          | _ => ldlFactorResidual n lower diagonal stage left right))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hcancel))
    (ldlFactorResidual_abs_le hpositive)

/-- Every rational Heron stage is an immediate exact input to the checked
three-color finite Gaussian covariance theorem. -/
theorem finiteGaussianRadialCovariance_threeColorHeronLDLRows
    (physicalSize stage : Nat) (lower : Nat → Nat → Q')
    (diagonal : Nat → Q') (b d : Nat → Q') :
    finiteGaussianCovariance
        (physicalSize + (physicalSize + physicalSize))
        (polyMul
          (finiteGaussianRadialSquare
            (physicalSize + (physicalSize + physicalSize)) 3
            (threeColorRows physicalSize
              (pulledRow physicalSize
                (heronLDLTransform lower diagonal stage) b)))
          (finiteGaussianRadialSquare
            (physicalSize + (physicalSize + physicalSize)) 3
            (threeColorRows physicalSize
              (pulledRow physicalSize
                (heronLDLTransform lower diagonal stage) b))))
        (finiteGaussianRadialSquare
          (physicalSize + (physicalSize + physicalSize)) 3
          (threeColorRows physicalSize
            (pulledRow physicalSize
              (heronLDLTransform lower diagonal stage) d))) ≈
      60 *
        physicalCovarianceBilinear physicalSize physicalSize
          (heronLDLTransform lower diagonal stage) b b *
        (physicalCovarianceBilinear physicalSize physicalSize
            (heronLDLTransform lower diagonal stage) b d *
          physicalCovarianceBilinear physicalSize physicalSize
            (heronLDLTransform lower diagonal stage) b d) := by
  exact finiteGaussianRadialCovariance_threeColorPulledRows
    physicalSize physicalSize (heronLDLTransform lower diagonal stage) b d

end YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor.finiteLDLPositiveDiagonalCheck_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor.factorCovariance_heronLDLTransform
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor.factorCovariance_heronLDLTransform_checked
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor.ldlFactorResidual_abs_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor.factorCovariance_heronLDLTransform_error
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor.finiteGaussianRadialCovariance_threeColorHeronLDLRows
