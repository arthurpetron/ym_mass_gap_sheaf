/-
# Exact finite centered-restriction spectral certificates

Finite mean-zero computations often eliminate one vacuum coordinate before
factorization.  This module makes that reduction explicit and constructive.
A restriction certificate supplies

* a lift from reduced coordinates to the full finite carrier;
* an exact weighted-centering proof for every lifted vector;
* a constructive reduced representative for every centered full vector;
* exact identification of two reduced matrices with the lifted upper and
  lower penalized quadratics.

Ordinary or cleared-denominator LDL checks of those reduced matrices then
prove the same absolute full-carrier contraction.  No basis, physical model,
LDL table, cutoff family, continuum limit, or Clay conclusion is constructed
here.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteRationalPenalizedMatrix

namespace YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr_both
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Quadratic invariance under pointwise coefficient equivalence -/

/-- A finite matrix quadratic depends only on the in-range coefficient values
up to rational equivalence. -/
theorem finiteMatrixQuadratic_coefficient_congr
    {n : Nat} {matrix : Nat → Nat → Q'}
    {left right : Nat → Q'}
    (hagrees : ∀ i, i < n → left i ≈ right i) :
    finiteMatrixQuadratic n matrix left ≈
      finiteMatrixQuadratic n matrix right := by
  unfold finiteMatrixQuadratic
  apply listQSum_congr_on
  intro i hi
  apply listQSum_congr_on
  intro j hj
  exact Q'.mul_eqv_congr_right _ _ (matrix i j)
    (mul_eqv_congr_both
      (hagrees i (List.mem_range.mp hi))
      (hagrees j (List.mem_range.mp hj)))

/-- The finite weighted diagonal quadratic likewise depends only on in-range
coefficient values up to rational equivalence. -/
theorem finiteDiagonalQuadratic_coefficient_congr
    {n : Nat} {weight : Nat → Q'}
    {left right : Nat → Q'}
    (hagrees : ∀ i, i < n → left i ≈ right i) :
    finiteDiagonalQuadratic n weight left ≈
      finiteDiagonalQuadratic n weight right := by
  unfold finiteDiagonalQuadratic
  apply listQSum_congr_on
  intro i hi
  exact Q'.mul_eqv_congr_right _ _ (weight i)
    (mul_eqv_congr_both
      (hagrees i (List.mem_range.mp hi))
      (hagrees i (List.mem_range.mp hi)))

/-! ## 2. Exact centered coordinate restriction -/

/-- Exact data identifying a reduced coordinate space with every centered
vector in a full finite reversible carrier.  `complete` is Type-valued data:
it constructs reduced coordinates rather than merely asserting existence. -/
structure FiniteCenteredTwoSidedRestriction
    (n : Nat) (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q') : Type 1 where
  reducedSize : Nat
  lift : (Nat → Q') → Nat → Q'
  liftCentered :
    ∀ reduced,
      finiteWeightedMean n weight (lift reduced) ≈ 0
  complete :
    ∀ coefficient,
      finiteWeightedMean n weight coefficient ≈ 0 →
        { reduced : Nat → Q' //
          ∀ i, i < n → coefficient i ≈ lift reduced i }
  upperMatrix : Nat → Nat → Q'
  lowerMatrix : Nat → Nat → Q'
  upperIdentify :
    ∀ reduced,
      finiteMatrixQuadratic reducedSize upperMatrix reduced ≈
        finitePenalizedReversibleQuadratic
          n q weight kernel (lift reduced)
  lowerIdentify :
    ∀ reduced,
      finiteMatrixQuadratic reducedSize lowerMatrix reduced ≈
        finiteLowerPenalizedReversibleQuadratic
          n q weight kernel (lift reduced)

namespace FiniteCenteredTwoSidedRestriction

/-- Nonnegativity of both reduced matrices proves the absolute contraction for
every centered full coefficient vector. -/
theorem absContraction_of_matrix_nonnegative
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    (restriction :
      FiniteCenteredTwoSidedRestriction n q weight kernel)
    (hupper : ∀ reduced,
      (0 : Q') ≤ finiteMatrixQuadratic
        restriction.reducedSize restriction.upperMatrix reduced)
    (hlower : ∀ reduced,
      (0 : Q') ≤ finiteMatrixQuadratic
        restriction.reducedSize restriction.lowerMatrix reduced)
    (coefficient : Nat → Q')
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    Q'.abs (finiteMatrixQuadratic n kernel coefficient) ≤
      q * finiteDiagonalQuadratic n weight coefficient := by
  let chosen := restriction.complete coefficient hcenter
  let reduced : Nat → Q' := chosen.val
  have hagrees : ∀ i, i < n →
      coefficient i ≈ restriction.lift reduced i :=
    chosen.property
  have hlift :
      Q'.abs
          (finiteMatrixQuadratic n kernel
            (restriction.lift reduced)) ≤
        q * finiteDiagonalQuadratic n weight
          (restriction.lift reduced) := by
    apply finiteReversibleAbsContraction_of_two_penalized
    · exact Q'.le_trans' _ _ _ (hupper reduced)
        (Q'.le_of_eqv (restriction.upperIdentify reduced))
    · exact Q'.le_trans' _ _ _ (hlower reduced)
        (Q'.le_of_eqv (restriction.lowerIdentify reduced))
    · exact restriction.liftCentered reduced
  have hleft :
      Q'.abs (finiteMatrixQuadratic n kernel coefficient) ≈
        Q'.abs
          (finiteMatrixQuadratic n kernel
            (restriction.lift reduced)) :=
    Q'.abs_eqv_congr
      (finiteMatrixQuadratic_coefficient_congr hagrees)
  have hright :
      q * finiteDiagonalQuadratic n weight
          (restriction.lift reduced) ≈
        q * finiteDiagonalQuadratic n weight coefficient :=
    Q'.mul_eqv_congr_left q _ _
      (Q'.eqv_symm
        (finiteDiagonalQuadratic_coefficient_congr hagrees))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hlift (Q'.le_of_eqv hright))

end FiniteCenteredTwoSidedRestriction

/-! ## 3. Executable reduced LDL producers -/

/-- Two full exact LDL checks of the reduced upper and lower matrices. -/
structure FiniteCenteredRestrictionLDLCertificate
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    (restriction :
      FiniteCenteredTwoSidedRestriction n q weight kernel) : Type 1 where
  upperLower : Nat → Nat → Q'
  upperDiagonal : Nat → Q'
  upperCheck :
    finiteLDLCheck restriction.reducedSize
      restriction.upperMatrix upperLower upperDiagonal = true
  lowerLower : Nat → Nat → Q'
  lowerDiagonal : Nat → Q'
  lowerCheck :
    finiteLDLCheck restriction.reducedSize
      restriction.lowerMatrix lowerLower lowerDiagonal = true

namespace FiniteCenteredRestrictionLDLCertificate

/-- Soundness of the two reduced full LDL checks. -/
theorem absContraction
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    {restriction :
      FiniteCenteredTwoSidedRestriction n q weight kernel}
    (certificate :
      FiniteCenteredRestrictionLDLCertificate restriction)
    (coefficient : Nat → Q')
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    Q'.abs (finiteMatrixQuadratic n kernel coefficient) ≤
      q * finiteDiagonalQuadratic n weight coefficient :=
  restriction.absContraction_of_matrix_nonnegative
    (fun reduced =>
      finiteMatrixQuadratic_nonnegative_of_ldl_check
        certificate.upperCheck reduced)
    (fun reduced =>
      finiteMatrixQuadratic_nonnegative_of_ldl_check
        certificate.lowerCheck reduced)
    coefficient hcenter

end FiniteCenteredRestrictionLDLCertificate

/-- A centered coordinate restriction bundled with complete ordinary LDL
checks of both of its reduced matrices.  Packaging this dependency at the
generic finite level avoids rebuilding a model-specific dependent recursor. -/
structure FiniteCenteredRestrictionLDLPackage
    (n : Nat) (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q') : Type 1 where
  restriction :
    FiniteCenteredTwoSidedRestriction n q weight kernel
  certificate : FiniteCenteredRestrictionLDLCertificate restriction

namespace FiniteCenteredRestrictionLDLPackage

/-- Soundness of a bundled restriction and its ordinary LDL checks. -/
theorem absContraction
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    (package : FiniteCenteredRestrictionLDLPackage n q weight kernel)
    (coefficient : Nat → Q')
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    Q'.abs (finiteMatrixQuadratic n kernel coefficient) ≤
      q * finiteDiagonalQuadratic n weight coefficient :=
  package.certificate.absContraction coefficient hcenter

end FiniteCenteredRestrictionLDLPackage

/-- Shardable cleared-denominator LDL checks of both reduced matrices. -/
structure FiniteCenteredRestrictionClearedLDLCertificate
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    (restriction :
      FiniteCenteredTwoSidedRestriction n q weight kernel) : Type 1 where
  upperLower : Nat → Nat → Q'
  upperDiagonal : Nat → Q'
  upperCommon : Nat → Nat → Nat
  upperRowsCheck :
    finiteLDLClearedRowsCheck restriction.reducedSize
      restriction.upperMatrix upperLower upperDiagonal upperCommon = true
  upperTriangular : ∀ i k, i < k → upperLower i k = 0
  upperDiagonalCheck :
    finiteLDLDiagonalCheck restriction.reducedSize upperDiagonal = true
  lowerLower : Nat → Nat → Q'
  lowerDiagonal : Nat → Q'
  lowerCommon : Nat → Nat → Nat
  lowerRowsCheck :
    finiteLDLClearedRowsCheck restriction.reducedSize
      restriction.lowerMatrix lowerLower lowerDiagonal lowerCommon = true
  lowerTriangular : ∀ i k, i < k → lowerLower i k = 0
  lowerDiagonalCheck :
    finiteLDLDiagonalCheck restriction.reducedSize lowerDiagonal = true

namespace FiniteCenteredRestrictionClearedLDLCertificate

/-- Soundness of the two independently shardable reduced LDL checks. -/
theorem absContraction
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    {restriction :
      FiniteCenteredTwoSidedRestriction n q weight kernel}
    (certificate :
      FiniteCenteredRestrictionClearedLDLCertificate restriction)
    (coefficient : Nat → Q')
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    Q'.abs (finiteMatrixQuadratic n kernel coefficient) ≤
      q * finiteDiagonalQuadratic n weight coefficient :=
  restriction.absContraction_of_matrix_nonnegative
    (fun reduced =>
      finiteMatrixQuadratic_nonnegative_of_cleared_ldl_check
        certificate.upperRowsCheck certificate.upperTriangular
        certificate.upperDiagonalCheck reduced)
    (fun reduced =>
      finiteMatrixQuadratic_nonnegative_of_cleared_ldl_check
        certificate.lowerRowsCheck certificate.lowerTriangular
        certificate.lowerDiagonalCheck reduced)
    coefficient hcenter

end FiniteCenteredRestrictionClearedLDLCertificate

/-- A centered coordinate restriction bundled with shardable
cleared-denominator LDL checks of both of its reduced matrices. -/
structure FiniteCenteredRestrictionClearedLDLPackage
    (n : Nat) (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q') : Type 1 where
  restriction :
    FiniteCenteredTwoSidedRestriction n q weight kernel
  certificate :
    FiniteCenteredRestrictionClearedLDLCertificate restriction

namespace FiniteCenteredRestrictionClearedLDLPackage

/-- Soundness of a bundled restriction and its cleared LDL checks. -/
theorem absContraction
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    (package :
      FiniteCenteredRestrictionClearedLDLPackage n q weight kernel)
    (coefficient : Nat → Q')
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    Q'.abs (finiteMatrixQuadratic n kernel coefficient) ≤
      q * finiteDiagonalQuadratic n weight coefficient :=
  package.certificate.absContraction coefficient hcenter

end FiniteCenteredRestrictionClearedLDLPackage

/-! ## 4. Generic cofinal families of changing finite carriers -/

/-- Ordinary bundled reduced LDL checks along a constructively selected
cofinal sequence of finite-model indices. -/
structure CofinalFiniteCenteredRestrictionLDLPackage
    (q : Q') (size : Nat → Nat)
    (weight : Nat → Nat → Q')
    (kernel : Nat → Nat → Nat → Q') : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ base, base ≤ anchor base
  certificate :
    ∀ base,
      FiniteCenteredRestrictionLDLPackage
        (size (anchor base)) q
        (weight (anchor base)) (kernel (anchor base))

/-- Cleared-denominator bundled reduced LDL checks along a constructively
selected cofinal sequence of finite-model indices. -/
structure CofinalFiniteCenteredRestrictionClearedLDLPackage
    (q : Q') (size : Nat → Nat)
    (weight : Nat → Nat → Q')
    (kernel : Nat → Nat → Nat → Q') : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ base, base ≤ anchor base
  certificate :
    ∀ base,
      FiniteCenteredRestrictionClearedLDLPackage
        (size (anchor base)) q
        (weight (anchor base)) (kernel (anchor base))

end YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate

#print axioms
  YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate.finiteMatrixQuadratic_coefficient_congr
#print axioms
  YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate.FiniteCenteredTwoSidedRestriction.absContraction_of_matrix_nonnegative
#print axioms
  YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate.FiniteCenteredRestrictionLDLCertificate.absContraction
#print axioms
  YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate.FiniteCenteredRestrictionClearedLDLCertificate.absContraction
#print axioms
  YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate.FiniteCenteredRestrictionLDLPackage.absContraction
#print axioms
  YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate.FiniteCenteredRestrictionClearedLDLPackage.absContraction
