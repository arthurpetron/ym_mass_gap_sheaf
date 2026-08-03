/-
# All-cutoff normalization for the exact BF4 slab comparison

The selected-face Peter--Weyl calculation proves that every non-vacuum
vacuum-boundary term of the literal 116-link slab has zero Haar contraction.
Consequently the exact vacuum partition is one at every label cutoff and for
every positive coupling.  This file installs that theorem in the
physical/reference comparison layer.

The resulting AF certificate no longer asks an analytic producer to supply
vacuum positivity or reflection symmetry.  Its remaining fields are exactly
the grouped-reference spectral eighth, the pointwise physical/reference
error, and the payment of finite carrier growth by the Haar diagonal.
-/

import YMGap.Continuum.BF4ExactSlabGroupedAFComparison
import YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord

namespace YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabGroupedAFComparison
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4GeometricAllSpinHaarGram
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Canonical exact normalization at every cutoff -/

/-- The literal exact slab has a canonical normalization at every coupling
and every label cutoff.  No tail estimate or positivity certificate remains
as input. -/
def exactSlabNormalizationData_allCutoffs
    (w : Q') (K : Nat) : ExactSlabNormalizationData w K :=
  ExactSlabNormalizationData.ofHaarNontrivialTermsVanish
    (exactVacuumNontrivialHaarTermsVanish_all_cutoffs K)

/-- The exact vacuum partition is identically one, uniformly in both the
coupling and cutoff. -/
theorem exactSlabVacuumPartition_eqv_one_allCutoffs
    (w : Q') (K : Nat) :
    exactSlabVacuumPartition w K ≈ 1 :=
  exactSlabVacuumPartition_eqv_one_of_nontrivial_terms_vanish
    (exactSlabVacuumNontrivialTermsVanish_of_haar
      (exactVacuumNontrivialHaarTermsVanish_all_cutoffs K) w)

/-- Strict positivity of the exact partition is therefore unconditional. -/
theorem exactSlabVacuumPartition_pos_allCutoffs
    (w : Q') (K : Nat) :
    (0 : Q') < exactSlabVacuumPartition w K :=
  (exactSlabNormalizationData_allCutoffs w K).vacuum_partition_pos

/-- The canonical all-cutoff normalized literal slab. -/
def normalizedExactSlabKernel_allCutoffs
    (w : Q') (K : Nat) (left right : EdgeLabelling) : Q' :=
  normalizedExactSlabKernel
    (exactSlabNormalizationData_allCutoffs w K) left right

theorem normalizedExactSlabKernel_allCutoffs_symmetric
    (w : Q') (K : Nat)
    (left right : EdgeLabelling)
    (hleft : left ∈ exactSlabPositiveHaarStates K)
    (hright : right ∈ exactSlabPositiveHaarStates K) :
    normalizedExactSlabKernel_allCutoffs w K left right ≈
      normalizedExactSlabKernel_allCutoffs w K right left :=
  normalizedExactSlabKernel_symmetric
    (exactSlabNormalizationData_allCutoffs w K)
    left right hleft hright

/-! ## 2. The reduced one-scale analytic producer -/

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hpointwise => by
      exact Q'.add_le_add
        (hpointwise head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hpointwise item (List.mem_cons_of_mem head hitem)))

/-- The exact analytic content of the row-error/growth step.  Unlike a
uniform entry budget, this interface permits target-dependent decay.  The
producer pays only the actual sum of its error majorant over the retained
carrier; no factor `(K+1)^24` is inserted by the consumer. -/
structure AllCutoffExactSlabGroupedRowSummableEighthData
    (w : Q') (K diagonalOrder crossOrder : Nat) : Type where
  spectral :
    GroupedMehlerHaarBoundarySpectralData
      K diagonalOrder crossOrder
  rate_le_oneEighth :
    spectral.rate ≤ Q'.mkPos 1 8 (by decide)
  entryBudget : EdgeLabelling → EdgeLabelling → Q'
  entryBudget_nonnegative :
    ∀ source,
      source ∈ exactSlabPositiveHaarStates K →
      ∀ target,
        target ∈ exactSlabPositiveHaarStates K →
          (0 : Q') ≤ entryBudget source target
  pointwise_entry_error :
    ∀ source,
      source ∈ exactSlabPositiveHaarStates K →
      ∀ target,
        target ∈ exactSlabPositiveHaarStates K →
          Q'.abs
              (normalizedExactSlabKernel_allCutoffs
                  w K source target +
                (-normalizedGroupedMehlerKernel
                  diagonalOrder crossOrder source target)) ≤
            entryBudget source target
  summed_growth_payment :
    ∀ source,
      source ∈ exactSlabPositiveHaarStates K →
        listQSum
            (entryBudget source)
            (exactSlabPositiveHaarStates K) ≤
          Q'.mkPos 1 8 (by decide) *
            exactSlabBoundaryHaarDiagonalWeight source

namespace AllCutoffExactSlabGroupedRowSummableEighthData

/-- Target-dependent entry control plus its exact row sum gives the required
row-relative eighth without a worst-case carrier-cardinality loss. -/
theorem row_relative_error_le_oneEighth
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (data :
      AllCutoffExactSlabGroupedRowSummableEighthData
        w K diagonalOrder crossOrder) :
    ∀ source,
      source ∈ exactSlabPositiveHaarStates K →
        finiteJointDifferenceAbsRowMass
            (exactSlabPositiveHaarStates K)
            (normalizedExactSlabKernel_allCutoffs w K)
            (normalizedGroupedMehlerKernel
              diagonalOrder crossOrder)
            source ≤
          Q'.mkPos 1 8 (by decide) *
            exactSlabBoundaryHaarDiagonalWeight source := by
  intro source hsource
  unfold finiteJointDifferenceAbsRowMass
  exact Q'.le_trans' _ _ _
    (listQSum_le_termwise_local
      (fun target =>
        Q'.abs
          (normalizedExactSlabKernel_allCutoffs w K source target +
            (-normalizedGroupedMehlerKernel
              diagonalOrder crossOrder source target)))
      (data.entryBudget source)
      (exactSlabPositiveHaarStates K)
      (data.pointwise_entry_error source hsource))
    (data.summed_growth_payment source hsource)

/-- The row-summable producer feeds the existing Schur consumer with exact
normalization and `epsilon = 1/8`. -/
def toRowComparison
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (data :
      AllCutoffExactSlabGroupedRowSummableEighthData
        w K diagonalOrder crossOrder) :
    ExactSlabGroupedRowComparison
      w K diagonalOrder crossOrder where
  normalization := exactSlabNormalizationData_allCutoffs w K
  spectral := data.spectral
  epsilon := Q'.mkPos 1 8 (by decide)
  epsilon_nonnegative := by decide
  row_relative_error := data.row_relative_error_le_oneEighth

/-- The sharpened row-summable certificate yields the exact quarter
quadratic contraction at one scale. -/
theorem exact_quadratic_abs_le_quarter
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (data :
      AllCutoffExactSlabGroupedRowSummableEighthData
        w K diagonalOrder crossOrder)
    (observable : EdgeLabelling → Q')
    (hmean : ExactSlabBoundaryMeanZero K observable) :
    Q'.abs
        (finiteJointQuadratic
          (exactSlabPositiveHaarStates K)
          observable
          (normalizedExactSlabKernel_allCutoffs w K)) ≤
      Q'.mkPos 1 4 (by decide) *
        exactSlabBoundaryWeightedSquare K observable := by
  exact ExactSlabGroupedRowComparison.exact_quadratic_abs_le_quarter
    data.toRowComparison
    data.rate_le_oneEighth
    (Q'.le_refl' (Q'.mkPos 1 8 (by decide)))
    observable hmean

end AllCutoffExactSlabGroupedRowSummableEighthData

/-- Entrywise eighth data after exact normalization has been discharged.
Compared with `ExactSlabGroupedEntrywiseEighthData`, this structure contains
no normalization field. -/
structure AllCutoffExactSlabGroupedEntrywiseEighthData
    (w : Q') (K diagonalOrder crossOrder : Nat) : Type where
  spectral :
    GroupedMehlerHaarBoundarySpectralData
      K diagonalOrder crossOrder
  rate_le_oneEighth :
    spectral.rate ≤ Q'.mkPos 1 8 (by decide)
  entryBudget : EdgeLabelling → Q'
  entryBudget_nonnegative :
    ∀ source,
      source ∈ exactSlabPositiveHaarStates K →
        (0 : Q') ≤ entryBudget source
  pointwise_entry_error :
    ∀ source,
      source ∈ exactSlabPositiveHaarStates K →
      ∀ target,
        target ∈ exactSlabPositiveHaarStates K →
          Q'.abs
              (normalizedExactSlabKernel_allCutoffs
                  w K source target +
                (-normalizedGroupedMehlerKernel
                  diagonalOrder crossOrder source target)) ≤
            entryBudget source
  cube_growth_payment :
    ∀ source,
      source ∈ exactSlabPositiveHaarStates K →
        Q'.ofNat ((K + 1) ^ 24) * entryBudget source ≤
          Q'.mkPos 1 8 (by decide) *
            exactSlabBoundaryHaarDiagonalWeight source

namespace AllCutoffExactSlabGroupedEntrywiseEighthData

/-- Forgetting that normalization was proved canonically recovers the
existing generic comparison consumer. -/
def toEntrywiseEighthData
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (data :
      AllCutoffExactSlabGroupedEntrywiseEighthData
        w K diagonalOrder crossOrder) :
    ExactSlabGroupedEntrywiseEighthData
      w K diagonalOrder crossOrder where
  normalization := exactSlabNormalizationData_allCutoffs w K
  spectral := data.spectral
  rate_le_oneEighth := data.rate_le_oneEighth
  entryBudget := data.entryBudget
  entryBudget_nonnegative := data.entryBudget_nonnegative
  pointwise_entry_error := data.pointwise_entry_error
  cube_growth_payment := data.cube_growth_payment

/-- The former uniform entry budget is a special case of the sharper
target-dependent row-summable interface.  This conversion is the only place
where the crude `(K+1)^24` carrier bound is paid. -/
def toRowSummableEighthData
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (data :
      AllCutoffExactSlabGroupedEntrywiseEighthData
        w K diagonalOrder crossOrder) :
    AllCutoffExactSlabGroupedRowSummableEighthData
      w K diagonalOrder crossOrder where
  spectral := data.spectral
  rate_le_oneEighth := data.rate_le_oneEighth
  entryBudget := fun source _ => data.entryBudget source
  entryBudget_nonnegative := by
    intro source hsource _ _
    exact data.entryBudget_nonnegative source hsource
  pointwise_entry_error := data.pointwise_entry_error
  summed_growth_payment := by
    intro source hsource
    have hsum :
        listQSum
            (fun _ : EdgeLabelling => data.entryBudget source)
            (exactSlabPositiveHaarStates K) ≤
          Q'.ofNat (exactSlabPositiveHaarStates K).length *
            data.entryBudget source := by
      exact listQSum_le_length_mul
        (fun _ : EdgeLabelling => data.entryBudget source)
        (data.entryBudget_nonnegative source hsource)
        (exactSlabPositiveHaarStates K)
        (fun _ _ => Q'.le_refl' (data.entryBudget source))
    have hcarrier :
        Q'.ofNat (exactSlabPositiveHaarStates K).length *
            data.entryBudget source ≤
          Q'.ofNat ((K + 1) ^ 24) * data.entryBudget source := by
      exact Q'.mul_le_mul_of_nonneg_right _ _ _
        (Q'.ofNat_le_ofNat
          (exactSlabPositiveHaarStates_length_le K))
        (data.entryBudget_nonnegative source hsource)
    exact Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ hcarrier
        (data.cube_growth_payment source hsource))

/-- The reduced analytic producer implies the literal exact-slab quarter
contraction at one scale. -/
theorem exact_quadratic_abs_le_quarter
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (data :
      AllCutoffExactSlabGroupedEntrywiseEighthData
        w K diagonalOrder crossOrder)
    (observable : EdgeLabelling → Q')
    (hmean : ExactSlabBoundaryMeanZero K observable) :
    Q'.abs
        (finiteJointQuadratic
          (exactSlabPositiveHaarStates K)
          observable
          (normalizedExactSlabKernel_allCutoffs w K)) ≤
      Q'.mkPos 1 4 (by decide) *
        exactSlabBoundaryWeightedSquare K observable :=
  data.toEntrywiseEighthData.exact_quadratic_abs_le_quarter
    observable hmean

end AllCutoffExactSlabGroupedEntrywiseEighthData

/-! ## 3. AF-uniform reduced certificate -/

/-- AF-uniform producer at the target-dependent row-summable layer.  This is
the minimal explicit error/growth certificate consumed by the exact quarter
contraction theorem. -/
structure AllCutoffExactSlabGroupedAFRowSummableEighthCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') : Type where
  coupling_pos : ∀ scale, (0 : Q') < coupling scale
  coupling_le_window : ∀ scale, coupling scale ≤ law.g₁
  diagonalOrder : Nat → Nat
  crossOrder : Nat → Nat
  summable :
    ∀ scale,
      AllCutoffExactSlabGroupedRowSummableEighthData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (diagonalOrder scale)
        (crossOrder scale)

namespace AllCutoffExactSlabGroupedAFRowSummableEighthCertificate

/-- The row-summable AF producer feeds the already-proved uniform quarter
consumer directly. -/
def toAFQuarterCertificate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      AllCutoffExactSlabGroupedAFRowSummableEighthCertificate
        family law spacing coupling) :
    ExactSlabGroupedAFQuarterCertificate
      family law spacing coupling where
  coupling_pos := certificate.coupling_pos
  coupling_le_window := certificate.coupling_le_window
  diagonalOrder := certificate.diagonalOrder
  crossOrder := certificate.crossOrder
  comparison := fun scale =>
    (certificate.summable scale).toRowComparison
  rate_le_oneEighth := fun scale =>
    (certificate.summable scale).rate_le_oneEighth
  epsilon_le_oneEighth := fun _ =>
    Q'.le_refl' (Q'.mkPos 1 8 (by decide))

/-- The exact AF-uniform scalar budget obtained from target-dependent row
summability. -/
theorem rate_add_epsilon_le_quarter
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      AllCutoffExactSlabGroupedAFRowSummableEighthCertificate
        family law spacing coupling) :
    ∀ scale,
      ((certificate.toAFQuarterCertificate.comparison scale).spectral.rate +
        (certificate.toAFQuarterCertificate.comparison scale).epsilon) ≤
        Q'.mkPos 1 4 (by decide) :=
  certificate.toAFQuarterCertificate.rate_add_epsilon_le_quarter

end AllCutoffExactSlabGroupedAFRowSummableEighthCertificate

/-- AF-uniform comparison data with exact slab normalization removed from
the frontier. -/
structure AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') : Type where
  coupling_pos : ∀ scale, (0 : Q') < coupling scale
  coupling_le_window : ∀ scale, coupling scale ≤ law.g₁
  diagonalOrder : Nat → Nat
  crossOrder : Nat → Nat
  entrywise :
    ∀ scale,
      AllCutoffExactSlabGroupedEntrywiseEighthData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (diagonalOrder scale)
        (crossOrder scale)

namespace AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate

/-- The reduced all-cutoff certificate feeds the established exact AF
quarter-contraction consumer. -/
def toAFEntrywiseEighthCertificate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate
        family law spacing coupling) :
    ExactSlabGroupedAFEntrywiseEighthCertificate
      family law spacing coupling where
  coupling_pos := certificate.coupling_pos
  coupling_le_window := certificate.coupling_le_window
  diagonalOrder := certificate.diagonalOrder
  crossOrder := certificate.crossOrder
  entrywise := fun scale =>
    (certificate.entrywise scale).toEntrywiseEighthData

/-- Named intermediate conversion, kept explicit to make the final scalar
consumer elaborate without a long chained projection. -/
def toAFQuarterCertificate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate
        family law spacing coupling) :
    ExactSlabGroupedAFQuarterCertificate
      family law spacing coupling :=
  certificate.toAFEntrywiseEighthCertificate.toAFQuarterCertificate

/-- The exact AF-uniform scalar budget `r(a) + epsilon(a) <= 1/4`. -/
theorem rate_add_epsilon_le_quarter
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate
        family law spacing coupling) :
    ∀ scale,
      ((certificate.toAFQuarterCertificate.comparison scale).spectral.rate +
        (certificate.toAFQuarterCertificate.comparison scale).epsilon) ≤
        Q'.mkPos 1 4 (by decide) :=
  certificate.toAFQuarterCertificate.rate_add_epsilon_le_quarter

end AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate

end YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison

#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison.exactSlabNormalizationData_allCutoffs
#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison.exactSlabVacuumPartition_eqv_one_allCutoffs
#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison.normalizedExactSlabKernel_allCutoffs_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison.AllCutoffExactSlabGroupedRowSummableEighthData.row_relative_error_le_oneEighth
#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison.AllCutoffExactSlabGroupedRowSummableEighthData.exact_quadratic_abs_le_quarter
#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison.AllCutoffExactSlabGroupedEntrywiseEighthData.exact_quadratic_abs_le_quarter
#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison.AllCutoffExactSlabGroupedAFRowSummableEighthCertificate.rate_add_epsilon_le_quarter
#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison.AllCutoffExactSlabGroupedAFEntrywiseEighthCertificate.rate_add_epsilon_le_quarter
