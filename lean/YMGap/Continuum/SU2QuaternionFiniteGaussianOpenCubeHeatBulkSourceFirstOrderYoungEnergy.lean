/-
# Source first-order control by supported diagonal energies

The actual bulk-source first-order coefficient is already localized to two
four-link physical supports.  The Young-energy estimate for each covariance
LDL residual entry now turns that double sum into a product of supported row
absolute masses and supported diagonal-energy masses.

This is the direct source consumer of the diagonal reduction.  The resulting
quantities are finite and explicit, but no cutoff-uniform bound for their
diagonal energies, ORIGINAL-law comparison, continuum limit, Hamiltonian gap,
or Clay theorem is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLYoungEnergy

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderYoungEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourcePhysicalSupport
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderSupport
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceLDLYoungEnergy

local infix:50 " ≈ " => Q'.eqv
local instance : DecidableEq Nat := Nat.decEq

private theorem listQSum_mono_local {Index : Type}
    (lower upper : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | item :: items, hypothesis =>
      Q'.add_le_add
        (hypothesis item List.mem_cons_self)
        (listQSum_mono_local lower upper items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

private theorem range_nodup_local (count : Nat) :
    (List.range count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ previous induction =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨induction,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightPrevious : right = previous := List.mem_singleton.mp hright
      rw [heq, hrightPrevious] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl previous)

private theorem listQSum_le_length_mul_local {Index : Type}
    (value : Index → Q') {bound : Q'}
    (hboundNonnegative : (0 : Q') ≤ bound) : ∀ items : List Index,
    (∀ item, item ∈ items → value item ≤ bound) →
      listQSum value items ≤ Q'.ofNat items.length * bound
  | [], _ => Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | item :: items, hypothesis => by
      have hhead := hypothesis item List.mem_cons_self
      have htail := listQSum_le_length_mul_local value hboundNonnegative items
        (fun other membership =>
          hypothesis other (List.mem_cons_of_mem item membership))
      refine Q'.le_trans' _ _ _ (Q'.add_le_add hhead htail) ?_
      refine Q'.le_of_eqv (Q'.eqv_symm ?_)
      refine Q'.eqv_trans _ ((Q'.ofNat items.length + 1) * bound) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ bound
          (Q'.ofNat_add_eqv items.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat items.length * bound + (1 : Q') * bound) _
        (Q'.add_mul_eqv (Q'.ofNat items.length) 1 bound) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat items.length * bound + bound) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
        (Q'.add_comm_eqv (Q'.ofNat items.length * bound) bound)

private theorem ldlFactorResidualCoefficient_nonnegative
    {n left right : Nat} {factor : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hpositive : finiteLDLPositiveDiagonalCheck n diagonal = true) :
    (0 : Q') ≤
      ldlFactorResidualCoefficient n factor diagonal left right := by
  unfold ldlFactorResidualCoefficient
  apply listQSum_nonnegative_on
  intro channel hchannel
  apply Q'.mul_nonneg
  · exact CReal.errAt_nonneg (diagonal channel)
      (finiteLDLPositiveDiagonalCheck_pos hpositive
        (List.mem_range.mp hchannel)) 0
  · exact Q'.abs_nonneg _

private theorem ldlFactorResidualDiagonalEnergy_nonnegative
    {n row : Nat} {factor : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hpositive : finiteLDLPositiveDiagonalCheck n diagonal = true) :
    (0 : Q') ≤
      ldlFactorResidualDiagonalEnergy n factor diagonal row := by
  unfold ldlFactorResidualDiagonalEnergy
  apply listQSum_nonnegative_on
  intro channel hchannel
  apply Q'.mul_nonneg
  · exact CReal.errAt_nonneg (diagonal channel)
      (finiteLDLPositiveDiagonalCheck_pos hpositive
        (List.mem_range.mp hchannel)) 0
  · exact YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _

private theorem internalBoundaryCoefficient_abs_le_one
    (face : Z4Plaq) (link : Z4Link) :
    Q'.abs (internalBoundaryCoefficient face link) ≤ 1 := by
  unfold internalBoundaryCoefficient
    BF4U1SameCarrierPushforward.orientedBoundaryCoefficient
  by_cases hfirst : link = (face.1, (dirsOf face.2).1)
  · rw [if_pos hfirst]
    decide
  · by_cases hsecond : link = (face.1, (dirsOf face.2).2)
    · rw [if_neg hfirst, if_pos hsecond]
      decide
    · by_cases hthird :
        link = (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
      · rw [if_neg hfirst, if_neg hsecond, if_pos hthird]
        decide
      · by_cases hfourth :
          link = (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
        · rw [if_neg hfirst, if_neg hsecond, if_neg hthird,
            if_pos hfourth]
          decide
        · rw [if_neg hfirst, if_neg hsecond, if_neg hthird,
            if_neg hfourth]
          decide

private theorem combGaugeCurl_abs_le_one
    (width faceIndex gaugeIndex : Nat) :
    Q'.abs (combGaugeCurl width faceIndex gaugeIndex) ≤ 1 := by
  unfold combGaugeCurl
  by_cases hvalid : faceIndex < internalOpenCubeFaceCount width ∧
      gaugeIndex < combGaugeEdgeCount width
  · rw [if_pos hvalid]
    exact internalBoundaryCoefficient_abs_le_one _ _
  · rw [if_neg hvalid]
    decide

private theorem bulkSourcePhysicalColorCurlRow_abs_le_one
    (side time rowIndex coordinate : Nat) :
    Q'.abs (bulkSourcePhysicalColorCurlRow
      side time rowIndex coordinate) ≤ 1 := by
  unfold bulkSourcePhysicalColorCurlRow combGaugeFreeHistoryCurlRow
  by_cases htime : historyTime
      (combGaugeEdgeCount (bulkSourceWidth side)) coordinate = time
  · rw [if_pos htime]
    exact combGaugeCurl_abs_le_one _ _ _
  · rw [if_neg htime]
    decide

/-- Absolute mass of a row on an explicitly supplied finite support. -/
def finiteRowSupportAbsMass
    (row : Nat → Q') (support : List Nat) : Q' :=
  listQSum (fun coordinate => Q'.abs (row coordinate)) support

/-- Absolute-row-weighted diagonal residual energy on an explicit support. -/
def finiteRowSupportDiagonalEnergyMass
    (n : Nat) (factor : Nat → Nat → Q') (diagonal : Nat → Q')
    (row : Nat → Q') (support : List Nat) : Q' :=
  listQSum
    (fun coordinate =>
      Q'.abs (row coordinate) *
        ldlFactorResidualDiagonalEnergy n factor diagonal coordinate)
    support

/-- Unweighted diagonal residual energy on an explicitly supplied support. -/
def finiteSupportDiagonalEnergySum
    (n : Nat) (factor : Nat → Nat → Q') (diagonal : Nat → Q')
    (support : List Nat) : Q' :=
  listQSum
    (fun coordinate =>
      ldlFactorResidualDiagonalEnergy n factor diagonal coordinate)
    support

theorem bulkSourcePhysicalColorCurlSupportedCoordinates_nodup
    (timeBonds side time rowIndex : Nat) :
    (bulkSourcePhysicalColorCurlSupportedCoordinates
      timeBonds side time rowIndex).Nodup := by
  unfold bulkSourcePhysicalColorCurlSupportedCoordinates
  exact List.filter_sublist.nodup (range_nodup_local _)

theorem bulkSourcePhysicalColorCurlSupportedCoordinates_subset_candidates
    {timeBonds side time rowIndex coordinate : Nat}
    (hmembership : coordinate ∈
      bulkSourcePhysicalColorCurlSupportedCoordinates
        timeBonds side time rowIndex) :
    coordinate ∈ bulkSourcePhysicalColorCurlCandidateCoordinates
      side time rowIndex :=
  (bulkSourcePhysicalColorCurlSupportedCoordinates_mem hmembership).2

theorem bulkSourcePhysicalColorCurlSupportedCoordinates_length_le_four
    (timeBonds side time rowIndex : Nat) :
    (bulkSourcePhysicalColorCurlSupportedCoordinates
      timeBonds side time rowIndex).length ≤ 4 := by
  have hnodup :
      (bulkSourcePhysicalColorCurlSupportedCoordinates
        timeBonds side time rowIndex).Nodup := by
    exact bulkSourcePhysicalColorCurlSupportedCoordinates_nodup
      timeBonds side time rowIndex
  have hsubset : ∀ coordinate,
      coordinate ∈ bulkSourcePhysicalColorCurlSupportedCoordinates
          timeBonds side time rowIndex →
        coordinate ∈ bulkSourcePhysicalColorCurlCandidateCoordinates
          side time rowIndex := by
    intro coordinate hcoordinate
    exact bulkSourcePhysicalColorCurlSupportedCoordinates_subset_candidates
      hcoordinate
  have hlength := @CayleyPruferInjection.nodup_subset_length_le
    Nat Nat.decEq
    (bulkSourcePhysicalColorCurlSupportedCoordinates
      timeBonds side time rowIndex)
    (bulkSourcePhysicalColorCurlCandidateCoordinates side time rowIndex)
    hnodup hsubset
  simpa only [bulkSourcePhysicalColorCurlCandidateCoordinates_length]
    using hlength

/-- Every actual source row has supported absolute mass at most four. -/
theorem bulkSourcePhysicalColorCurlSupportAbsMass_le_four
    (timeBonds side time rowIndex : Nat) :
    finiteRowSupportAbsMass
        (bulkSourcePhysicalColorCurlRow side time rowIndex)
        (bulkSourcePhysicalColorCurlSupportedCoordinates
          timeBonds side time rowIndex) ≤ 4 := by
  unfold finiteRowSupportAbsMass
  let support := bulkSourcePhysicalColorCurlSupportedCoordinates
    timeBonds side time rowIndex
  have hsum := listQSum_le_length_mul_local
    (fun coordinate => Q'.abs
      (bulkSourcePhysicalColorCurlRow side time rowIndex coordinate))
    Q'.zero_le_one support
    (fun coordinate _ =>
      bulkSourcePhysicalColorCurlRow_abs_le_one
        side time rowIndex coordinate)
  refine Q'.le_trans' _ _ _ hsum ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.ofNat support.length))) ?_
  exact Q'.ofNat_le_ofNat
    (bulkSourcePhysicalColorCurlSupportedCoordinates_length_le_four
      timeBonds side time rowIndex)

/-- Dropping the source-row absolute coefficient only enlarges its supported
diagonal-energy mass. -/
theorem bulkSourcePhysicalColorCurlSupportDiagonalEnergyMass_le_sum
    (timeBonds side time rowIndex : Nat) :
    let n := historyCoordinateCount timeBonds
      (combGaugeEdgeCount (bulkSourceWidth side))
    let data := combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds (bulkSourceWidth side)
    let row := bulkSourcePhysicalColorCurlRow side time rowIndex
    let support := bulkSourcePhysicalColorCurlSupportedCoordinates
      timeBonds side time rowIndex
    finiteRowSupportDiagonalEnergyMass
        n data.lower data.diagonal row support ≤
      finiteSupportDiagonalEnergySum
        n data.lower data.diagonal support := by
  dsimp only
  unfold finiteRowSupportDiagonalEnergyMass finiteSupportDiagonalEnergySum
  apply listQSum_mono_local
  intro coordinate _
  let energy := ldlFactorResidualDiagonalEnergy
    (historyCoordinateCount timeBonds
      (combGaugeEdgeCount (bulkSourceWidth side)))
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds (bulkSourceWidth side)).lower
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds (bulkSourceWidth side)).diagonal coordinate
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ energy
      (bulkSourcePhysicalColorCurlRow_abs_le_one
        side time rowIndex coordinate)
      (ldlFactorResidualDiagonalEnergy_nonnegative
        (combGaugeHeatFreeHistoryCovariancePositiveLDL_diagonal_check
          timeBonds (bulkSourceWidth side)))) ?_
  exact Q'.le_of_eqv (Q'.one_mul_eqv energy)

private theorem nestedYoungEnvelope_eq
    (n : Nat) (factor : Nat → Nat → Q') (diagonal : Nat → Q')
    (leftRow rightRow : Nat → Q')
    (leftSupport rightSupport : List Nat) :
    listQSum
        (fun left => listQSum
          (fun right =>
            half *
              (((Q'.abs (leftRow left) *
                    ldlFactorResidualDiagonalEnergy
                      n factor diagonal left) *
                  Q'.abs (rightRow right)) +
                (Q'.abs (leftRow left) *
                  (Q'.abs (rightRow right) *
                    ldlFactorResidualDiagonalEnergy
                      n factor diagonal right))))
          rightSupport)
        leftSupport ≈
      half *
        (finiteRowSupportDiagonalEnergyMass
              n factor diagonal leftRow leftSupport *
            finiteRowSupportAbsMass rightRow rightSupport +
          finiteRowSupportAbsMass leftRow leftSupport *
            finiteRowSupportDiagonalEnergyMass
              n factor diagonal rightRow rightSupport) := by
  refine Q'.eqv_trans _ _ _
    (listQSum_congr_on
      (fun left => listQSum
        (fun right =>
          half *
            (((Q'.abs (leftRow left) *
                  ldlFactorResidualDiagonalEnergy
                    n factor diagonal left) *
                Q'.abs (rightRow right)) +
              (Q'.abs (leftRow left) *
                (Q'.abs (rightRow right) *
                  ldlFactorResidualDiagonalEnergy
                    n factor diagonal right))))
        rightSupport)
      (fun left =>
        half *
          ((Q'.abs (leftRow left) *
                ldlFactorResidualDiagonalEnergy
                  n factor diagonal left) *
              finiteRowSupportAbsMass rightRow rightSupport +
            Q'.abs (leftRow left) *
              finiteRowSupportDiagonalEnergyMass
                n factor diagonal rightRow rightSupport))
      leftSupport (fun left _ => ?_)) ?_
  · refine Q'.eqv_trans _ _ _
      (listQSum_mul_left half
        (fun right =>
          ((Q'.abs (leftRow left) *
                ldlFactorResidualDiagonalEnergy
                  n factor diagonal left) *
              Q'.abs (rightRow right)) +
            (Q'.abs (leftRow left) *
              (Q'.abs (rightRow right) *
                ldlFactorResidualDiagonalEnergy
                  n factor diagonal right)))
        rightSupport) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left half _ _
        (listQSum_add
          (fun right =>
            (Q'.abs (leftRow left) *
                ldlFactorResidualDiagonalEnergy
                  n factor diagonal left) *
              Q'.abs (rightRow right))
          (fun right =>
            Q'.abs (leftRow left) *
              (Q'.abs (rightRow right) *
                ldlFactorResidualDiagonalEnergy
                  n factor diagonal right))
          rightSupport)) ?_
    exact Q'.mul_eqv_congr_left half _ _
      (Q'.add_eqv_congr'
        (listQSum_mul_left
          (Q'.abs (leftRow left) *
            ldlFactorResidualDiagonalEnergy n factor diagonal left)
          (fun right => Q'.abs (rightRow right)) rightSupport)
        (listQSum_mul_left (Q'.abs (leftRow left))
          (fun right =>
            Q'.abs (rightRow right) *
              ldlFactorResidualDiagonalEnergy
                n factor diagonal right)
          rightSupport))
  · refine Q'.eqv_trans _ _ _
      (listQSum_mul_left half
        (fun left =>
          (Q'.abs (leftRow left) *
                ldlFactorResidualDiagonalEnergy
                  n factor diagonal left) *
              finiteRowSupportAbsMass rightRow rightSupport +
            Q'.abs (leftRow left) *
              finiteRowSupportDiagonalEnergyMass
                n factor diagonal rightRow rightSupport)
        leftSupport) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left half _ _
        (listQSum_add
          (fun left =>
            (Q'.abs (leftRow left) *
                ldlFactorResidualDiagonalEnergy
                  n factor diagonal left) *
              finiteRowSupportAbsMass rightRow rightSupport)
          (fun left =>
            Q'.abs (leftRow left) *
              finiteRowSupportDiagonalEnergyMass
                n factor diagonal rightRow rightSupport)
          leftSupport)) ?_
    exact Q'.mul_eqv_congr_left half _ _
      (Q'.add_eqv_congr'
        (listQSum_mul_right
          (fun left =>
            Q'.abs (leftRow left) *
              ldlFactorResidualDiagonalEnergy n factor diagonal left)
          (finiteRowSupportAbsMass rightRow rightSupport) leftSupport)
        (listQSum_mul_right
          (fun left => Q'.abs (leftRow left))
          (finiteRowSupportDiagonalEnergyMass
            n factor diagonal rightRow rightSupport)
          leftSupport))

/-- A finite row-pair residual envelope is controlled by the product of the
two support masses and diagonal-energy masses. -/
theorem finiteSupportedResidualEnvelope_le_youngEnergy
    {n : Nat} {factor : Nat → Nat → Q'} {diagonal : Nat → Q'}
    (hpositive : finiteLDLPositiveDiagonalCheck n diagonal = true)
    (leftRow rightRow : Nat → Q')
    (leftSupport rightSupport : List Nat) :
    listQSum
        (fun left => listQSum
          (fun right =>
            Q'.abs (leftRow left * rightRow right) *
              ldlFactorResidualCoefficient
                n factor diagonal left right)
          rightSupport)
        leftSupport ≤
      half *
        (finiteRowSupportDiagonalEnergyMass
              n factor diagonal leftRow leftSupport *
            finiteRowSupportAbsMass rightRow rightSupport +
          finiteRowSupportAbsMass leftRow leftSupport *
            finiteRowSupportDiagonalEnergyMass
              n factor diagonal rightRow rightSupport) := by
  let upper := fun left right =>
    half *
      (((Q'.abs (leftRow left) *
            ldlFactorResidualDiagonalEnergy n factor diagonal left) *
          Q'.abs (rightRow right)) +
        (Q'.abs (leftRow left) *
          (Q'.abs (rightRow right) *
            ldlFactorResidualDiagonalEnergy n factor diagonal right)))
  have hsum :
      listQSum
          (fun left => listQSum
            (fun right =>
              Q'.abs (leftRow left * rightRow right) *
                ldlFactorResidualCoefficient
                  n factor diagonal left right)
            rightSupport)
          leftSupport ≤
        listQSum
          (fun left => listQSum (upper left) rightSupport)
          leftSupport := by
    apply listQSum_mono_local
    intro left _
    apply listQSum_mono_local
    intro right _
    let coefficient :=
      ldlFactorResidualCoefficient n factor diagonal left right
    let leftEnergy :=
      ldlFactorResidualDiagonalEnergy n factor diagonal left
    let rightEnergy :=
      ldlFactorResidualDiagonalEnergy n factor diagonal right
    have hrowProduct :
        Q'.abs (leftRow left * rightRow right) ≤
          Q'.abs (leftRow left) * Q'.abs (rightRow right) :=
      ExpNeg.abs_mul_le _ _
    have hcoefficient :
        coefficient ≤ half * (leftEnergy + rightEnergy) :=
      ldlFactorResidualCoefficient_le_diagonalEnergy_average hpositive
    have hfirst :
        Q'.abs (leftRow left * rightRow right) * coefficient ≤
          (Q'.abs (leftRow left) * Q'.abs (rightRow right)) *
            coefficient :=
      Q'.mul_le_mul_of_nonneg_right _ _ coefficient hrowProduct
        (ldlFactorResidualCoefficient_nonnegative hpositive)
    have hsecond :
        (Q'.abs (leftRow left) * Q'.abs (rightRow right)) *
            coefficient ≤
          (Q'.abs (leftRow left) * Q'.abs (rightRow right)) *
            (half * (leftEnergy + rightEnergy)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hcoefficient
        (Q'.mul_nonneg _ _ (Q'.abs_nonneg _) (Q'.abs_nonneg _))
    refine Q'.le_trans' _ _ _ hfirst (Q'.le_trans' _ _ _ hsecond ?_)
    unfold upper
    exact Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1))
          (.mul (.var 2) (.add (.var 3) (.var 4))))
        (.mul (.var 2)
          (.add (.mul (.mul (.var 0) (.var 3)) (.var 1))
            (.mul (.var 0) (.mul (.var 1) (.var 4)))))
        (by decide) (fun
          | 0 => Q'.abs (leftRow left)
          | 1 => Q'.abs (rightRow right)
          | 2 => half
          | 3 => leftEnergy
          | _ => rightEnergy))
  refine Q'.le_trans' _ _ _ hsum ?_
  exact Q'.le_of_eqv
    (nestedYoungEnvelope_eq n factor diagonal
      leftRow rightRow leftSupport rightSupport)

/-- The actual source first-order coefficient is controlled by the supported
absolute masses and supported diagonal-energy masses of its two physical curl
rows. -/
theorem bulkSourceHeatActionScalingFirstOrderCoefficient_le_youngEnergy
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat)
    (hleftRowIndex :
      leftRowIndex < 3 * (bulkSourceFaces side).length)
    (hrightRowIndex :
      rightRowIndex < 3 * (bulkSourceFaces side).length) :
    let n := historyCoordinateCount timeBonds
      (combGaugeEdgeCount (bulkSourceWidth side))
    let data := combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds (bulkSourceWidth side)
    let leftRow := bulkSourcePhysicalColorCurlRow
      side leftTime leftRowIndex
    let rightRow := bulkSourcePhysicalColorCurlRow
      side rightTime rightRowIndex
    let leftSupport := bulkSourcePhysicalColorCurlSupportedCoordinates
      timeBonds side leftTime leftRowIndex
    let rightSupport := bulkSourcePhysicalColorCurlSupportedCoordinates
      timeBonds side rightTime rightRowIndex
    bulkSourceHeatActionScalingFirstOrderCoefficient
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex ≤
      half *
        (finiteRowSupportDiagonalEnergyMass
              n data.lower data.diagonal leftRow leftSupport *
            finiteRowSupportAbsMass rightRow rightSupport +
          finiteRowSupportAbsMass leftRow leftSupport *
            finiteRowSupportDiagonalEnergyMass
              n data.lower data.diagonal rightRow rightSupport) := by
  dsimp only
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (bulkSourceHeatActionScalingFirstOrderCoefficient_eq_support
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex
        hleftRowIndex hrightRowIndex)) ?_
  exact finiteSupportedResidualEnvelope_le_youngEnergy
    (combGaugeHeatFreeHistoryCovariancePositiveLDL_diagonal_check
      timeBonds (bulkSourceWidth side))
    (bulkSourcePhysicalColorCurlRow side leftTime leftRowIndex)
    (bulkSourcePhysicalColorCurlRow side rightTime rightRowIndex)
    (bulkSourcePhysicalColorCurlSupportedCoordinates
      timeBonds side leftTime leftRowIndex)
    (bulkSourcePhysicalColorCurlSupportedCoordinates
      timeBonds side rightTime rightRowIndex)

/-- Four-link source geometry removes the row-mass factors entirely: the
first-order coefficient is at most twice the sum of the two supported
diagonal-energy sums. -/
theorem bulkSourceHeatActionScalingFirstOrderCoefficient_le_two_energySums
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat)
    (hleftRowIndex :
      leftRowIndex < 3 * (bulkSourceFaces side).length)
    (hrightRowIndex :
      rightRowIndex < 3 * (bulkSourceFaces side).length) :
    let n := historyCoordinateCount timeBonds
      (combGaugeEdgeCount (bulkSourceWidth side))
    let data := combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds (bulkSourceWidth side)
    let leftSupport := bulkSourcePhysicalColorCurlSupportedCoordinates
      timeBonds side leftTime leftRowIndex
    let rightSupport := bulkSourcePhysicalColorCurlSupportedCoordinates
      timeBonds side rightTime rightRowIndex
    bulkSourceHeatActionScalingFirstOrderCoefficient
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex ≤
      2 *
        (finiteSupportDiagonalEnergySum
              n data.lower data.diagonal leftSupport +
          finiteSupportDiagonalEnergySum
            n data.lower data.diagonal rightSupport) := by
  dsimp only
  let n := historyCoordinateCount timeBonds
    (combGaugeEdgeCount (bulkSourceWidth side))
  let data := combGaugeHeatFreeHistoryCovariancePositiveLDL
    timeBonds (bulkSourceWidth side)
  let leftRow := bulkSourcePhysicalColorCurlRow
    side leftTime leftRowIndex
  let rightRow := bulkSourcePhysicalColorCurlRow
    side rightTime rightRowIndex
  let leftSupport := bulkSourcePhysicalColorCurlSupportedCoordinates
    timeBonds side leftTime leftRowIndex
  let rightSupport := bulkSourcePhysicalColorCurlSupportedCoordinates
    timeBonds side rightTime rightRowIndex
  let leftEnergyMass := finiteRowSupportDiagonalEnergyMass
    n data.lower data.diagonal leftRow leftSupport
  let rightEnergyMass := finiteRowSupportDiagonalEnergyMass
    n data.lower data.diagonal rightRow rightSupport
  let leftEnergySum := finiteSupportDiagonalEnergySum
    n data.lower data.diagonal leftSupport
  let rightEnergySum := finiteSupportDiagonalEnergySum
    n data.lower data.diagonal rightSupport
  let leftAbsMass := finiteRowSupportAbsMass leftRow leftSupport
  let rightAbsMass := finiteRowSupportAbsMass rightRow rightSupport
  have hsource :=
    bulkSourceHeatActionScalingFirstOrderCoefficient_le_youngEnergy
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex
      hleftRowIndex hrightRowIndex
  have hleftEnergy : leftEnergyMass ≤ leftEnergySum := by
    exact bulkSourcePhysicalColorCurlSupportDiagonalEnergyMass_le_sum
      timeBonds side leftTime leftRowIndex
  have hrightEnergy : rightEnergyMass ≤ rightEnergySum := by
    exact bulkSourcePhysicalColorCurlSupportDiagonalEnergyMass_le_sum
      timeBonds side rightTime rightRowIndex
  have hleftMass : leftAbsMass ≤ 4 := by
    exact bulkSourcePhysicalColorCurlSupportAbsMass_le_four
      timeBonds side leftTime leftRowIndex
  have hrightMass : rightAbsMass ≤ 4 := by
    exact bulkSourcePhysicalColorCurlSupportAbsMass_le_four
      timeBonds side rightTime rightRowIndex
  have hleftEnergyNonnegative : (0 : Q') ≤ leftEnergySum := by
    unfold leftEnergySum finiteSupportDiagonalEnergySum
    apply listQSum_nonnegative_on
    intro coordinate _
    exact ldlFactorResidualDiagonalEnergy_nonnegative
      (combGaugeHeatFreeHistoryCovariancePositiveLDL_diagonal_check
        timeBonds (bulkSourceWidth side))
  have hrightEnergyNonnegative : (0 : Q') ≤ rightEnergySum := by
    unfold rightEnergySum finiteSupportDiagonalEnergySum
    apply listQSum_nonnegative_on
    intro coordinate _
    exact ldlFactorResidualDiagonalEnergy_nonnegative
      (combGaugeHeatFreeHistoryCovariancePositiveLDL_diagonal_check
        timeBonds (bulkSourceWidth side))
  have hleftEnergyMassNonnegative : (0 : Q') ≤ leftEnergyMass := by
    unfold leftEnergyMass finiteRowSupportDiagonalEnergyMass
    apply listQSum_nonnegative_on
    intro coordinate _
    exact Q'.mul_nonneg _ _ (Q'.abs_nonneg _)
      (ldlFactorResidualDiagonalEnergy_nonnegative
        (combGaugeHeatFreeHistoryCovariancePositiveLDL_diagonal_check
          timeBonds (bulkSourceWidth side)))
  have hrightEnergyMassNonnegative : (0 : Q') ≤ rightEnergyMass := by
    unfold rightEnergyMass finiteRowSupportDiagonalEnergyMass
    apply listQSum_nonnegative_on
    intro coordinate _
    exact Q'.mul_nonneg _ _ (Q'.abs_nonneg _)
      (ldlFactorResidualDiagonalEnergy_nonnegative
        (combGaugeHeatFreeHistoryCovariancePositiveLDL_diagonal_check
          timeBonds (bulkSourceWidth side)))
  have hleftMassNonnegative : (0 : Q') ≤ leftAbsMass := by
    unfold leftAbsMass finiteRowSupportAbsMass
    apply listQSum_nonnegative_on
    intro coordinate _
    exact Q'.abs_nonneg _
  have hrightMassNonnegative : (0 : Q') ≤ rightAbsMass := by
    unfold rightAbsMass finiteRowSupportAbsMass
    apply listQSum_nonnegative_on
    intro coordinate _
    exact Q'.abs_nonneg _
  have hfirstProduct :
      leftEnergyMass * rightAbsMass ≤ leftEnergySum * 4 :=
    Q'.mul_le_mul_of_nonneg hleftEnergy hrightMass
      hleftEnergyNonnegative hrightMassNonnegative
  have hsecondProduct :
      leftAbsMass * rightEnergyMass ≤ 4 * rightEnergySum :=
    Q'.mul_le_mul_of_nonneg hleftMass hrightEnergy
      (by decide) hrightEnergyMassNonnegative
  have hinside :
      leftEnergyMass * rightAbsMass +
          leftAbsMass * rightEnergyMass ≤
        leftEnergySum * 4 + 4 * rightEnergySum :=
    Q'.add_le_add hfirstProduct hsecondProduct
  have hscaled :
      half *
          (leftEnergyMass * rightAbsMass +
            leftAbsMass * rightEnergyMass) ≤
        half * (leftEnergySum * 4 + 4 * rightEnergySum) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hinside half_nonneg
  refine Q'.le_trans' _ _ _ hsource (Q'.le_trans' _ _ _ hscaled ?_)
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ ((half * 4) *
        (leftEnergySum + rightEnergySum)) _
      (poly_identity_of_normal_eq
        (.mul (.var 0)
          (.add (.mul (.var 1) (.const 4))
            (.mul (.const 4) (.var 2))))
        (.mul (.mul (.var 0) (.const 4))
          (.add (.var 1) (.var 2)))
        (by decide) (fun
          | 0 => half
          | 1 => leftEnergySum
          | _ => rightEnergySum))
      (Q'.mul_eqv_congr_right (half * 4) 2
        (leftEnergySum + rightEnergySum) (by decide)))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderYoungEnergy

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderYoungEnergy.finiteSupportedResidualEnvelope_le_youngEnergy
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderYoungEnergy.bulkSourceHeatActionScalingFirstOrderCoefficient_le_youngEnergy
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderYoungEnergy.bulkSourcePhysicalColorCurlSupportedCoordinates_length_le_four
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderYoungEnergy.bulkSourcePhysicalColorCurlSupportAbsMass_le_four
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderYoungEnergy.bulkSourceHeatActionScalingFirstOrderCoefficient_le_two_energySums
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderYoungEnergy.bulkSourcePhysicalColorCurlSupportedCoordinates_nodup
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderYoungEnergy.bulkSourcePhysicalColorCurlSupportedCoordinates_subset_candidates
