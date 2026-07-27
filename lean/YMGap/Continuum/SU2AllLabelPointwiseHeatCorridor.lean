/-
# SU(2) all-label pointwise heat corridor

The rational constants used by the BF4 grouped Harnack ledger originate in
the following elementary character estimate.  On the class coordinate
`x ∈ [-1,1]` and for `0 ≤ w ≤ 1/2`, the doubled-label heat term

    coeffW w n * Cheb.U n x

has absolute value at most

    (n+1)^2 * w^(n(n+2)).

The label-one majorant is at most `1/2`.  Starting at label two, the
majorants have ratio at most

    (4/3)^2 * (1/2)^7 = 1/72,

and head `9/256`; hence every finite tail is bounded by

    (9/256) / (1 - 1/72) = 81/2272.

Adding the vacuum term gives the exact finite-partial pointwise corridor

    1055/2272 ≤ heatPartial ≤ 3489/2272.

Honest scope: this file proves the corridor for every finite character
partial sum.  It does not identify such a class kernel with any one of the
23 retained BF4 slab factors, does not construct the BF4 conditional path
carrier, and does not silently turn finite-partial control into a continuum
`CReal` heat kernel.  Those are separate identification/completion steps.

## Axiom gate

Only exact `Q'` arithmetic, finite sums, and the proved constructive
Chebyshev bound are used.  There is no `Classical.*`, `Real`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4GroupedFeynmanKacHarnack
import YMGap.Continuum.BF4RetainedKineticWindow
import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.ChebyshevU
import YMGap.Constructive.CornerBound

namespace YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.BF4RetainedKineticWindow
open YMGap.Continuum.BF4RetainedPathConditionalOrder
open YMGap.Continuum.GroupedAllLabelHaarRefresh

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact constants and the pointwise finite partial -/

def half : Q' := Q'.mkPos 1 2 (by decide)
def sixteenNinths : Q' := Q'.mkPos 16 9 (by decide)
def sharpTailRatio : Q' := Q'.mkPos 1 72 (by decide)
def labelTwoHead : Q' := Q'.mkPos 9 256 (by decide)
def allLabelTailBudget : Q' := Q'.mkPos 81 2272 (by decide)
def allLabelExcitedBudget : Q' := Q'.mkPos 1217 2272 (by decide)

/-- One doubled-label central heat-character term. -/
def pointwiseHeatTerm (w x : Q') (label : Nat) : Q' :=
  coeffW w label * Cheb.U label x

/-- The finite heat partial containing labels `0`, `1`, and
`2, ..., M+1`. -/
def pointwiseHeatPartial (w x : Q') (M : Nat) : Q' :=
  (1 : Q') + pointwiseHeatTerm w x 1 +
    finSum (fun k => pointwiseHeatTerm w x (2 + k)) M

/-- The usual prefix notation, summing labels `0, ..., cutoff-1`. -/
def standardPointwiseHeatPartial
    (w x : Q') (cutoff : Nat) : Q' :=
  finSum (pointwiseHeatTerm w x) cutoff

/-- The positive absolute majorant of one pointwise heat term. -/
def pointwiseHeatMajorant (w : Q') (label : Nat) : Q' :=
  tailTerm w 2 label

theorem sharpTailRatio_nonnegative :
    (0 : Q') ≤ sharpTailRatio := by
  decide

theorem allLabelTailBudget_nonnegative :
    (0 : Q') ≤ allLabelTailBudget := by
  decide

theorem exact_geometric_closure :
    labelTwoHead + sharpTailRatio * allLabelTailBudget ≤
      allLabelTailBudget := by
  decide

private theorem pointwiseHeatTerm_zero_eqv_one
    (w x : Q') :
    pointwiseHeatTerm w x 0 ≈ (1 : Q') := by
  unfold pointwiseHeatTerm
  rw [coeffW_zero]
  change (1 : Q') * 1 ≈ 1
  exact Q'.one_mul_eqv 1

private theorem finSum_split_local
    (f : Nat → Q') (N : Nat) :
    ∀ M,
      finSum f (N + M) ≈
        finSum f N + finSum (fun k => f (N + k)) M
  | 0 => by
      rw [Nat.add_zero, finSum_zero, Q'.add_zero']
      exact Q'.eqv_refl _
  | M + 1 => by
      have ih := finSum_split_local f N M
      show
        finSum f (N + M) + f (N + M) ≈
          finSum f N +
            (finSum (fun k => f (N + k)) M +
              f (N + M))
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih)
        (Q'.add_assoc_eqv _ _ _)

/-- The displayed `0 + 1 + tail` partial is exactly the ordinary character
prefix of length `M+2`. -/
theorem standardPointwiseHeatPartial_eqv
    (w x : Q') (M : Nat) :
    standardPointwiseHeatPartial w x (2 + M) ≈
      pointwiseHeatPartial w x M := by
  have hsplit :=
    finSum_split_local
      (pointwiseHeatTerm w x) 2 M
  refine Q'.eqv_trans _ _ _ hsplit ?_
  unfold pointwiseHeatPartial
  apply Q'.add_eqv_congr_right
  change
    ((0 : Q') + pointwiseHeatTerm w x 0) +
        pointwiseHeatTerm w x 1 ≈
      (1 : Q') + pointwiseHeatTerm w x 1
  apply Q'.add_eqv_congr_right
  rw [Q'.zero_add']
  exact pointwiseHeatTerm_zero_eqv_one w x

/-! ## 2. The sharp label-two ratio -/

private theorem sharp_poly_nat
    (label : Nat) (hlabel : 2 ≤ label) :
    9 * (label + 2) ^ 2 ≤ 16 * (label + 1) ^ 2 := by
  have hlinear : 3 * (label + 2) ≤ 4 * (label + 1) := by
    omega
  have hsquare := Nat.pow_le_pow_left hlinear 2
  simpa [Nat.mul_pow, Nat.pow_two, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using hsquare

private theorem sharp_poly_q
    (label : Nat) (hlabel : 2 ≤ label) :
    Q'.ofNat ((label + 2) ^ 2) ≤
      sixteenNinths * Q'.ofNat ((label + 1) ^ 2) := by
  have hnat := sharp_poly_nat label hlabel
  show
    (Q'.ofNat ((label + 2) ^ 2)).num *
          ((sixteenNinths *
            Q'.ofNat ((label + 1) ^ 2)).den : Int) ≤
      (sixteenNinths *
          Q'.ofNat ((label + 1) ^ 2)).num *
        ((Q'.ofNat ((label + 2) ^ 2)).den : Int)
  have hleftNum :
      (Q'.ofNat ((label + 2) ^ 2)).num =
        (((label + 2) ^ 2 : Nat) : Int) := rfl
  have hleftDen :
      ((Q'.ofNat ((label + 2) ^ 2)).den : Int) = 1 := rfl
  have hrightNum :
      (sixteenNinths *
          Q'.ofNat ((label + 1) ^ 2)).num =
        (16 : Int) * (((label + 1) ^ 2 : Nat) : Int) := rfl
  have hrightDen :
      ((sixteenNinths *
          Q'.ofNat ((label + 1) ^ 2)).den : Int) = 9 := by
    unfold sixteenNinths
    rw [Q'.mul_den_cast]
    rfl
  rw [hleftNum, hleftDen, hrightNum, hrightDen,
    Int.mul_one]
  have hnat' :
      (label + 2) ^ 2 * 9 ≤
        16 * (label + 1) ^ 2 := by
    simpa only [Nat.mul_comm] using hnat
  exact_mod_cast hnat'

private theorem half_gain_le_seventh
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (label : Nat) (hlabel : 2 ≤ label) :
    qpow w (2 * label + 3) ≤ qpow half 7 := by
  have hbase :
      qpow w (2 * label + 3) ≤
        qpow half (2 * label + 3) :=
    qpow_mono hw0 hw (2 * label + 3)
  have hexponent :
      qpow half (2 * label + 3) ≤ qpow half 7 :=
    qpow_antitone (by decide) (by decide) 7
      (2 * label + 3) (by omega)
  exact Q'.le_trans' _ _ _ hbase hexponent

private theorem sharp_ratio_constant :
    sixteenNinths * qpow half 7 ≈ sharpTailRatio := by
  decide

/-- **Sharp all-label majorant ratio.**  Past doubled label two, the exact
polynomial ratio and the seven-power Casimir gain give `1/72`. -/
theorem pointwiseHeatMajorant_succ_le
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (label : Nat) (hlabel : 2 ≤ label) :
    pointwiseHeatMajorant w (label + 1) ≤
      sharpTailRatio * pointwiseHeatMajorant w label := by
  have hw1 : w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hw (by decide)
  have hc :
      c4 (label + 1) = c4 label + (2 * label + 3) :=
    c4_succ label
  unfold pointwiseHeatMajorant tailTerm
  rw [hc]
  have hsplit :
      qpow w (c4 label + (2 * label + 3)) ≈
        qpow w (c4 label) * qpow w (2 * label + 3) :=
    qpow_add w (c4 label) (2 * label + 3)
  have hpoly := sharp_poly_q label hlabel
  have hgain := half_gain_le_seventh hw0 hw label hlabel
  have hpowNonnegative :
      (0 : Q') ≤
        qpow w (c4 label) * qpow w (2 * label + 3) :=
    Q'.mul_nonneg _ _
      (qpow_nonneg w hw0 (c4 label))
      (qpow_nonneg w hw0 (2 * label + 3))
  have hpolyScaled :
      Q'.ofNat ((label + 1 + 1) ^ 2) *
          (qpow w (c4 label) *
            qpow w (2 * label + 3)) ≤
        (sixteenNinths *
            Q'.ofNat ((label + 1) ^ 2)) *
          (qpow w (c4 label) *
            qpow w (2 * label + 3)) := by
    have hindex :
        label + 1 + 1 = label + 2 := by
      omega
    rw [hindex]
    exact Q'.mul_le_mul_of_nonneg_right
      _ _ _ hpoly hpowNonnegative
  have hcoefficientNonnegative :
      (0 : Q') ≤
        sixteenNinths * Q'.ofNat ((label + 1) ^ 2) :=
    Q'.mul_nonneg _ _ (by decide) (zero_le_ofNat _)
  have hbasePowerNonnegative :
      (0 : Q') ≤ qpow w (c4 label) :=
    qpow_nonneg w hw0 (c4 label)
  have hgainScaled :
      (sixteenNinths *
          Q'.ofNat ((label + 1) ^ 2)) *
        (qpow w (c4 label) *
          qpow w (2 * label + 3)) ≤
      (sixteenNinths *
          Q'.ofNat ((label + 1) ^ 2)) *
        (qpow w (c4 label) * qpow half 7) := by
    apply Q'.mul_le_mul_of_nonneg_left
    · exact Q'.mul_le_mul_of_nonneg_left
        _ _ _ hgain hbasePowerNonnegative
    · exact hcoefficientNonnegative
  have hleftEqv :
      Q'.ofNat ((label + 1 + 1) ^ 2) *
          qpow w (c4 label + (2 * label + 3)) ≈
        Q'.ofNat ((label + 1 + 1) ^ 2) *
          (qpow w (c4 label) *
            qpow w (2 * label + 3)) :=
    Q'.mul_eqv_congr_left _ _ _ hsplit
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv hleftEqv)
    (Q'.le_trans' _ _ _ hpolyScaled
      (Q'.le_trans' _ _ _ hgainScaled ?_))
  have hswap :
      (sixteenNinths *
          Q'.ofNat ((label + 1) ^ 2)) *
        (qpow w (c4 label) * qpow half 7) ≈
      (sixteenNinths * qpow half 7) *
        (Q'.ofNat ((label + 1) ^ 2) *
          qpow w (c4 label)) :=
    mul_four_swap
      sixteenNinths
      (Q'.ofNat ((label + 1) ^ 2))
      (qpow w (c4 label))
      (qpow half 7)
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ hswap
      (Q'.mul_eqv_congr_right _ _ _
        sharp_ratio_constant))

/-! ## 3. Finite geometric tail and pointwise term bounds -/

theorem labelTwo_majorant_le
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    pointwiseHeatMajorant w 2 ≤ labelTwoHead := by
  unfold pointwiseHeatMajorant tailTerm
  have hpower : qpow w (c4 2) ≤ qpow half (c4 2) :=
    qpow_mono hw0 hw (c4 2)
  have hscaled :
      Q'.ofNat ((2 + 1) ^ 2) * qpow w (c4 2) ≤
        Q'.ofNat ((2 + 1) ^ 2) * qpow half (c4 2) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpower
      (zero_le_ofNat _)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (by decide))

/-- Every finite majorant tail from label two is bounded by `81/2272`. -/
theorem pointwiseHeatMajorant_tail_le
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    ∀ M,
      finSum
          (fun k => pointwiseHeatMajorant w (2 + k)) M ≤
        allLabelTailBudget := by
  intro M
  apply CharacterTail.geom_series_le
    (fun k => pointwiseHeatMajorant w (2 + k))
    labelTwoHead sharpTailRatio allLabelTailBudget
  · exact sharpTailRatio_nonnegative
  · exact allLabelTailBudget_nonnegative
  · simpa only [Nat.add_zero] using labelTwo_majorant_le hw0 hw
  · intro k
    have hindex : 2 + (k + 1) = (2 + k) + 1 := by
      omega
    rw [hindex]
    exact pointwiseHeatMajorant_succ_le
      hw0 hw (2 + k) (by omega)
  · exact exact_geometric_closure

private theorem heatTerm_majorant_eqv
    (w : Q') (label : Nat) :
    coeffW w label * Q'.ofNat (label + 1) ≈
      pointwiseHeatMajorant w label := by
  unfold coeffW dimQ pointwiseHeatMajorant tailTerm
  have hsquare :
      Q'.ofNat (label + 1) * Q'.ofNat (label + 1) ≈
        Q'.ofNat ((label + 1) ^ 2) := by
    simpa only [Nat.pow_two] using
      (SU3CharFactor.ofNat_mul_eqv
        (label + 1) (label + 1))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv
      (Q'.ofNat (label + 1))
      (qpow w (c4 label))
      (Q'.ofNat (label + 1))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (Q'.ofNat (label + 1)) _ _
      (Q'.mul_comm_eqv
        (qpow w (c4 label))
        (Q'.ofNat (label + 1)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (Q'.ofNat (label + 1))
        (Q'.ofNat (label + 1))
        (qpow w (c4 label)))) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    hsquare

/-- Two-sided pointwise domination by the positive squared-dimension
majorant. -/
theorem pointwiseHeatTerm_twoSided
    {w x : Q'} (hw0 : (0 : Q') ≤ w)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (label : Nat) :
    -pointwiseHeatMajorant w label ≤
        pointwiseHeatTerm w x label ∧
      pointwiseHeatTerm w x label ≤
        pointwiseHeatMajorant w label := by
  have hcoefficient :
      (0 : Q') ≤ coeffW w label :=
    coeffW_nonneg hw0 label
  obtain ⟨hUUpper, hULower⟩ :=
    ChebU.absU_le label x hxUpper hxLower
  have hupper :
      pointwiseHeatTerm w x label ≤
        coeffW w label * Q'.ofNat (label + 1) :=
    Q'.mul_le_mul_of_nonneg_left
      _ _ _ hUUpper hcoefficient
  have hupper' :
      pointwiseHeatTerm w x label ≤
        pointwiseHeatMajorant w label :=
    Q'.le_trans' _ _ _ hupper
      (Q'.le_of_eqv
        (heatTerm_majorant_eqv w label))
  have hlowerScaled :
      coeffW w label * (-(Q'.ofNat (label + 1))) ≤
        pointwiseHeatTerm w x label :=
    Q'.mul_le_mul_of_nonneg_left
      _ _ _ hULower hcoefficient
  have hnegEqv :
      coeffW w label * (-(Q'.ofNat (label + 1))) ≈
        -(pointwiseHeatMajorant w label) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_neg_eqv
        (coeffW w label)
        (Q'.ofNat (label + 1))) ?_
    exact Q'.neg_eqv_congr _ _
      (heatTerm_majorant_eqv w label)
  exact
    ⟨Q'.le_trans' _ _ _
        (Q'.ge_of_eqv hnegEqv)
        hlowerScaled,
      hupper'⟩

private theorem signedTail_upper
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    finSum (fun k => pointwiseHeatTerm w x (2 + k)) M ≤
      allLabelTailBudget := by
  have hterm :
      ∀ k,
        pointwiseHeatTerm w x (2 + k) ≤
          pointwiseHeatMajorant w (2 + k) :=
    fun k =>
      (pointwiseHeatTerm_twoSided
        hw0 hxLower hxUpper (2 + k)).2
  exact Q'.le_trans' _ _ _
    (CharacterTail.finSum_le_termwise _ _ hterm M)
    (pointwiseHeatMajorant_tail_le hw0 hw M)

private theorem signedTail_lower
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    -allLabelTailBudget ≤
      finSum (fun k => pointwiseHeatTerm w x (2 + k)) M := by
  let majorant :=
    fun k => pointwiseHeatMajorant w (2 + k)
  let signed :=
    fun k => pointwiseHeatTerm w x (2 + k)
  have hmajorant :
      finSum majorant M ≤ allLabelTailBudget :=
    pointwiseHeatMajorant_tail_le hw0 hw M
  have hneg :
      -allLabelTailBudget ≤ -(finSum majorant M) :=
    Q'.neg_le_neg hmajorant
  have hsum :
      finSum (fun k => -(majorant k)) M ≤
        finSum signed M := by
    apply CharacterTail.finSum_le_termwise
    intro k
    exact
      (pointwiseHeatTerm_twoSided
        hw0 hxLower hxUpper (2 + k)).1
  exact Q'.le_trans' _ _ _ hneg
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Constructive.neg_finSum majorant M))
      hsum)

private theorem labelOne_majorant_le
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    pointwiseHeatMajorant w 1 ≤ half := by
  unfold pointwiseHeatMajorant tailTerm
  have hpower : qpow w (c4 1) ≤ qpow half (c4 1) :=
    qpow_mono hw0 hw (c4 1)
  have hscaled :
      Q'.ofNat ((1 + 1) ^ 2) * qpow w (c4 1) ≤
        Q'.ofNat ((1 + 1) ^ 2) * qpow half (c4 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpower
      (zero_le_ofNat _)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (by decide))

private theorem labelOne_twoSided
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    -half ≤ pointwiseHeatTerm w x 1 ∧
      pointwiseHeatTerm w x 1 ≤ half := by
  have hterm :=
    pointwiseHeatTerm_twoSided
      hw0 hxLower hxUpper 1
  have hhead := labelOne_majorant_le hw0 hw
  exact
    ⟨Q'.le_trans' _ _ _
        (Q'.neg_le_neg hhead) hterm.1,
      Q'.le_trans' _ _ _ hterm.2 hhead⟩

/-! ## 4. Exact finite-partial pointwise corridor -/

/-- **Pointwise all-label floor for every finite partial.** -/
theorem allLabelHaarFloor_le_pointwiseHeatPartial
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    allLabelHaarFloor ≤ pointwiseHeatPartial w x M := by
  have hone := (labelOne_twoSided
    hw0 hw hxLower hxUpper).1
  have htail :=
    signedTail_lower hw0 hw hxLower hxUpper M
  have hsum :
      ((1 : Q') + -half) + -allLabelTailBudget ≤
        ((1 : Q') + pointwiseHeatTerm w x 1) +
          finSum (fun k =>
            pointwiseHeatTerm w x (2 + k)) M :=
    Q'.add_le_add
      ((Q'.add_le_add
        (Q'.le_refl' 1) hone))
      htail
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by decide))
    hsum

/-- **Pointwise all-label ceiling for every finite partial.** -/
theorem pointwiseHeatPartial_le_allLabelHaarCeiling
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    pointwiseHeatPartial w x M ≤ allLabelHaarCeiling := by
  have hone := (labelOne_twoSided
    hw0 hw hxLower hxUpper).2
  have htail :=
    signedTail_upper hw0 hw hxLower hxUpper M
  have hsum :
      ((1 : Q') + pointwiseHeatTerm w x 1) +
          finSum (fun k =>
            pointwiseHeatTerm w x (2 + k)) M ≤
        ((1 : Q') + half) + allLabelTailBudget :=
    Q'.add_le_add
      (Q'.add_le_add (Q'.le_refl' 1) hone)
      htail
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv (by decide))

/-- Every finite pointwise partial is strictly positive, uniformly in the
label cutoff. -/
theorem pointwiseHeatPartial_pos
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    (0 : Q') < pointwiseHeatPartial w x M :=
  lt_of_lt_of_le allLabelHaarFloor_pos
    (allLabelHaarFloor_le_pointwiseHeatPartial
      hw0 hw hxLower hxUpper M)

/-- The exact finite-partial corridor is packaged without claiming an
identification with an interacting BF4 retained factor. -/
structure FinitePointwiseHeatCorridor
    (w x : Q') (M : Nat) : Type where
  lower :
    allLabelHaarFloor ≤ pointwiseHeatPartial w x M
  upper :
    pointwiseHeatPartial w x M ≤ allLabelHaarCeiling

def finitePointwiseHeatCorridor
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    FinitePointwiseHeatCorridor w x M where
  lower :=
    allLabelHaarFloor_le_pointwiseHeatPartial
      hw0 hw hxLower hxUpper M
  upper :=
    pointwiseHeatPartial_le_allLabelHaarCeiling
      hw0 hw hxLower hxUpper M

/-! ## 5. Literal 23-factor retained finite-heat consumer -/

/-- A retained kinetic weight which is literally a product of finite
pointwise SU(2) class-heat partials. -/
def finitePointwiseRetainedKinetic
    {Source Target State Factor : Type}
    (factors : List Factor)
    (heatNome : Factor → Q')
    (classCoordinate :
      Source → Target → List State → Factor → Q')
    (cutoff : Factor → Nat)
    (source : Source) (target : Target) (path : List State) : Q' :=
  retainedFactorProduct
    (fun factor =>
      pointwiseHeatPartial
        (heatNome factor)
        (classCoordinate source target path factor)
        (cutoff factor))
    factors

/-- **Finite retained SU(2) heat Harnack datum.**  A literal product of 23
finite pointwise class-heat partials satisfies the exact BF4 retained-path
Harnack window whenever every nome lies in `[0,1/2]` and every class
coordinate lies in `[-1,1]`.

This is not an identification theorem for the interacting BF4 slab.  A
physical consumer must still prove that its retained kinetic weight is
equal (or semantically equivalent in a compatible interface) to this
literal 23-factor product. -/
def finitePointwiseBF4RetainedKineticHarnack
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (heatNome : Factor → Q')
    (classCoordinate :
      Source → Target → List State → Factor → Q')
    (cutoff : Factor → Nat)
    (sources : List Source) (targets : List Target)
    (nome_nonnegative :
      ∀ factor, factor ∈ factors →
        (0 : Q') ≤ heatNome factor)
    (nome_le_half :
      ∀ factor, factor ∈ factors →
        heatNome factor ≤ half)
    (coordinate_lower :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            ∀ factor, factor ∈ factors →
              (-(1 : Q')) ≤
                classCoordinate source target path factor)
    (coordinate_upper :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            ∀ factor, factor ∈ factors →
              classCoordinate source target path factor ≤
                (1 : Q')) :
    RetainedKineticHarnackData
      paths
      (finitePointwiseRetainedKinetic
        factors heatNome classCoordinate cutoff)
      sources targets :=
  bf4RetainedProductKineticHarnackOfLocalBounds
    paths factors factor_count
    (fun source target path factor =>
      pointwiseHeatPartial
        (heatNome factor)
        (classCoordinate source target path factor)
        (cutoff factor))
    sources targets
    (by
      intro source hsource target htarget
        path hpath factor hfactor
      exact allLabelHaarFloor_le_pointwiseHeatPartial
        (nome_nonnegative factor hfactor)
        (nome_le_half factor hfactor)
        (coordinate_lower source hsource target htarget
          path hpath factor hfactor)
        (coordinate_upper source hsource target htarget
          path hpath factor hfactor)
        (cutoff factor))
    (by
      intro source hsource target htarget
        path hpath factor hfactor
      exact pointwiseHeatPartial_le_allLabelHaarCeiling
        (nome_nonnegative factor hfactor)
        (nome_le_half factor hfactor)
        (coordinate_lower source hsource target htarget
          path hpath factor hfactor)
        (coordinate_upper source hsource target htarget
          path hpath factor hfactor)
        (cutoff factor))

/-! ## Axiom gates -/

#print axioms pointwiseHeatMajorant_succ_le
#print axioms pointwiseHeatMajorant_tail_le
#print axioms pointwiseHeatTerm_twoSided
#print axioms allLabelHaarFloor_le_pointwiseHeatPartial
#print axioms pointwiseHeatPartial_le_allLabelHaarCeiling
#print axioms pointwiseHeatPartial_pos
#print axioms finitePointwiseBF4RetainedKineticHarnack

end YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
