/-
# Explicit convergence modulus for the completed BF4 conditional tail

`BF4CompletedConditionalTailBound` identifies the exact error after finite
conditional integration:

    bf4ProductTail(spacingClosedTail(w, 2+M))
      * rationalPathSum(pathWeight, paths).

This module turns that formula into an explicit tolerance-to-cutoff modulus.
For a fixed rational nome and a fixed finite retained path carrier, collect
all factors independent of the geometric power into
`bf4ConditionalTailScale`.  At tolerance `ε`, rescale by

    δ = ε / (bf4ConditionalTailScale + 1)

and take

    N(ε) = powBaseCutoff(spacingTailRatio(w), δ).

The harmless `+1` makes the construction valid even when the retained path
mass is zero.  Beyond `N(ε)`, the exact conditional tail is at most `ε`.

## Honest scope

The nome `w`, path carrier, and path weights are fixed data.  The cutoff is a
label cutoff for that fixed carrier; no spacing-uniform or continuum-spacing
claim is made here.

## Constructivity

The cutoff and rescaling are explicit `Type`-level data.  All estimates use
the project's rational order and the already-proved general-base power
modulus.  There is no `Classical.*`, `Real`, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4CompletedConditionalTailBound

namespace YMGap.Continuum.BF4CompletedConditionalTailModulus

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CompletedConditionalLimitBridge
open YMGap.Continuum.BF4CompletedConditionalTailBound
open YMGap.Continuum.BF4CompletedProductTailBound
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.GroupedAllLabelHaarRefresh
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Fixed-carrier scale and explicit cutoff -/

/-- The fixed coefficient multiplying
`spacingTailRatio(w)^(2+M)` in the exact BF4 conditional tail. -/
def bf4ConditionalTailScale
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (w : Q') : Q' :=
  (Q'.ofNat 23 * allLabelHaarCeiling ^ 22) *
    (spacingTailHead w *
      (HKConv.divPos 1 (1 + (-spacingTailRatio w)) *
        rationalPathSum pathWeight paths))

/-- Positive denominator used to rescale a requested tolerance.  The `+1`
keeps it positive when every path weight vanishes or the carrier is empty. -/
def bf4ConditionalTailScaleDenominator
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (w : Q') : Q' :=
  bf4ConditionalTailScale paths pathWeight w + 1

/-- Explicit tolerance rescaling for the fixed finite path carrier. -/
def bf4ConditionalTailRescale
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (w ε : Q') : Q' :=
  HKConv.divPos ε
    (bf4ConditionalTailScaleDenominator
      paths pathWeight w)

/-- Explicit label cutoff at which the exact conditional BF4 tail is below
the requested tolerance. -/
def bf4ConditionalTailCutoff
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (w ε : Q') : Nat :=
  powBaseCutoff
    (spacingTailRatio w)
    (bf4ConditionalTailRescale
      paths pathWeight w ε)

/-! ## 2. Positivity and exact coefficient algebra -/

/-- A finite rational path sum is nonnegative when every retained summand is
nonnegative. -/
theorem rationalPathSum_nonnegative
    {Path : Type}
    (pathWeight : Path → Q') :
    ∀ paths : List Path,
      (∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path) →
      (0 : Q') ≤ rationalPathSum pathWeight paths
  | [], _ => Q'.le_refl' 0
  | path :: rest, pathWeight_nonnegative =>
      Q'.zero_le_add _ _
        (pathWeight_nonnegative
          path List.mem_cons_self)
        (rationalPathSum_nonnegative
          pathWeight rest
          (fun item hitem =>
            pathWeight_nonnegative item
              (List.mem_cons_of_mem path hitem)))

/-- The fixed conditional-tail scale is nonnegative. -/
theorem bf4ConditionalTailScale_nonnegative
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') ≤
      bf4ConditionalTailScale
        paths pathWeight w := by
  unfold bf4ConditionalTailScale
  exact Q'.mul_nonneg _ _
    (by decide)
    (Q'.mul_nonneg _ _
      (spacingTailHead_nonnegative hw0)
      (Q'.mul_nonneg _ _
        (HKConv.divPos_nonneg
          (Q'.le_of_lt
            (CReal.pos_of_num_pos (by decide))))
        (rationalPathSum_nonnegative
          pathWeight paths pathWeight_nonnegative)))

/-- The safe rescaling denominator is strictly positive. -/
theorem bf4ConditionalTailScaleDenominator_pos
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') <
      bf4ConditionalTailScaleDenominator
        paths pathWeight w := by
  have hscale :=
    bf4ConditionalTailScale_nonnegative
      paths pathWeight pathWeight_nonnegative hw0
  have hone :
      (1 : Q') ≤
        1 +
          bf4ConditionalTailScale
            paths pathWeight w :=
    Q'.add_le_self_of_nonneg 1 _ hscale
  exact Q'.pos_of_lt_of_le
    (by decide)
    (Q'.le_trans' _ _ _ hone
      (Q'.le_of_eqv
        (Q'.add_comm_eqv
          1
          (bf4ConditionalTailScale
            paths pathWeight w))))

/-- Moving the geometric power past the Haar denominator and total path
weight.  This is the exact five-factor regrouping used below. -/
private theorem conditional_tail_regroup
    (a head power haarMass pathMass : Q') :
    (a * ((head * power) * haarMass)) * pathMass ≈
      (a * (head * (haarMass * pathMass))) * power := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv
      a ((head * power) * haarMass) pathMass) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      a
      (((head * power) * haarMass) * pathMass)
      ((head * power) * (haarMass * pathMass))
      (Q'.mul_assoc_eqv
        (head * power) haarMass pathMass)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      a
      ((head * power) * (haarMass * pathMass))
      (head * (power * (haarMass * pathMass)))
      (Q'.mul_assoc_eqv
        head power (haarMass * pathMass))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      a
      (head * (power * (haarMass * pathMass)))
      (head * ((haarMass * pathMass) * power))
      (Q'.mul_eqv_congr_left
        head
        (power * (haarMass * pathMass))
        ((haarMass * pathMass) * power)
        (Q'.mul_comm_eqv
          power (haarMass * pathMass)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      a
      (head * ((haarMass * pathMass) * power))
      ((head * (haarMass * pathMass)) * power)
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          head (haarMass * pathMass) power))) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv
      a (head * (haarMass * pathMass)) power)

/-- The exact conditional tail is the fixed carrier scale times the remaining
geometric power. -/
theorem bf4ConditionalTail_formula
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (w : Q') (M : Nat) :
    bf4ConditionalTail
        paths pathWeight
        (spacingClosedTail w (2 + M)) ≈
      bf4ConditionalTailScale
          paths pathWeight w *
        spacingTailRatio w ^ (2 + M) := by
  unfold bf4ConditionalTail bf4ProductTail
  unfold spacingClosedTail geoTailBase
  unfold bf4ConditionalTailScale
  exact conditional_tail_regroup
    (Q'.ofNat 23 * allLabelHaarCeiling ^ 22)
    (spacingTailHead w)
    (spacingTailRatio w ^ (2 + M))
    (HKConv.divPos 1 (1 + (-spacingTailRatio w)))
    (rationalPathSum pathWeight paths)

/-! ## 3. The computed tolerance rescaling -/

/-- The explicit rescaling is positive at every positive tolerance. -/
theorem bf4ConditionalTailRescale_pos
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (w ε : Q') (hε : (0 : Q') < ε) :
    (0 : Q') <
      bf4ConditionalTailRescale
        paths pathWeight w ε := by
  unfold bf4ConditionalTailRescale
  exact HKConv.divPos_pos
    (CReal.num_pos_of_pos hε)

/-- Multiplying the rescaled tolerance by the fixed conditional-tail scale
uses no more than the requested tolerance. -/
theorem bf4ConditionalTailScale_mul_rescale_le
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    {w ε : Q'} (hw0 : (0 : Q') < w)
    (hε : (0 : Q') < ε) :
    bf4ConditionalTailScale paths pathWeight w *
        bf4ConditionalTailRescale
          paths pathWeight w ε ≤
      ε := by
  let scale :=
    bf4ConditionalTailScale paths pathWeight w
  let denominator :=
    bf4ConditionalTailScaleDenominator
      paths pathWeight w
  let δ :=
    bf4ConditionalTailRescale
      paths pathWeight w ε
  have hscale0 : (0 : Q') ≤ scale :=
    bf4ConditionalTailScale_nonnegative
      paths pathWeight pathWeight_nonnegative hw0
  have hdenPos : (0 : Q') < denominator :=
    bf4ConditionalTailScaleDenominator_pos
      paths pathWeight pathWeight_nonnegative hw0
  have hδ0 : (0 : Q') ≤ δ :=
    Q'.le_of_lt
      (bf4ConditionalTailRescale_pos
        paths pathWeight w ε hε)
  have hscaleDen : scale ≤ denominator := by
    exact Q'.add_le_self_of_nonneg
      scale 1 (by decide)
  have hmul :
      scale * δ ≤ denominator * δ :=
    Q'.mul_le_mul_of_nonneg_right
      scale denominator δ hscaleDen hδ0
  have hcancel : denominator * δ ≈ ε := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv denominator δ)
      (HKConv.divPos_mul_eqv
        (CReal.num_pos_of_pos hdenPos))
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv hcancel)

/-- Type-level package of the explicit rescaling witness. -/
def bf4ConditionalTailRescaleData
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    {w ε : Q'} (hw0 : (0 : Q') < w)
    (hε : (0 : Q') < ε) :
    Σ' δ : Q',
      (0 : Q') < δ ∧
        bf4ConditionalTailScale
            paths pathWeight w * δ ≤
          ε :=
  ⟨bf4ConditionalTailRescale
      paths pathWeight w ε,
    bf4ConditionalTailRescale_pos
      paths pathWeight w ε hε,
    bf4ConditionalTailScale_mul_rescale_le
      paths pathWeight pathWeight_nonnegative
      hw0 hε⟩

/-! ## 4. Explicit generic and potential-weight convergence moduli -/

/-- The exact fixed-carrier conditional tail is at most `ε` at every label
index beyond the computed cutoff. -/
theorem bf4ConditionalTail_le_tolerance
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    {w ε : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (hε : (0 : Q') < ε)
    (M : Nat)
    (hM :
      bf4ConditionalTailCutoff
          paths pathWeight w ε ≤
        M) :
    bf4ConditionalTail
        paths pathWeight
        (spacingClosedTail w (2 + M)) ≤
      ε := by
  let ratio := spacingTailRatio w
  let scale :=
    bf4ConditionalTailScale paths pathWeight w
  let δ :=
    bf4ConditionalTailRescale
      paths pathWeight w ε
  have hw1 : w < (1 : Q') :=
    Q'.lt_of_le_of_lt hw (by decide)
  have hratio0 : (0 : Q') < ratio :=
    spacingTailRatio_pos hw0
  have hratio1 : ratio < (1 : Q') :=
    spacingTailRatio_lt_one hw0 hw1
  have hδpos : (0 : Q') < δ :=
    bf4ConditionalTailRescale_pos
      paths pathWeight w ε hε
  have hcutoff :
      ratio ^
          (bf4ConditionalTailCutoff
            paths pathWeight w ε) ≤
        δ := by
    exact pow_base_le_cutoff
      hratio0 hratio1 hδpos
  have hpowerM : ratio ^ M ≤ δ := by
    exact Q'.le_trans' _ _ _
      (pow_base_antitone
        (Q'.le_of_lt hratio0)
        (Q'.le_of_lt hratio1)
        hM)
      hcutoff
  have hpowerShift :
      ratio ^ (2 + M) ≤ ratio ^ M := by
    exact pow_base_antitone
      (Q'.le_of_lt hratio0)
      (Q'.le_of_lt hratio1)
      (by omega)
  have hscale0 : (0 : Q') ≤ scale :=
    bf4ConditionalTailScale_nonnegative
      paths pathWeight pathWeight_nonnegative hw0
  have htailScale :
      scale * ratio ^ (2 + M) ≤
        scale * δ :=
    Q'.mul_le_mul_of_nonneg_left
      _ _ scale
      (Q'.le_trans' _ _ _ hpowerShift hpowerM)
      hscale0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (bf4ConditionalTail_formula
        paths pathWeight w M))
    (Q'.le_trans' _ _ _ htailScale
      (bf4ConditionalTailScale_mul_rescale_le
        paths pathWeight pathWeight_nonnegative
        hw0 hε))

/-- Potential-weight specialization of the explicit cutoff. -/
def bf4PotentialConditionalTailCutoff
    {State : Type}
    (paths : List (List State))
    (potential : State → Q')
    (w ε : Q') : Nat :=
  bf4ConditionalTailCutoff
    paths (pathPotentialProduct potential) w ε

/-- For nonnegative local interior potentials, the actual potential-weighted
conditional BF4 tail is below `ε` beyond the computed cutoff. -/
theorem bf4PotentialConditionalTail_le_tolerance
    {State : Type}
    (paths : List (List State))
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    {w ε : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (hε : (0 : Q') < ε)
    (M : Nat)
    (hM :
      bf4PotentialConditionalTailCutoff
          paths potential w ε ≤
        M) :
    bf4PotentialConditionalTail
        paths potential
        (spacingClosedTail w (2 + M)) ≤
      ε := by
  exact bf4ConditionalTail_le_tolerance
    paths
    (pathPotentialProduct potential)
    (fun path hpath =>
      pathPotentialProduct_nonnegative
        potential_nonnegative path)
    hw0 hw hε M hM

/-! ## Axiom gates -/

#print axioms rationalPathSum_nonnegative
#print axioms bf4ConditionalTailScale_nonnegative
#print axioms bf4ConditionalTail_formula
#print axioms bf4ConditionalTailScale_mul_rescale_le
#print axioms bf4ConditionalTailRescaleData
#print axioms bf4ConditionalTail_le_tolerance
#print axioms bf4PotentialConditionalTail_le_tolerance

end YMGap.Continuum.BF4CompletedConditionalTailModulus
