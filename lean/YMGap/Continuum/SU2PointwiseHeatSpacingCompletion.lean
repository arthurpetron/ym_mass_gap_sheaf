/-
# Spacing-dependent completion of the SU(2) pointwise heat series

The fixed `w ≤ 1/2` corridor has a cutoff-independent tail ratio.  At a
general rational heat nome `0 < w < 1`, the same character majorant is still
super-geometric, but the useful geometric ratio starts later.  This module
constructs that later cutoff as data:

    N(w) = powBaseCutoff w (1/8).

The general-base power modulus gives `w^N ≤ 1/8`.  Since powers decrease on
`[0,1]`,

    w^(2N+3) ≤ w^N ≤ 1/8,

and therefore the degree-two character-majorant ratio

    rho(w) = 4 * w^(2N+3)

is at most `1/2`, hence strictly below one.  Starting at label `N(w)`, the
signed SU(2) heat-character terms are dominated by

    tailTerm(w,2,N) * rho(w)^k.

The existing general-base geometric completion engine then turns the standard
character prefixes through label `N+M-1` into a genuine `CReal`.

## Honest scope

This is a pointwise class-coordinate completion for one rational nome and one
`x ∈ [-1,1]`.  The label cutoff depends explicitly on `w`, as it must when
`w → 1`.  No spacing-uniform cutoff, interacting BF4 slab identification,
Haar integration, or continuum-spacing limit is asserted here.

## Constructivity

The label cutoff and the tolerance rescaling are explicit functions.  The
rescaling witness is first returned as `Type`-level sigma data and only then
fed into the legacy `Prop`-level existential expected by `CReal`.  There is no
`Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealLe

namespace YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.HKConv
open YMGap.Continuum.HKPos
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The explicit spacing-dependent label cutoff -/

/-- The rational target used to locate the geometric tail. -/
def eighth : Q' := Q'.mkPos 1 8 (by decide)

/-- The first retained tail label at nome `w`.  This is the explicit
spacing-dependent cutoff supplied by the general-base power modulus. -/
def spacingLabelCutoff (w : Q') : Nat :=
  powBaseCutoff w eighth

/-- The degree-two majorant ratio after `spacingLabelCutoff w`. -/
def spacingTailRatio (w : Q') : Q' :=
  Q'.ofNat 4 *
    qpow w (2 * spacingLabelCutoff w + 3)

/-- The first majorant in the shifted tail. -/
def spacingTailHead (w : Q') : Q' :=
  pointwiseHeatMajorant w (spacingLabelCutoff w)

/-- The project `qpow` fold and the `Q'.pow` fold used by
`powBaseCutoff` represent the same rational value. -/
theorem qpow_eqv_pow (w : Q') :
    ∀ n, qpow w n ≈ w ^ n
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      have ih := qpow_eqv_pow w n
      show qpow w n * w ≈ w * w ^ n
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ w ih)
        (Q'.mul_comm_eqv (w ^ n) w)

/-- The explicit cutoff pays the target power `w^N ≤ 1/8`. -/
theorem spacingLabelCutoff_power_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    qpow w (spacingLabelCutoff w) ≤ eighth := by
  have hpow :
      w ^ (powBaseCutoff w eighth) ≤ eighth :=
    pow_base_le_cutoff hw0 hw1 (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (qpow_eqv_pow w (spacingLabelCutoff w)))
    hpow

/-- The larger Casimir-gain exponent is no larger than the cutoff power. -/
theorem spacingCasimirGain_le_eighth
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    qpow w (2 * spacingLabelCutoff w + 3) ≤ eighth := by
  have hmono :
      qpow w (2 * spacingLabelCutoff w + 3) ≤
        qpow w (spacingLabelCutoff w) :=
    qpow_antitone
      (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      (spacingLabelCutoff w)
      (2 * spacingLabelCutoff w + 3)
      (by omega)
  exact Q'.le_trans' _ _ _ hmono
    (spacingLabelCutoff_power_le hw0 hw1)

/-- The actual degree-two shifted-tail ratio is at most `1/2`. -/
theorem spacingTailRatio_le_half
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    spacingTailRatio w ≤
      Q'.mkPos 1 2 (by decide) := by
  have hgain :=
    spacingCasimirGain_le_eighth hw0 hw1
  have hscaled :
      Q'.ofNat 4 *
          qpow w (2 * spacingLabelCutoff w + 3) ≤
        Q'.ofNat 4 * eighth :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hgain (by decide)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (by decide))

/-- The shifted-tail ratio is strictly positive. -/
theorem spacingTailRatio_pos
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < spacingTailRatio w := by
  unfold spacingTailRatio
  exact q_mul_pos
    (CReal.pos_of_num_pos (by decide))
    (qpow_pos hw0 _)

/-- The shifted-tail ratio is genuinely contractive. -/
theorem spacingTailRatio_lt_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    spacingTailRatio w < (1 : Q') :=
  Q'.lt_of_le_of_lt
    (spacingTailRatio_le_half hw0 hw1)
    (by decide)

/-- The first shifted majorant is strictly positive. -/
theorem spacingTailHead_pos
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < spacingTailHead w := by
  unfold spacingTailHead pointwiseHeatMajorant tailTerm
  apply q_mul_pos
  · apply CReal.pos_of_num_pos
    show (0 : Int) <
      ((((spacingLabelCutoff w + 1) ^ 2 : Nat) : Int))
    exact_mod_cast
      Nat.pow_pos (Nat.succ_pos (spacingLabelCutoff w))
  · exact qpow_pos hw0 _

/-- Nonnegative form of the shifted head. -/
theorem spacingTailHead_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') ≤ spacingTailHead w :=
  Q'.le_of_lt (spacingTailHead_pos hw0)

/-! ## 2. Geometric domination of the signed shifted tail -/

/-- The actual majorant ratio step at the computed cutoff. -/
theorem shiftedMajorant_ratio
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (k : Nat) :
    pointwiseHeatMajorant w
        (spacingLabelCutoff w + (k + 1)) ≤
      spacingTailRatio w *
        pointwiseHeatMajorant w
          (spacingLabelCutoff w + k) := by
  simpa [pointwiseHeatMajorant, spacingTailRatio] using
    (tailTerm_ratio
      (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      2 (spacingLabelCutoff w) k)

/-- Every shifted majorant is bounded by the explicit geometric envelope. -/
theorem shiftedMajorant_le_geometric
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (k : Nat) :
    pointwiseHeatMajorant w
        (spacingLabelCutoff w + k) ≤
      spacingTailHead w * spacingTailRatio w ^ k := by
  exact CharacterTail.geom_dom
    (fun j =>
      pointwiseHeatMajorant w
        (spacingLabelCutoff w + j))
    (spacingTailHead w)
    (spacingTailRatio w)
    (Q'.le_of_lt (spacingTailRatio_pos hw0))
    (by
      simpa [spacingTailHead] using
        (Q'.le_refl'
          (pointwiseHeatMajorant w
            (spacingLabelCutoff w))))
    (shiftedMajorant_ratio hw0 hw1)
    k

/-- The shifted signed heat term lies in the same geometric envelope. -/
theorem shiftedHeatTerm_twoSided
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (k : Nat) :
    -(spacingTailHead w * spacingTailRatio w ^ k) ≤
        pointwiseHeatTerm w x
          (spacingLabelCutoff w + k) ∧
      pointwiseHeatTerm w x
          (spacingLabelCutoff w + k) ≤
        spacingTailHead w * spacingTailRatio w ^ k := by
  have hterm :=
    pointwiseHeatTerm_twoSided
      (Q'.le_of_lt hw0) hxLower hxUpper
      (spacingLabelCutoff w + k)
  have hmajorant :=
    shiftedMajorant_le_geometric hw0 hw1 k
  exact
    ⟨Q'.le_trans' _ _ _
        (Q'.neg_le_neg hmajorant) hterm.1,
      Q'.le_trans' _ _ _ hterm.2 hmajorant⟩

/-! ## 3. Shifted standard prefixes and their increment bounds -/

/-- The ordinary character prefix through labels
`0, ..., spacingLabelCutoff(w)+M-1`. -/
def spacingPointwiseHeatPartial
    (w x : Q') (M : Nat) : Q' :=
  standardPointwiseHeatPartial
    w x (spacingLabelCutoff w + M)

/-- Adding one shifted label adds exactly its signed heat term. -/
theorem spacingPointwiseHeatPartial_succ
    (w x : Q') (M : Nat) :
    spacingPointwiseHeatPartial w x (M + 1) =
      spacingPointwiseHeatPartial w x M +
        pointwiseHeatTerm w x
          (spacingLabelCutoff w + M) := by
  unfold spacingPointwiseHeatPartial
  have hindex :
      spacingLabelCutoff w + (M + 1) =
        (spacingLabelCutoff w + M) + 1 := by
    omega
  rw [hindex]
  rfl

/-- Upper one-step increment bound for the shifted prefix sequence. -/
theorem spacingPointwiseHeatPartial_hup
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    spacingPointwiseHeatPartial w x (M + 1) ≤
      spacingPointwiseHeatPartial w x M +
        geoIncrBase
          (spacingTailHead w) (spacingTailRatio w) M := by
  rw [spacingPointwiseHeatPartial_succ]
  exact Q'.add_le_add_left _ _ _
    (shiftedHeatTerm_twoSided
      hw0 hw1 hxLower hxUpper M).2

/-- Lower one-step increment bound for the shifted prefix sequence. -/
theorem spacingPointwiseHeatPartial_hlo
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    spacingPointwiseHeatPartial w x M ≤
      spacingPointwiseHeatPartial w x (M + 1) +
        geoIncrBase
          (spacingTailHead w) (spacingTailRatio w) M := by
  rw [spacingPointwiseHeatPartial_succ]
  let tail :=
    geoIncrBase
      (spacingTailHead w) (spacingTailRatio w) M
  let term :=
    pointwiseHeatTerm w x
      (spacingLabelCutoff w + M)
  have hlower : -tail ≤ term := by
    dsimp [tail, term, geoIncrBase]
    exact
      (shiftedHeatTerm_twoSided
        hw0 hw1 hxLower hxUpper M).1
  have hnonnegative : (0 : Q') ≤ term + tail := by
    have hadd :
        -tail + tail ≤ term + tail :=
      Q'.add_le_add_right _ _ tail hlower
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.neg_add_self_eqv tail))
      hadd
  have hbase :
      spacingPointwiseHeatPartial w x M ≤
        spacingPointwiseHeatPartial w x M +
          (term + tail) :=
    Q'.add_le_self_of_nonneg _ _ hnonnegative
  exact Q'.le_trans' _ _ _ hbase
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.add_assoc_eqv
          (spacingPointwiseHeatPartial w x M)
          term tail)))

/-! ## 4. Type-level rescaling data and the constructive CReal -/

/-- The scale multiplying the geometric base power in the closed tail. -/
def spacingTailScale (w : Q') : Q' :=
  spacingTailHead w *
    HKConv.divPos 1 (1 + (-spacingTailRatio w))

/-- The explicit rational rescaling used at target tolerance `ε`. -/
def spacingTailRescale (w ε : Q') : Q' :=
  HKConv.divPos ε (spacingTailScale w)

/-- The explicit approximation-index cutoff associated to a target tolerance. -/
def spacingTailCauchyCutoff (w ε : Q') : Nat :=
  powBaseCutoff
    (spacingTailRatio w)
    (spacingTailRescale w ε)

/-- The closed geometric-tail scale is strictly positive. -/
theorem spacingTailScale_pos
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < spacingTailScale w := by
  unfold spacingTailScale
  exact q_mul_pos
    (spacingTailHead_pos hw0)
    (HKConv.divPos_pos (by decide))

/-- The tolerance rescaling is returned as `Type`-level data. -/
def spacingTailRescaleData
    {w : Q'} (hw0 : (0 : Q') < w)
    (ε : Q') (hε : (0 : Q') < ε) :
    Σ' δ : Q',
      (0 : Q') < δ ∧
        spacingTailScale w * δ ≤ ε := by
  have hscaleNum :
      0 < (spacingTailScale w).num :=
    CReal.num_pos_of_pos
      (spacingTailScale_pos hw0)
  refine
    ⟨spacingTailRescale w ε,
      HKConv.divPos_pos (CReal.num_pos_of_pos hε),
      ?_⟩
  refine Q'.le_of_eqv ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (spacingTailScale w)
      (spacingTailRescale w ε))
    (HKConv.divPos_mul_eqv hscaleNum)

/-- Legacy existential wrapper consumed by `crealOfGeoIncrementBase`; its
witness is the explicit sigma datum above. -/
theorem spacingTailRescale_exists
    {w : Q'} (hw0 : (0 : Q') < w) :
    ∀ ε : Q', (0 : Q') < ε →
      ∃ δ : Q', (0 : Q') < δ ∧
        (spacingTailHead w *
          HKConv.divPos 1 (1 + (-spacingTailRatio w))) *
            δ ≤ ε := by
  intro ε hε
  let data :=
    spacingTailRescaleData hw0 ε hε
  exact ⟨data.1, data.2.1, data.2.2⟩

/-- **The arbitrary-nome pointwise SU(2) heat series as a constructive real.**
Its `M`-th rational approximation is the ordinary character prefix through the
spacing-dependent cutoff plus `M` additional labels. -/
def pointwiseHeatCReal
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CReal :=
  crealOfGeoIncrementBase
    (spacingPointwiseHeatPartial w x)
    (spacingTailHead w)
    (spacingTailRatio w)
    (spacingTailHead_nonnegative hw0)
    (spacingTailRatio_pos hw0)
    (spacingTailRatio_lt_one hw0 hw1)
    (spacingPointwiseHeatPartial_hup
      hw0 hw1 hxLower hxUpper)
    (spacingPointwiseHeatPartial_hlo
      hw0 hw1 hxLower hxUpper)
    (spacingTailRescale_exists hw0)

/-- The completed real's approximations are exactly the shifted standard
character prefixes. -/
@[simp] theorem pointwiseHeatCReal_approx
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    (pointwiseHeatCReal
      hw0 hw1 hxLower hxUpper).approx M =
        spacingPointwiseHeatPartial w x M := rfl

/-- **Convergence of the finite character prefixes to the completed heat
value.**  This is the canonical `CReal` convergence supplied by the Cauchy
modulus carried in `pointwiseHeatCReal`. -/
theorem spacingPointwiseHeatPartial_converges
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CReal.ConvergesTo
      (fun M =>
        CReal.ofQ'
          (spacingPointwiseHeatPartial w x M))
      (pointwiseHeatCReal
        hw0 hw1 hxLower hxUpper) := by
  exact CReal.convergesTo_self
    (pointwiseHeatCReal
      hw0 hw1 hxLower hxUpper)

/-! ## Axiom gates -/

#print axioms qpow_eqv_pow
#print axioms spacingLabelCutoff_power_le
#print axioms spacingTailRatio_lt_one
#print axioms shiftedMajorant_le_geometric
#print axioms shiftedHeatTerm_twoSided
#print axioms spacingTailRescaleData
#print axioms pointwiseHeatCReal
#print axioms pointwiseHeatCReal_approx
#print axioms spacingPointwiseHeatPartial_converges

end YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
