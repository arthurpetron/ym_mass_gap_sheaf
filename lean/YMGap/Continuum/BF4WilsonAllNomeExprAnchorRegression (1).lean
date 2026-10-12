/-
# No-regression: the padded plaquette trajectory `Y_j` is an expression anchor

Companion to `audits/AUDIT-EXPR-ANCHOR-TRAJECTORY-2026-10-06.md` §3. ADDITIVE.

`toExprTrajectory tr` sends every `DyadicSmoothedTrajectory` to the
`ExprAnchorTrajectory` with
* width `trajWidth`;
* radius `tr.radius`;
* expression `familyState (trajWidth j) (faces j) (coeff j) _`.

DEFINITIONAL agreement (`rfl` / `Iff.rfl`):
* the unsmoothed vector, the smoothed state and the response;
* the shifted H1, window survival and nondegeneracy Props;
* the anchor data `exprShiftedPathAnchor = shiftedPathAnchor`;
* hence `ExprShiftedAnchorPackage ↔ ShiftedAnchorPackage`;
* the floor `exprNondegFloor (paddedVar) (paddedRho) = paddedNondegFloor`.

H-var and H-ray are DISCHARGED for every plaquette trajectory:
* H-var by `familyExcitation_norm_floor`, with `v_j = varianceFloor(w_j)·Σ c_j²`;
* H-ray under padding by `family_rayleigh_floor`, with
  `ρ_j = familyResponseFraction(w_j, |faces_j|)`.

So the general package reproves `path_normalized_anchor_of_windowSurvival_padded`
(`padded_package_via_expr`). Concrete instances: `paddedZeroMomentumTrajectory` and
`afPaddedZeroMomentumTrajectory`. Window survival stays the single OPEN input.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeExprShiftedAnchorPackage
import YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory

namespace YMGap.Continuum.BF4WilsonAllNomeExprAnchorRegression

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity (varianceFloor varianceFloor_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
  (familyResponseFraction familyResponseFraction_positive)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyState)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance (familyExcitation_norm_floor)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondOrbit (family_rayleigh_floor)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
  (DyadicSmoothedTrajectory trajWidth trajWidth_ratio)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor
  (PathShiftedEpsBound PathShiftedNondegenerate shiftedPathAnchor ShiftedAnchorPackage)
open YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival (PathShiftedWindowSurvival)
open YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate
  (PathFacesPadded paddedNondegFloor paddedNondegFloor_pos paddedZeroMomentumTrajectory
   paddedZeroMomentum_padded)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
  (afPaddedZeroMomentumTrajectory afPaddedZeroMomentum_padded)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprShiftedAnchorPackage

/-! ## 1. The embedding and definitional agreement -/

/-- A plaquette trajectory as an expression anchor trajectory. -/
def toExprTrajectory (tr : DyadicSmoothedTrajectory) : ExprAnchorTrajectory where
  schedule := tr.schedule
  width := trajWidth
  radius := tr.radius
  expr := fun j => familyState (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j)

theorem toExpr_vector (tr : DyadicSmoothedTrajectory) (j : Nat) :
    (toExprTrajectory tr).vector j = tr.familyVector j := rfl

theorem toExpr_state (tr : DyadicSmoothedTrajectory) (j : Nat) :
    (toExprTrajectory tr).state j = tr.state j := rfl

theorem toExpr_response (tr : DyadicSmoothedTrajectory) (j n : Nat) :
    (toExprTrajectory tr).response j n = tr.response j n := rfl

theorem toExpr_epsBound_iff (tr : DyadicSmoothedTrajectory) (c0 : Q') :
    ExprShiftedEpsBound (toExprTrajectory tr) c0 ↔ PathShiftedEpsBound tr c0 := Iff.rfl

theorem toExpr_window_iff (tr : DyadicSmoothedTrajectory) (theta : Q') :
    ExprShiftedWindowSurvival (toExprTrajectory tr) theta ↔ PathShiftedWindowSurvival tr theta :=
  Iff.rfl

theorem toExpr_nondeg_iff (tr : DyadicSmoothedTrajectory) (fl : Nat → Q') :
    ExprShiftedNondegenerate (toExprTrajectory tr) fl ↔ PathShiftedNondegenerate tr fl :=
  Iff.rfl

theorem toExpr_anchor (tr : DyadicSmoothedTrajectory) (delta : Q') (hdelta : delta < (1 : Q'))
    (a : Nat) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j) (j : Nat) :
    exprShiftedPathAnchor (toExprTrajectory tr) delta hdelta a fl hfl j =
      shiftedPathAnchor tr delta hdelta a fl hfl j := rfl

/-- The general package IS the existing one on plaquette trajectories. -/
theorem toExpr_package_iff (tr : DyadicSmoothedTrajectory) (delta : Q')
    (hdelta : delta < (1 : Q')) (a : Nat) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j) :
    ExprShiftedAnchorPackage (toExprTrajectory tr) delta hdelta a fl hfl ↔
      ShiftedAnchorPackage tr delta hdelta a fl hfl := Iff.rfl

/-! ## 2. H-var and H-ray from the existing plaquette floors -/

/-- `v_j = varianceFloor(w_j) · Σ_p c_j(p)²`. -/
def paddedVar (tr : DyadicSmoothedTrajectory) (j : Nat) : Q' :=
  varianceFloor (tr.schedule.nome j) (tr.schedule.nome_pos j) *
    listQSum (fun face => tr.coeff j face * tr.coeff j face) (tr.faces j)

/-- `ρ_j = familyResponseFraction(w_j, |faces_j|)`. -/
def paddedRho (tr : DyadicSmoothedTrajectory) (j : Nat) : Q' :=
  familyResponseFraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.faces j).length

/-- H-var holds for every plaquette trajectory (signed-family coercivity). -/
theorem toExpr_hvar (tr : DyadicSmoothedTrajectory) :
    ExprHVar (toExprTrajectory tr) (paddedVar tr) := fun j =>
  ⟨Q'.mul_pos (varianceFloor_positive (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j))
      (tr.coeff_mass_pos j),
    familyExcitation_norm_floor (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.faces_nodup j)⟩

/-- H-ray holds for every padded plaquette trajectory (family band response). -/
theorem toExpr_hray (tr : DyadicSmoothedTrajectory) (hpad : PathFacesPadded tr) :
    ExprHRay (toExprTrajectory tr) (paddedRho tr) := fun j =>
  ⟨familyResponseFraction_positive (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) _,
    family_rayleigh_floor (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (trajWidth_ratio j) (tr.faces j) (tr.coeff j) (hpad j)⟩

/-- The general floor `ρ_j^(2M_j+side_j) v_j` IS `paddedNondegFloor`. -/
theorem toExpr_floor (tr : DyadicSmoothedTrajectory) (j : Nat) :
    exprNondegFloor (toExprTrajectory tr) (paddedVar tr) (paddedRho tr) j =
      paddedNondegFloor tr j := rfl

/-- `pathShiftedNondegenerate_of_padded`, reproved through the general layer. -/
theorem padded_nondegenerate_via_expr (tr : DyadicSmoothedTrajectory)
    (hpad : PathFacesPadded tr) : PathShiftedNondegenerate tr (paddedNondegFloor tr) :=
  (toExpr_nondeg_iff tr _).mp
    (exprShiftedNondegenerate_of_hvar_hray (toExprTrajectory tr) (paddedVar tr) (paddedRho tr)
      (toExpr_hvar tr) (toExpr_hray tr hpad))

/-- `path_normalized_anchor_of_windowSurvival_padded`, reproved from the general
package (`expr_normalized_anchor_of_windowSurvival_hvar_hray`). -/
theorem padded_package_via_expr (tr : DyadicSmoothedTrajectory)
    (c0 theta delta : Q') (a : Nat) (ha : 1 ≤ a)
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : (1 : Q') ≤ c0)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : c0 ≤ Q'.ofNat (side a) * delta)
    (hpad : PathFacesPadded tr) (Hw : PathShiftedWindowSurvival tr theta) :
    ShiftedAnchorPackage tr delta hdelta a (paddedNondegFloor tr) (paddedNondegFloor_pos tr) :=
  (toExpr_package_iff tr delta hdelta a _ _).mp
    (expr_normalized_anchor_of_windowSurvival_hvar_hray (toExprTrajectory tr) c0 theta delta a
      ha h0 h1 hc0 hc1 hdelta0 hdelta hcd (paddedVar tr) (paddedRho tr)
      (toExpr_hvar tr) (toExpr_hray tr hpad) ((toExpr_window_iff tr theta).mpr Hw))

/-! ## 3. Concrete instances -/

/-- The concrete padded zero-momentum trajectory as an expression anchor. -/
def paddedZeroMomentumExpr : ExprAnchorTrajectory := toExprTrajectory paddedZeroMomentumTrajectory

theorem paddedZeroMomentumExpr_hvar :
    ExprHVar paddedZeroMomentumExpr (paddedVar paddedZeroMomentumTrajectory) :=
  toExpr_hvar _

theorem paddedZeroMomentumExpr_hray :
    ExprHRay paddedZeroMomentumExpr (paddedRho paddedZeroMomentumTrajectory) :=
  toExpr_hray _ paddedZeroMomentum_padded

/-- The AF-scheduled padded trajectory as an expression anchor. -/
def afPaddedZeroMomentumExpr : ExprAnchorTrajectory :=
  toExprTrajectory afPaddedZeroMomentumTrajectory

theorem afPaddedZeroMomentumExpr_hvar :
    ExprHVar afPaddedZeroMomentumExpr (paddedVar afPaddedZeroMomentumTrajectory) :=
  toExpr_hvar _

theorem afPaddedZeroMomentumExpr_hray :
    ExprHRay afPaddedZeroMomentumExpr (paddedRho afPaddedZeroMomentumTrajectory) :=
  toExpr_hray _ afPaddedZeroMomentum_padded

#print axioms toExprTrajectory
#print axioms toExpr_vector
#print axioms toExpr_state
#print axioms toExpr_response
#print axioms toExpr_epsBound_iff
#print axioms toExpr_window_iff
#print axioms toExpr_nondeg_iff
#print axioms toExpr_anchor
#print axioms toExpr_package_iff
#print axioms toExpr_hvar
#print axioms toExpr_hray
#print axioms toExpr_floor
#print axioms padded_nondegenerate_via_expr
#print axioms padded_package_via_expr
#print axioms paddedZeroMomentumExpr_hvar
#print axioms paddedZeroMomentumExpr_hray
#print axioms afPaddedZeroMomentumExpr_hvar
#print axioms afPaddedZeroMomentumExpr_hray

end YMGap.Continuum.BF4WilsonAllNomeExprAnchorRegression
