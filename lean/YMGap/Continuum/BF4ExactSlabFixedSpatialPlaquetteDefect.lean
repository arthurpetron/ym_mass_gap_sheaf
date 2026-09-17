/-
# A positive original temporal defect on one fundamental plaquette

The literal source plaquette has character square cap four on its own Haar
carrier. The original odd marginal retains that cap, with its full spatial
weight and both terminal messages. Combining it with the original one-step
plaquette energy floor gives the explicit fraction starRatio(w)/8 in the
existing partition-cleared diagonal defect.

This is ONE plaquette diagonal at every width, boundary depth and late heat
cutoff. It does not estimate signed combinations, time orbits, a completed
vacuum complement, physical mass, or a continuum limit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteEnergyFloor
import YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported plaquette_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovariance
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] weightedMass terminalMessage transferStep plaquette baseLinks

/-- Spin one uses the exact character cap four, not a coefficient norm. -/
def plaquetteSquareBound (width : Nat) (p : Z4Plaq) :
    SquareBound (N width) (characterPolynomial (plaquette width p).scalar 1) 4 :=
  SquareBound.changeCap (by decide : characterBound 1 ≈ (4 : Q'))
    (character_squareBound
      (SquareBound.scalar (plaquette_supported width (N width) (Nat.le_refl _) p)
        (plaquette_unit width (N width) (Nat.le_refl _) p)) 1)

private theorem smul_neg (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

private theorem weighted_square_cap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {d f : RatPoly} {c : Q'}
    (D : Certificate (N width) d) (P : SquareBound (N width) f c) :
    weightedMass w K width (polyMul d (polyMul f f)) ≤ c*weightedMass w K width d := by
  have hn := weightedMass_nonnegative hw0 hw1 K width hK (D.mul P.certificate)
  have he : RatPolyCoeffEqv (polyMul d (gap c f))
      (polyAdd (polyMul d (cap c)) (polySmul (-1) (polyMul d (polyMul f f)))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 2) (.neg (.var 1))))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 0) (.var 1))))
      (by decide) (fun | 0 => d | 1 => polyMul f f | _ => cap c)).trans
      ((RatPolyCoeffEqv.refl _).add (smul_neg _).symm)
  have hc : weightedMass w K width (polyMul d (cap c)) ≈ c*weightedMass w K width d :=
    Q'.eqv_trans _ _ _ (weightedMass_congr w K width
      ((RatPolyCoeffEqv.mul_comm _ _).trans (cap_mul_left c d)))
      (weightedMass_smul w K width c d)
  have hs := Q'.eqv_trans _ _ _ (weightedMass_congr w K width he)
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' hc
        (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) _)
          (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
            (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv hs))

/-- The SAME raw odd-marginal second moment is at most four times its mass. -/
theorem plaquette_mass_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (p : Z4Plaq) :
    let g := terminalMessage w K width n
    let d := polyMul g (transferStep w K width g)
    let c := characterPolynomial (plaquette width p).scalar 1
    weightedMass w K width (polyMul d (polyMul c c)) ≤
      (4 : Q')*weightedMass w K width d := by
  dsimp only
  rw [terminalMessage_next]
  exact weighted_square_cap hw0 hw1 K width hK
    ((terminalMessage_certificate hw0 hw1 K width hK n).mul
      (terminalMessage_certificate hw0 hw1 K width hK (n+1)))
    (plaquetteSquareBound width p)

/-- Explicit fraction for the individual plaquette diagonal. -/
def plaquetteFraction (w : Q') : Q' := starRatio w * Q'.mkPos 1 8 (by decide)

theorem plaquetteFraction_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < plaquetteFraction w :=
  Q'.mul_pos (starRatio_positive hw0 hw1) (by decide)

private theorem scalar_clearing (S Z A B E r : Q')
    (hS : (0 : Q') ≤ S) (hZ : (0 : Q') ≤ Z)
    (hZr : Z*r ≈ 1) (hA : A ≤ (4 : Q')*Z) (hE : S ≤ (2 : Q')*(E*r)) :
    (S*Q'.mkPos 1 8 (by decide))*(Z*A + -(B*B)) ≤ Z*E := by
  let e : Q' := Q'.mkPos 1 8 (by decide)
  let h : Q' := Q'.mkPos 1 2 (by decide)
  have he0 : (0 : Q') ≤ e := by decide
  have hh0 : (0 : Q') ≤ h := by decide
  have hd : (0 : Q') ≤ S*e := Q'.mul_nonneg _ _ hS he0
  have hb : Z*A + -(B*B) ≤ Z*A :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left (Z*A) _ _ (Q'.neg_le_neg (SumOfSquares.q_mul_self_nonneg B)))
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.const 0))) (.var 0) (by decide) (fun _ => Z*A)))
  have hcap := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (S*e) hb hd)
    (Q'.mul_le_mul_of_nonneg_left _ _ (S*e)
      (Q'.mul_le_mul_of_nonneg_left _ _ Z hA hZ) hd)
  have hEZ : S*Z ≤ (2 : Q')*E := by
    have hz := Q'.mul_le_mul_of_nonneg_right _ _ Z hE hZ
    have hp : ((2 : Q')*(E*r))*Z ≈ ((2 : Q')*E)*(Z*r) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 2))
        (.mul (.mul (.const 2) (.var 0)) (.mul (.var 2) (.var 1)))
        (by decide) (fun | 0 => E | 1 => r | _ => Z)
    exact Q'.le_trans' _ _ _ hz (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hp
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hZr) (Q'.mul_one_eqv _))))
  have hfinal := Q'.mul_le_mul_of_nonneg_left _ _ h
    (Q'.mul_le_mul_of_nonneg_right _ _ Z hEZ hZ) hh0
  have he4 : e*(4 : Q') ≈ h := by decide
  have hh2 : h*(2 : Q') ≈ 1 := by decide
  have hl : (S*e)*(Z*((4 : Q')*Z)) ≈ h*((S*Z)*Z) :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.mul (.const 4) (.var 1))))
        (.mul (.mul (.var 2) (.const 4)) (.mul (.mul (.var 0) (.var 1)) (.var 1)))
        (by decide) (fun | 0 => S | 1 => Z | _ => e))
      (Q'.mul_eqv_congr_right _ _ _ he4)
  have hr : h*(((2 : Q')*E)*Z) ≈ Z*E :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 2) (.mul (.mul (.const 2) (.var 0)) (.var 1)))
        (.mul (.mul (.var 2) (.const 2)) (.mul (.var 1) (.var 0)))
        (by decide) (fun | 0 => E | 1 => Z | _ => h))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hh2) (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ hcap
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
      (Q'.le_trans' _ _ _ hfinal (Q'.le_of_eqv hr)))

/-- The original partition-cleared defect is nonnegative on ONE literal
fundamental plaquette, uniformly in width, depth and the cofinal cutoff. -/
theorem plaquette_clearedDefect_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    let c := characterPolynomial (plaquette width p).scalar 1
    (0 : Q') ≤ clearedDefect w (plaquetteFraction w) K width
      (terminalMessage w K width n) c c := by
  let g := terminalMessage w K width n
  let d := polyMul g (transferStep w K width g)
  let c := characterPolynomial (plaquette width p).scalar 1
  let Z := weightedMass w K width d
  let r := Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)
  have hmass : Z ≈ oddMass w K width n := by
    dsimp [Z, d, g]
    rw [terminalMessage_next]
    exact weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _)
  have hZr : Z*r ≈ 1 := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ r hmass)
    (Q'.mul_recipPos_eqv _ (oddMass_positive hw0 hw1 K width hK n))
  apply (clearedDefect_diagonal_nonnegative_iff w (plaquetteFraction w) K width g c).mpr
  exact scalar_clearing (starRatio w) Z _ _ (energy w K width g c) r
    (Q'.le_of_lt (starRatio_positive hw0 hw1))
    (Q'.le_trans' _ _ _ (Q'.le_of_lt (oddMass_positive hw0 hw1 K width hK n))
      (Q'.ge_of_eqv hmass)) hZr
    (plaquette_mass_square_le hw0 hw1 K width hK n p)
    (BF4ExactSlabFixedSpatialPlaquetteEnergyFloor.plaquette_energy_floor
      hw0 hw1 K width hK n p hp)

#print axioms plaquetteSquareBound
#print axioms plaquette_mass_square_le
#print axioms plaquetteFraction
#print axioms plaquetteFraction_positive
#print axioms plaquette_clearedDefect_nonnegative

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDefect
