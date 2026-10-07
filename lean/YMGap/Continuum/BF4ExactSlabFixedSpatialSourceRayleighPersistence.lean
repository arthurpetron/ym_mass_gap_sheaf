/-
# Persistence of a source Rayleigh floor under the original finite transfer

For the actual V-weighted pairing, one-step quadratic positivity and weighted
symmetry propagate a source Rayleigh lower bound to every iterate of the
original fixed-spatial transfer. The proof uses positivity of the weighted
norm and of the transfer quadratic on `T b - rho*b`; it neither divides by a
source norm nor invokes a spectral theorem. This is a finite-cutoff statement,
not an operator or continuum gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSourceRayleighPersistence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_quadratic_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (transferStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (transferStep_add transferStep_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarSquareCertificate (Certificate supported_add)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep iterateStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] baseLinks weightedMass transferStep

/-- The actual, unnormalised V-weighted pairing. -/
def pair (w : Q') (K width : Nat) (f g : RatPoly) : Q' :=
  weightedMass w K width (polyMul f g)

private theorem pair_congr (w : Q') (K width : Nat) {f f' g g' : RatPoly}
    (hf : RatPolyCoeffEqv f f') (hg : RatPolyCoeffEqv g g') :
    pair w K width f g ≈ pair w K width f' g' :=
  weightedMass_congr w K width (hf.mul hg)

private theorem pair_add_right (w : Q') (K width : Nat) (f g h : RatPoly) :
    pair w K width f (polyAdd g h) ≈
      pair w K width f g + pair w K width f h := by
  exact Q'.eqv_trans _ _ _
    (weightedMass_congr w K width (RatPolyCoeffEqv.mul_add_right f g h))
    (weightedMass_add w K width _ _)

private theorem pair_add_left (w : Q') (K width : Nat) (f g h : RatPoly) :
    pair w K width (polyAdd f g) h ≈
      pair w K width f h + pair w K width g h := by
  exact Q'.eqv_trans _ _ _
    (weightedMass_congr w K width
      ((RatPolyCoeffEqv.mul_comm _ _).trans
        ((RatPolyCoeffEqv.mul_add_right h f g).trans
          ((RatPolyCoeffEqv.mul_comm _ _).add (RatPolyCoeffEqv.mul_comm _ _)))))
    (weightedMass_add w K width _ _)

private theorem pair_smul_right (w : Q') (K width : Nat) (c : Q')
    (f g : RatPoly) :
    pair w K width f (polySmul c g) ≈ c * pair w K width f g := by
  exact Q'.eqv_trans _ _ _
    (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_right c f g))
    (weightedMass_smul w K width c _)

private theorem pair_smul_left (w : Q') (K width : Nat) (c : Q')
    (f g : RatPoly) :
    pair w K width (polySmul c f) g ≈ c * pair w K width f g := by
  exact Q'.eqv_trans _ _ _
    (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_left c f g))
    (weightedMass_smul w K width c _)

private theorem pair_symmetric (w : Q') (K width : Nat) (f g : RatPoly) :
    pair w K width f g ≈ pair w K width g f :=
  weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm f g)

private theorem pair_sub_expand (w rho : Q') (K width : Nat)
    (a b c d : RatPoly) :
    pair w K width (polyAdd a (polySmul (-rho) b))
      (polyAdd c (polySmul (-rho) d)) ≈
      pair w K width a c + -(rho * pair w K width a d) +
        (-(rho * pair w K width b c) +
          (rho * rho) * pair w K width b d) := by
  have h := pair_add_left w K width a (polySmul (-rho) b)
      (polyAdd c (polySmul (-rho) d))
  have h0 := pair_add_right w K width a c (polySmul (-rho) d)
  have h1 := pair_add_right w K width (polySmul (-rho) b) c (polySmul (-rho) d)
  have h2 := pair_smul_right w K width (-rho) a d
  have h3 := pair_smul_left w K width (-rho) b c
  have h4 := pair_smul_left w K width (-rho) b (polySmul (-rho) d)
  have h5 := pair_smul_right w K width (-rho) b d
  have h6 : ((-rho) * ((-rho) * pair w K width b d)).eqv
      ((rho * rho) * pair w K width b d) :=
    poly_identity_of_normal_eq
      (.mul (.neg (.var 0)) (.mul (.neg (.var 0)) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.var 1))
      (by decide) (fun | 0 => rho | _ => pair w K width b d)
  have hleft := Q'.eqv_trans _ _ _ h0
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ h2 (Q'.neg_mul_eqv rho (pair w K width a d))))
  have hright := Q'.eqv_trans _ _ _ h1
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ h3 (Q'.neg_mul_eqv rho (pair w K width b c)))
      (Q'.eqv_trans _ _ _ h4
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h5) h6)))
  exact Q'.eqv_trans _ _ _ h (Q'.add_eqv_congr' hleft hright)

private theorem persistence_identity (rho R0 R1 R2 R3 : Q') :
    (R3 + -(rho*R2) + (-(rho*R2)+(rho*rho)*R1)) +
        rho*(R2 + -(rho*R1) + (-(rho*R1)+(rho*rho)*R0)) +
        (rho*rho)*(R1 + -(rho*R0)) ≈ R3 + -(rho*R2) := by
  let r : PolyExpr := .var 0
  let p0 : PolyExpr := .var 1
  let p1 : PolyExpr := .var 2
  let p2 : PolyExpr := .var 3
  let p3 : PolyExpr := .var 4
  let square : PolyExpr := .mul r r
  let norm : PolyExpr := .add (.add p2 (.neg (.mul r p1)))
    (.add (.neg (.mul r p1)) (.mul square p0))
  let quad : PolyExpr := .add (.add p3 (.neg (.mul r p2)))
    (.add (.neg (.mul r p2)) (.mul square p1))
  exact poly_identity_of_normal_eq
    (.add (.add quad (.mul r norm)) (.mul square (.add p1 (.neg (.mul r p0)))))
    (.add p3 (.neg (.mul r p2))) (by decide)
    (fun | 0 => rho | 1 => R0 | 2 => R1 | 3 => R2 | _ => R3)

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Supportedness of every actual source block. -/
theorem sourceRayleigh_supported (w : Q') (K width t : Nat) {c : RatPoly}
    (hc : SupportedQuaternionBlocks (N width) c) :
    SupportedQuaternionBlocks (N width) (originalBlockTransfer w K width t c) := by
  change SupportedQuaternionBlocks (N width)
    (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) t c)
  exact iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) t hc

private theorem block_succ (w : Q') (K width t : Nat) (c : RatPoly) :
    originalBlockTransfer w K width (t+1) c =
      transferStep w K width (originalBlockTransfer w K width t c) := by
  change iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width)
      (t+1) c = _
  simpa only [transferStep] using
    (iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width)
      t 1 c)

private theorem step_linear (w rho : Q') (K width : Nat) (b : RatPoly) :
    RatPolyCoeffEqv (transferStep w K width
        (polyAdd (transferStep w K width b) (polySmul (-rho) b)))
      (polyAdd (transferStep w K width (transferStep w K width b))
        (polySmul (-rho) (transferStep w K width b))) := by
  exact (transferStep_add w K width _ _).trans
    ((RatPolyCoeffEqv.refl _).add (transferStep_smul w K width (-rho) b))

/-- One-step persistence from the actual quadratic, weighted symmetry, and
the initial Rayleigh comparison. Norm positivity supplies the second positive
term. No strict positivity or inverse of the source norm is assumed. -/
theorem sourceRayleigh_floor_step {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) {c : RatPoly}
    (hc : SupportedQuaternionBlocks (N width) c) {rho : Q'}
    (hrho : (0 : Q') ≤ rho)
    (hfloor : rho * pair w K width c c ≤
      pair w K width c (transferStep w K width c)) :
    rho * pair w K width (transferStep w K width c) (transferStep w K width c) ≤
      pair w K width (transferStep w K width c)
        (transferStep w K width (transferStep w K width c)) := by
  let Tc := transferStep w K width c
  let T2c := transferStep w K width Tc
  let y := polyAdd Tc (polySmul (-rho) c)
  let Ty := transferStep w K width y
  let R0 := pair w K width c c
  let R1 := pair w K width c Tc
  let R2 := pair w K width Tc Tc
  let R3 := pair w K width Tc T2c
  have hTc : SupportedQuaternionBlocks (N width) Tc := transferStep_supported w K width hc
  have hy : SupportedQuaternionBlocks (N width) y :=
    supported_add hTc (support_smul hc (-rho))
  have hyNorm : (0 : Q') ≤ pair w K width y y :=
    weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square y hy)
  have hyTransfer : (0 : Q') ≤ pair w K width y Ty :=
    transferStep_quadratic_nonnegative w (Q'.le_of_lt hw0) K width y hy
  have hTy : RatPolyCoeffEqv Ty
      (polyAdd T2c (polySmul (-rho) Tc)) := step_linear w rho K width c
  have hTcross : pair w K width c T2c ≈ R2 := by
    change pair w K width c (transferStep w K width Tc) ≈
      pair w K width (transferStep w K width c) Tc
    exact transferStep_weighted_symmetric w K width hTc hc
  have hselfCross : pair w K width Tc c ≈ R1 :=
    pair_symmetric w K width Tc c
  have hnormExpand := pair_sub_expand w rho K width Tc c Tc c
  have hTExpand := pair_sub_expand w rho K width Tc c T2c Tc
  have hnormForm : pair w K width y y ≈
      R2 + -(rho * R1) + (-(rho * R1) + (rho * rho) * R0) := by
    dsimp only [y, R2, R1, R0]
    exact Q'.eqv_trans _ _ _ hnormExpand
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr_left _ _ _
          (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hselfCross)))
        (Q'.add_eqv_congr'
          (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_refl _)))
          (Q'.eqv_refl _)))
  have htransferForm : pair w K width y Ty ≈
      R3 + -(rho * R2) + (-(rho * R2) + (rho * rho) * R1) := by
    exact Q'.eqv_trans _ _ _
      (pair_congr w K width (RatPolyCoeffEqv.refl _) hTy)
      (Q'.eqv_trans _ _ _ hTExpand
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_refl _))
          (Q'.add_eqv_congr'
            (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hTcross))
            (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_refl _)))))
  have hgap : (0 : Q') ≤ R1 + -(rho * R0) :=
    Q'.sub_nonneg_of_le (by simpa only [R0, R1] using hfloor)
  have hrho2 : (0 : Q') ≤ rho * rho := Q'.mul_nonneg _ _ hrho hrho
  have hnormTerm : (0 : Q') ≤ rho * pair w K width y y :=
    Q'.mul_nonneg _ _ hrho hyNorm
  have hgapTerm : (0 : Q') ≤ (rho * rho) * (R1 + -(rho * R0)) :=
    Q'.mul_nonneg _ _ hrho2 hgap
  have hsum : (0 : Q') ≤ pair w K width y Ty +
      rho * pair w K width y y +
        (rho * rho) * (R1 + -(rho * R0)) :=
    Q'.zero_le_add _ _ (Q'.zero_le_add _ _ hyTransfer hnormTerm) hgapTerm
  have hidentity :
      (pair w K width y Ty + rho * pair w K width y y +
        (rho * rho) * (R1 + -(rho * R0))).eqv (R3 + -(rho * R2)) := by
    calc
      _ ≈ (R3 + -(rho * R2) + (-(rho * R2) + (rho * rho) * R1)) +
          rho * (R2 + -(rho * R1) + (-(rho * R1) + (rho * rho) * R0)) +
          (rho * rho) * (R1 + -(rho * R0)) := by
            exact Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.eqv_trans _ _ _ htransferForm (Q'.eqv_refl _))
                (Q'.mul_eqv_congr_left _ _ _ hnormForm))
              (Q'.eqv_refl _)
      _ ≈ R3 + -(rho * R2) := persistence_identity rho R0 R1 R2 R3
  have htarget : (0 : Q') ≤ R3 + -(rho * R2) :=
    Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hidentity)
  exact Q'.le_of_sub_nonneg (by simpa only [R3, R2, Tc, T2c] using htarget)

/-- Every actual original block iterate retains the source Rayleigh floor.
This is a finite, fixed-cutoff persistence statement; it does not assert a
uniform cutoff, volume, or continuum spectral gap. -/
theorem sourceRayleigh_floor_persists {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) {c : RatPoly}
    (hc : SupportedQuaternionBlocks (N width) c) {rho : Q'}
    (hrho : (0 : Q') ≤ rho)
    (hfloor : rho * pair w K width c c ≤
      pair w K width c (transferStep w K width c)) (t : Nat) :
    let b := originalBlockTransfer w K width t c
    rho * pair w K width b b ≤ pair w K width b (transferStep w K width b) := by
  induction t with
  | zero =>
      simpa only [originalBlockTransfer, iterateStep] using hfloor
  | succ t ih =>
      let b := originalBlockTransfer w K width t c
      have hb : SupportedQuaternionBlocks (N width) b :=
        sourceRayleigh_supported w K width t hc
      have hs := sourceRayleigh_floor_step hw0 hw1 K width hK hb hrho ih
      simpa only [block_succ] using hs

#print axioms sourceRayleigh_supported
#print axioms sourceRayleigh_floor_step
#print axioms sourceRayleigh_floor_persists

end YMGap.Continuum.BF4ExactSlabFixedSpatialSourceRayleighPersistence
