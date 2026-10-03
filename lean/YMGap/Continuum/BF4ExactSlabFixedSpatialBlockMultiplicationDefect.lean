/-
# Original finite-block multiplication defect

Every iterate here is the original K(x,y)V(x) transfer step. The exact
recurrence retains its spatial action at every step; it does not replace
the interacting transfer by a bare character eigenvalue. Constant shifts
of the observable leave this defect unchanged. These are signed coefficient
identities, not a norm estimate, favorable gain, or scaling assertion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing
import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
  (transferStep_add transferStep_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Actual t-step source, including every original spatial action factor. -/
def originalBlockTransfer (w : Q') (K width t : Nat) (p : RatPoly) : RatPoly :=
  iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) t p

/-- Literal signed commutator of multiplication with the original block. -/
def blockMultiplicationDefect (w : Q') (K width t : Nat) (g f : RatPoly) : RatPoly :=
  polyAdd (originalBlockTransfer w K width t (polyMul g f))
    (polyNeg (polyMul f (originalBlockTransfer w K width t g)))

attribute [local irreducible] baseLinks kineticWeight spatialWeight

private theorem block_succ (w : Q') (K width t : Nat) (p : RatPoly) :
    originalBlockTransfer w K width (t+1) p =
      transferStep w K width (originalBlockTransfer w K width t p) := by
  simpa only [originalBlockTransfer, iterateStep, transferStep] using
    iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) t 1 p

private theorem transfer_congr (w : Q') (K width : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (transferStep w K width p) (transferStep w K width q) :=
  partialHaarHeads_congr (N width)
    ((h.mul_left (spatialWeight w K width)).mul_left (kineticWeight w K width))

private theorem transfer_neg (w : Q') (K width : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (transferStep w K width (polyNeg p))
      (polyNeg (transferStep w K width p)) :=
  (transfer_congr w K width (neg_smul p)).trans
    ((transferStep_smul w K width (-1) p).trans
      (neg_smul (transferStep w K width p)).symm)

private theorem block_congr (w : Q') (K width : Nat) :
    (t : Nat) → {p q : RatPoly} → RatPolyCoeffEqv p q →
      RatPolyCoeffEqv (originalBlockTransfer w K width t p)
        (originalBlockTransfer w K width t q)
  | 0, _, _, h => h
  | t+1, _, _, h => by
      rw [block_succ, block_succ]
      exact transfer_congr w K width (block_congr w K width t h)

private theorem block_add (w : Q') (K width : Nat) :
    (t : Nat) → (p q : RatPoly) →
      RatPolyCoeffEqv (originalBlockTransfer w K width t (polyAdd p q))
        (polyAdd (originalBlockTransfer w K width t p) (originalBlockTransfer w K width t q))
  | 0, _, _ => RatPolyCoeffEqv.refl _
  | t+1, p, q => by
      rw [block_succ, block_succ, block_succ]
      exact (transfer_congr w K width (block_add w K width t p q)).trans
        (transferStep_add w K width _ _)

private theorem block_smul (w : Q') (K width : Nat) :
    (t : Nat) → (c : Q') → (p : RatPoly) →
      RatPolyCoeffEqv (originalBlockTransfer w K width t (polySmul c p))
        (polySmul c (originalBlockTransfer w K width t p))
  | 0, _, _ => RatPolyCoeffEqv.refl _
  | t+1, c, p => by
      rw [block_succ, block_succ]
      exact (transfer_congr w K width (block_smul w K width t c p)).trans
        (transferStep_smul w K width c _)

/-- At zero steps the original multiplication defect is identically zero. -/
theorem blockMultiplicationDefect_zero (w : Q') (K width : Nat) (g f : RatPoly) :
    RatPolyCoeffEqv (blockMultiplicationDefect w K width 0 g f) polyZero := by
  change RatPolyCoeffEqv (polyAdd (polyMul g f) (polyNeg (polyMul f g))) polyZero
  exact ((RatPolyCoeffEqv.mul_comm g f).add (neg_smul (polyMul f g))).trans
    (RatPolyCoeffEqv.add_neg_smul (polyMul f g))

/-- Genuine original recurrence: the old defect is transferred with V,
and the new one-step commutator acts on the actual evolved source. -/
theorem blockMultiplicationDefect_succ (w : Q') (K width t : Nat) (g f : RatPoly) :
    RatPolyCoeffEqv (blockMultiplicationDefect w K width (t+1) g f)
      (polyAdd (transferStep w K width (blockMultiplicationDefect w K width t g f))
        (blockMultiplicationDefect w K width 1
          (originalBlockTransfer w K width t g) f)) := by
  let u := originalBlockTransfer w K width t g
  let v := originalBlockTransfer w K width t (polyMul g f)
  have hlinear : RatPolyCoeffEqv
      (transferStep w K width (polyAdd v (polyNeg (polyMul f u))))
      (polyAdd (transferStep w K width v) (polyNeg (transferStep w K width (polyMul f u)))) :=
    (transferStep_add w K width v _).trans
      ((RatPolyCoeffEqv.refl _).add (transfer_neg w K width _))
  have hcomm : RatPolyCoeffEqv (transferStep w K width (polyMul u f))
      (transferStep w K width (polyMul f u)) :=
    transfer_congr w K width (RatPolyCoeffEqv.mul_comm u f)
  have hcancel : RatPolyCoeffEqv
      (polyAdd (polyAdd (transferStep w K width v) (polyNeg (transferStep w K width (polyMul f u))))
        (polyAdd (transferStep w K width (polyMul f u)) (polyNeg (polyMul f (transferStep w K width u)))))
      (polyAdd (transferStep w K width v) (polyNeg (polyMul f (transferStep w K width u)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
      (.add (.var 0) (.neg (.var 2))) (by decide)
      (fun
        | 0 => transferStep w K width v
        | 1 => transferStep w K width (polyMul f u)
        | _ => polyMul f (transferStep w K width u))
  have h := (hlinear.add (hcomm.add (RatPolyCoeffEqv.refl _))).trans hcancel
  unfold blockMultiplicationDefect
  rw [block_succ w K width t (polyMul g f), block_succ w K width t g]
  exact h.symm

private theorem product_shift (g f : RatPoly) (c : Q') :
    RatPolyCoeffEqv (polyMul g (shifted f c))
      (polyAdd (polyMul g f) (polySmul (-c) g)) := by
  have hstart : RatPolyCoeffEqv (polyMul g (shifted f c))
      (polyMul g (polyAdd f (polySmul (-c) polyOne))) :=
    ((RatPolyCoeffEqv.one_smul f).add (RatPolyCoeffEqv.refl _)).mul_left g
  have hfinish : RatPolyCoeffEqv (polyMul g (polyAdd f (polySmul (-c) polyOne)))
      (polyAdd (polyMul g f) (polySmul (-c) g)) := by
    exact (RatPolyCoeffEqv.mul_add_right g f (polySmul (-c) polyOne)).trans
      ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.polyMul_smul_right (-c) g polyOne).trans
          ((RatPolyCoeffEqv.mul_one g).smul (-c))))
  exact hstart.trans hfinish

/-- Constant-shift invariance with the SAME original source and transfer.
In particular, this permits the computed OWN mean without a centered eigenpin. -/
theorem blockMultiplicationDefect_shifted (w : Q') (K width t : Nat)
    (g f : RatPoly) (c : Q') :
    RatPolyCoeffEqv (blockMultiplicationDefect w K width t g (shifted f c))
      (blockMultiplicationDefect w K width t g f) := by
  let u := originalBlockTransfer w K width t g
  let v := originalBlockTransfer w K width t (polyMul g f)
  have hfirst : RatPolyCoeffEqv (originalBlockTransfer w K width t (polyMul g (shifted f c)))
      (polyAdd v (polySmul (-c) u)) :=
    (block_congr w K width t (product_shift g f c)).trans
      ((block_add w K width t _ _).trans
        ((RatPolyCoeffEqv.refl _).add (block_smul w K width t (-c) g)))
  have hsecond : RatPolyCoeffEqv (polyMul (shifted f c) u)
      (polyAdd (polyMul f u) (polySmul (-c) u)) :=
    (RatPolyCoeffEqv.mul_comm _ _).trans
      ((product_shift u f c).trans
        ((RatPolyCoeffEqv.mul_comm u f).add (RatPolyCoeffEqv.refl _)))
  exact (hfirst.add (RatPolyCoeffEqv.neg hsecond)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 2)) (.neg (.add (.var 1) (.var 2))))
      (.add (.var 0) (.neg (.var 1))) (by decide)
      (fun
        | 0 => v
        | 1 => polyMul f u
        | _ => polySmul (-c) u))

#print axioms originalBlockTransfer
#print axioms blockMultiplicationDefect
#print axioms blockMultiplicationDefect_zero
#print axioms blockMultiplicationDefect_succ
#print axioms blockMultiplicationDefect_shifted

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect
