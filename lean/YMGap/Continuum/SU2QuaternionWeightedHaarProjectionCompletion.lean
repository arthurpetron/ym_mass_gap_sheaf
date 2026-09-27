/-
Coordinate Haar projections on the SAME certified spectator-weighted GNS
completion.  Independence of a coordinate is an explicit algebraic premise;
these are comparator projections, not original-action conditionals.
-/

import YMGap.Continuum.SU2QuaternionWeightedHaarBlockProjection
import YMGap.Continuum.SU2QuaternionHaarBoundedCompletion
import YMGap.Continuum.GNSPairingNormBound

namespace YMGap.Continuum.SU2QuaternionWeightedHaarProjectionCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionWeightedHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBoundedCompletion
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

private theorem project_smul (block : Nat) (c : Q') (f : RatPoly) :
    RatPolyCoeffEqv (project block (polySmul c f)) (polySmul c (project block f)) := by
  have ht : RatPolyTermwiseEqv
      (project block (polySmul c f)) (polySmul c (project block f)) := by
    induction f with
    | nil => exact True.intro
    | cons t rest ih => exact ⟨rfl, Q'.mul_assoc_eqv _ _ _, ih⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

/-- The explicit coefficient-one bounded coordinate map under a certified
spectator weight. -/
def projectionMap (blocks : Nat) (W : RatPoly) (H : Certificate blocks W)
    (block : Nat) (hb : block < blocks) (hW : QuaternionBlockIndependent block W) :
    BoundedMap (weightedGNSData blocks W H) (1 : Q') where
  toFun p := ⟨project block p.val, project_supported block p.property⟩
  nonnegative := by decide
  map_sub := by
    intro p q
    change RatPolyCoeffEqv
      (project block (polyAdd p.val (polySmul (-1) q.val)))
      (polyAdd (project block p.val) (polySmul (-1) (project block q.val)))
    rw [project_add]
    exact (RatPolyCoeffEqv.refl _).add (project_smul block (-1) q.val)
  norm_bound := by
    intro p
    change weightedPair blocks W (project block p.val) (project block p.val) ≤
      ((1:Q')*1)*weightedPair blocks W p.val p.val
    exact Q'.le_trans' _ _ _
      (weighted_project_square_contraction blocks block hb W p.val H hW p.property)
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv (1:Q')))
        (Q'.one_mul_eqv _))))

/-- The actual map on the certified weighted completion. -/
def projection (blocks : Nat) (W : RatPoly) (H : Certificate blocks W)
    (block : Nat) (hb : block < blocks) (hW : QuaternionBlockIndependent block W) :
    GNSCompletionSpace (weightedGNSData blocks W H) →
      GNSCompletionSpace (weightedGNSData blocks W H) :=
  (projectionMap blocks W H block hb hW).completionMap

theorem projection_embed (blocks : Nat) (W : RatPoly) (H : Certificate blocks W)
    (block : Nat) (hb : block < blocks) (hW : QuaternionBlockIndependent block W)
    (p : (weightedGNSData blocks W H).V) :
    projection blocks W H block hb hW (embedV (weightedGNSData blocks W H) p) =
      embedV (weightedGNSData blocks W H) ⟨project block p.val,
        project_supported block p.property⟩ :=
  (projectionMap blocks W H block hb hW).completionMap_embed p

private theorem null_of_pointwise_veq (D : GNSData) (X Y : CauchyGNS D)
    (h : ∀ n, D.veq (X.seq n) (Y.seq n)) : CauchyNull D X Y := by
  intro epsilon hepsilon
  refine ⟨0, fun n _ => ?_⟩
  have hr : D.rad (X.seq n) (Y.seq n) := by
    exact Q'.eqv_trans _ _ _
      (D.B_diag_congr (D.add_congr (h n) (D.veq_refl (D.neg (Y.seq n)))))
      (D.rad_refl (Y.seq n))
  exact Q'.le_trans' _ 0 epsilon (Q'.le_of_eqv hr) (Q'.le_of_lt hepsilon)

theorem projection_idempotent (blocks : Nat) (W : RatPoly) (H : Certificate blocks W)
    (block : Nat) (hb : block < blocks) (hW : QuaternionBlockIndependent block W)
    (x : GNSCompletionSpace (weightedGNSData blocks W H)) :
    projection blocks W H block hb hW (projection blocks W H block hb hW x) =
      projection blocks W H block hb hW x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  apply null_of_pointwise_veq
  intro n
  exact project_idempotent block (X.seq n).val

theorem projection_comm (blocks : Nat) (W : RatPoly) (H : Certificate blocks W)
    (left right : Nat) (hl : left < blocks) (hr : right < blocks)
    (hWl : QuaternionBlockIndependent left W)
    (hWr : QuaternionBlockIndependent right W)
    (x : GNSCompletionSpace (weightedGNSData blocks W H)) :
    projection blocks W H left hl hWl (projection blocks W H right hr hWr x) =
      projection blocks W H right hr hWr (projection blocks W H left hl hWl x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  apply null_of_pointwise_veq
  intro n
  exact project_comm left right (X.seq n).val

theorem projection_selfAdjoint (blocks : Nat) (W : RatPoly) (H : Certificate blocks W)
    (block : Nat) (hb : block < blocks) (hW : QuaternionBlockIndependent block W)
    (x y : GNSCompletionSpace (weightedGNSData blocks W H)) :
    (weightedGNSData blocks W H).cinnerCompl (projection blocks W H block hb hW x) y =
      (weightedGNSData blocks W H).cinnerCompl x (projection blocks W H block hb hW y) := by
  let D := weightedGNSData blocks W H
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal ?_
    (CReal.convergesTo_ofQ'CauchySeq _ _) (CReal.convergesTo_ofQ'CauchySeq _ _)
  intro n
  exact CReal.ofQ'_equiv_of_eqv
    (weighted_project_selfAdjoint blocks block hb W (X.seq n).val (Y.seq n).val hW)

theorem projection_norm (blocks : Nat) (W : RatPoly) (H : Certificate blocks W)
    (block : Nat) (hb : block < blocks) (hW : QuaternionBlockIndependent block W)
    (x : GNSCompletionSpace (weightedGNSData blocks W H)) :
    CReal.RCle
      ((weightedGNSData blocks W H).cinnerCompl
        (projection blocks W H block hb hW x) (projection blocks W H block hb hW x))
      ((weightedGNSData blocks W H).cinnerCompl x x) := by
  let D := weightedGNSData blocks W H
  apply YMGap.Continuum.GNSPairingNormBound.norm_le_of_self_pairing D
  have hs := projection_selfAdjoint blocks W H block hb hW x
    (projection blocks W H block hb hW x)
  rw [projection_idempotent blocks W H block hb hW x] at hs
  exact Eq.trans hs (D.cinnerCompl_comm x (projection blocks W H block hb hW x))

theorem projection_fixed_cauchy (blocks : Nat) (W : RatPoly) (H : Certificate blocks W)
    (block : Nat) (hb : block < blocks) (hW : QuaternionBlockIndependent block W)
    (X : CauchyGNS (weightedGNSData blocks W H))
    (hX : ∀ n, QuaternionBlockIndependent block (X.seq n).val) :
    projection blocks W H block hb hW (Quotient.mk (cauchySetoid _) X) =
      Quotient.mk (cauchySetoid _) X := by
  apply Quotient.sound
  apply null_of_pointwise_veq
  intro n
  exact project_fixed block (X.seq n).val (hX n)

theorem projection_sub (blocks : Nat) (W : RatPoly) (H : Certificate blocks W)
    (block : Nat) (hb : block < blocks) (hW : QuaternionBlockIndependent block W)
    (x y : GNSCompletionSpace (weightedGNSData blocks W H)) :
    projection blocks W H block hb hW ((weightedGNSData blocks W H).cSub x y) =
      (weightedGNSData blocks W H).cSub
        (projection blocks W H block hb hW x)
        (projection blocks W H block hb hW y) := by
  let D := weightedGNSData blocks W H
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply Quotient.sound
  apply null_of_pointwise_veq
  intro n
  exact (projectionMap blocks W H block hb hW).map_sub (X.seq n) (Y.seq n)

#print axioms projectionMap
#print axioms projection
#print axioms projection_embed
#print axioms projection_idempotent
#print axioms projection_comm
#print axioms projection_selfAdjoint
#print axioms projection_norm
#print axioms projection_fixed_cauchy
#print axioms projection_sub

end YMGap.Continuum.SU2QuaternionWeightedHaarProjectionCompletion
