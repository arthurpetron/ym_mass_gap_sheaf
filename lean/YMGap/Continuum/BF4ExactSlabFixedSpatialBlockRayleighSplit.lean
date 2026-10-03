/-
# Cleared vacuum-subtracted Rayleigh cost on the original block source

For A=T^t g and b=T^t(g*f), keep the two distinct masses
Z0=ell(A*A), Z1=ell(A*T A). The cleared cost Z1*ell(b*b)-Z0*ell(b*T b)
splits into Z0 times the original temporal energy of A*f, a finite
terminal-boundary drift, and one SIGNED multiplication-commutator pairing.
No polynomial inverse, stationary eigenpin, favorable sign, or estimate of
the remaining combined signed cost is assumed. Every transfer retains V.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalRayleighDrift

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (transferStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (transferStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison (comparisonEta)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalRayleighDrift (clearedDrift_abs_le clearedDrift_bounds)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] weightedMass baseLinks

private def pair (w : Q') (K width : Nat) (p q : RatPoly) : Q' :=
  weightedMass w K width (polyMul p q)

private theorem pair_congr (w : Q') (K width : Nat) {p q r s : RatPoly}
    (hp : RatPolyCoeffEqv p q) (hr : RatPolyCoeffEqv r s) :
    pair w K width p r ≈ pair w K width q s :=
  weightedMass_congr w K width (hp.mul hr)

private theorem pair_add_left (w : Q') (K width : Nat) (p q r : RatPoly) :
    pair w K width (polyAdd p q) r ≈ pair w K width p r + pair w K width q r := by
  unfold pair
  rw [polyMul_add_left_exact]
  exact weightedMass_add w K width _ _

private theorem pair_add_right (w : Q') (K width : Nat) (p q r : RatPoly) :
    pair w K width p (polyAdd q r) ≈ pair w K width p q + pair w K width p r :=
  Q'.eqv_trans _ _ _
    (weightedMass_congr w K width (RatPolyCoeffEqv.mul_add_right p q r))
    (weightedMass_add w K width _ _)

private theorem pair_smul_left (w : Q') (K width : Nat) (c : Q') (p q : RatPoly) :
    pair w K width (polySmul c p) q ≈ c * pair w K width p q :=
  Q'.eqv_trans _ _ _
    (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_left c p q))
    (weightedMass_smul w K width c _)

private theorem pair_smul_right (w : Q') (K width : Nat) (c : Q') (p q : RatPoly) :
    pair w K width p (polySmul c q) ≈ c * pair w K width p q :=
  Q'.eqv_trans _ _ _
    (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_right c p q))
    (weightedMass_smul w K width c _)

private theorem pair_four (w : Q') (K width : Nat) (b u p q : RatPoly) :
    pair w K width (polyAdd b (polySmul (-1) u)) (polyAdd p q) ≈
      (pair w K width b p + pair w K width b q) +
        -(pair w K width u p + pair w K width u q) :=
  Q'.eqv_trans _ _ _ (pair_add_left w K width b (polySmul (-1) u) (polyAdd p q))
    (Q'.add_eqv_congr' (pair_add_right w K width b p q)
      (Q'.eqv_trans _ _ _ (pair_smul_left w K width (-1) u (polyAdd p q))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (pair_add_right w K width u p q))
          (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
            (by decide) (fun _ => pair w K width u p + pair w K width u q)))))

private theorem norm_difference (w : Q') (K width : Nat) (b u : RatPoly) :
    pair w K width (polyAdd b (polySmul (-1) u)) (polyAdd b u) ≈
      pair w K width b b + -(pair w K width u u) := by
  have hc : pair w K width u b ≈ pair w K width b u :=
    weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm u b)
  exact Q'.eqv_trans _ _ _ (pair_four w K width b u b u)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hc (Q'.eqv_refl _))))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 1) (.var 2))))
        (.add (.var 0) (.neg (.var 2))) (by decide)
        (fun | 0 => pair w K width b b | 1 => pair w K width b u | _ => pair w K width u u)))

private theorem transfer_difference (w : Q') (K width : Nat) {b u : RatPoly}
    (hb : SupportedQuaternionBlocks (N width) b)
    (hu : SupportedQuaternionBlocks (N width) u) :
    pair w K width (polyAdd b (polySmul (-1) u)) (transferStep w K width (polyAdd b u)) ≈
      pair w K width b (transferStep w K width b) +
        -(pair w K width u (transferStep w K width u)) := by
  have hc : pair w K width u (transferStep w K width b) ≈
      pair w K width b (transferStep w K width u) :=
    transferStep_weighted_symmetric w K width hb hu
  exact Q'.eqv_trans _ _ _
    (pair_congr w K width (RatPolyCoeffEqv.refl _) (transferStep_add w K width b u))
    (Q'.eqv_trans _ _ _ (pair_four w K width b u _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hc (Q'.eqv_refl _))))
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 1) (.var 2))))
          (.add (.var 0) (.neg (.var 2))) (by decide)
          (fun | 0 => pair w K width b (transferStep w K width b)
               | 1 => pair w K width b (transferStep w K width u)
               | _ => pair w K width u (transferStep w K width u)))))

/-- The two original partitions are distinct and never canceled by an
assumed finite eigenvector relation. -/
def clearedRayleighCost (w : Q') (K width : Nat) (A b : RatPoly) : Q' :=
  pair w K width A (transferStep w K width A) * pair w K width b b +
    -(pair w K width A A * pair w K width b (transferStep w K width b))

/-- Original finite-boundary drift, cleared without dividing by A or Z0. -/
def boundaryDrift (w : Q') (K width : Nat) (A f : RatPoly) : Q' :=
  let Z0 := pair w K width A A
  let Z1 := pair w K width A (transferStep w K width A)
  pair w K width (polyMul A (polyMul f f))
    (polyAdd (polySmul Z1 A) (polySmul (-Z0) (transferStep w K width A)))

/-- One signed pairing of the COMPLETE multiplication defect. No absolute
bound on individual telescoping summands is taken. -/
def signedMultiplicationCost (w : Q') (K width : Nat) (A b f : RatPoly) : Q' :=
  let u := polyMul A f
  let Z0 := pair w K width A A
  let Z1 := pair w K width A (transferStep w K width A)
  pair w K width (polyAdd b (polySmul (-1) u))
    (polyAdd (polySmul Z1 (polyAdd b u))
      (polySmul (-Z0) (transferStep w K width (polyAdd b u))))

private theorem boundary_expand (w : Q') (K width : Nat) (A f : RatPoly) :
    boundaryDrift w K width A f ≈
      pair w K width A (transferStep w K width A) * pair w K width (polyMul A f) (polyMul A f) +
        -(pair w K width A A * weightedMass w K width
          (polyMul (polyMul A (transferStep w K width A)) (polyMul f f))) := by
  have hs : pair w K width (polyMul A (polyMul f f)) A ≈
      pair w K width (polyMul A f) (polyMul A f) :=
    weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 0))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => A | _ => f))
  have hm : pair w K width (polyMul A (polyMul f f)) (transferStep w K width A) ≈
      weightedMass w K width (polyMul (polyMul A (transferStep w K width A)) (polyMul f f)) :=
    weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => A | 1 => f | _ => transferStep w K width A))
  unfold boundaryDrift
  exact Q'.eqv_trans _ _ _ (pair_add_right w K width _ _ _)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (pair_smul_right w K width _ _ _)
        (Q'.mul_eqv_congr_left _ _ _ hs))
      (Q'.eqv_trans _ _ _ (pair_smul_right w K width _ _ _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm) (Q'.neg_mul_eqv _ _))))

private theorem multiplication_expand (w : Q') (K width : Nat) {A b f : RatPoly}
    (hb : SupportedQuaternionBlocks (N width) b)
    (hu : SupportedQuaternionBlocks (N width) (polyMul A f)) :
    signedMultiplicationCost w K width A b f ≈
      clearedRayleighCost w K width A b + -(clearedRayleighCost w K width A (polyMul A f)) := by
  let u := polyMul A f
  let Z0 := pair w K width A A
  let Z1 := pair w K width A (transferStep w K width A)
  have he := Q'.eqv_trans _ _ _ (pair_add_right w K width _ _ _)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (pair_smul_right w K width Z1 _ _)
        (Q'.mul_eqv_congr_left _ _ _ (norm_difference w K width b u)))
      (Q'.eqv_trans _ _ _ (pair_smul_right w K width (-Z0) _ _)
        (Q'.mul_eqv_congr_left _ _ _ (transfer_difference w K width hb hu))))
  exact Q'.eqv_trans _ _ _ he
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.var 2) (.neg (.var 3))))
        (.mul (.neg (.var 1)) (.add (.var 4) (.neg (.var 5)))))
      (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 4))))
        (.neg (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 5))))))
      (by decide) (fun
        | 0 => Z1 | 1 => Z0 | 2 => pair w K width b b | 3 => pair w K width u u
        | 4 => pair w K width b (transferStep w K width b)
        | _ => pair w K width u (transferStep w K width u)))

/-- The COMPLETE signed multiplication cost is the difference of two
cleared costs with the SAME A and BOTH original partition factors. -/
theorem signedMultiplicationCost_difference (w : Q') (K width : Nat) {A b f : RatPoly}
    (hb : SupportedQuaternionBlocks (N width) b)
    (hu : SupportedQuaternionBlocks (N width) (polyMul A f)) :
    signedMultiplicationCost w K width A b f ≈
      clearedRayleighCost w K width A b +
        -(clearedRayleighCost w K width A (polyMul A f)) :=
  multiplication_expand w K width hb hu

/-- Exact signed split with the actual weighted transfer symmetry. Only
carrier support is needed; neither positivity nor stationarity is assumed. -/
theorem clearedRayleighCost_split (w : Q') (K width : Nat) {A b f : RatPoly}
    (hb : SupportedQuaternionBlocks (N width) b)
    (hu : SupportedQuaternionBlocks (N width) (polyMul A f)) :
    clearedRayleighCost w K width A b ≈
      (pair w K width A A * energy w K width A f + boundaryDrift w K width A f) +
        signedMultiplicationCost w K width A b f := by
  have hbase : pair w K width A A * energy w K width A f + boundaryDrift w K width A f ≈
      clearedRayleighCost w K width A (polyMul A f) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (boundary_expand w K width A f))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
          (.add (.mul (.var 3) (.var 4)) (.neg (.mul (.var 0) (.var 1)))))
        (.add (.mul (.var 3) (.var 4)) (.neg (.mul (.var 0) (.var 2))))
        (by decide) (fun
          | 0 => pair w K width A A
          | 1 => weightedMass w K width
              (polyMul (polyMul A (transferStep w K width A)) (polyMul f f))
          | 2 => pair w K width (polyMul A f) (transferStep w K width (polyMul A f))
          | 3 => pair w K width A (transferStep w K width A)
          | _ => pair w K width (polyMul A f) (polyMul A f)))
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hbase (multiplication_expand w K width hb hu))
    (poly_identity_of_normal_eq (.add (.var 0) (.add (.var 1) (.neg (.var 0)))) (.var 1)
      (by decide) (fun
        | 0 => clearedRayleighCost w K width A (polyMul A f)
        | _ => clearedRayleighCost w K width A b)))

/-- The split is instantiated on the literal half-smoothed original source;
f may be the SAME finite centered observable, with no recentering. -/
theorem original_block_rayleigh_split (w : Q') (K width t : Nat) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) :
    let A := originalBlockTransfer w K width t g
    let b := originalBlockTransfer w K width t (polyMul g f)
    clearedRayleighCost w K width A b ≈
      (weightedMass w K width (polyMul A A) * energy w K width A f +
        boundaryDrift w K width A f) + signedMultiplicationCost w K width A b f := by
  have hA := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) t hg
  have hb := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) t (supported_polyMul hg hf)
  exact clearedRayleighCost_split w K width hb (supported_polyMul hA hf)

/-- The defect in the signed split is literally the original block
commutator. Its constant-shift invariance is already proved independently. -/
theorem original_block_defect_pin (w : Q') (K width t : Nat) (g f : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (originalBlockTransfer w K width t (polyMul g f))
        (polySmul (-1) (polyMul (originalBlockTransfer w K width t g) f)))
      (blockMultiplicationDefect w K width t g f) :=
  (RatPolyCoeffEqv.refl _).add
    ((neg_smul _).symm.trans
      (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_comm _ _)))

/-- The finite-boundary term in THIS split has an actual computed bound,
uniform in every cutoff above the unchanged head guard at fixed w/width. -/
theorem boundaryDrift_terminal_abs_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (s : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let A := terminalMessage w K width (s+1)
    Q'.abs (boundaryDrift w K width A f) ≤
      comparisonEta hw0 hw1 width s * weightedMass w K width
        (polyMul A (transferStep w K width A)) * weightedMass w K width
          (polyMul (polyMul A A) (polyMul f f)) :=
  clearedDrift_abs_le hw0 hw1 K width hK s hf

/-- An actual upper bound: the terminal drift is PAID, while the original
energy and combined signed commutator cost remain visible and unestimated. -/
theorem terminal_clearedRayleighCost_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (s : Nat) {b f : RatPoly}
    (hb : SupportedQuaternionBlocks (N width) b)
    (hf : SupportedQuaternionBlocks (N width) f) :
    let A := terminalMessage w K width (s+1)
    clearedRayleighCost w K width A b ≤
      (weightedMass w K width (polyMul A A) * energy w K width A f +
        comparisonEta hw0 hw1 width s * weightedMass w K width
          (polyMul A (transferStep w K width A)) * weightedMass w K width
            (polyMul (polyMul A A) (polyMul f f))) +
        signedMultiplicationCost w K width A b f := by
  have hA := BF4ExactSlabFixedSpatialTerminalBracket.terminalMessage_supported w K width (s+1)
  have hs := clearedRayleighCost_split w K width hb (supported_polyMul hA hf)
  have hd := (clearedDrift_bounds hw0 hw1 K width hK s hf).2
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hs)
    (Q'.add_le_add_right _ _ _ (Q'.add_le_add_left _ _ _ hd))

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit.clearedRayleighCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit.boundaryDrift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit.signedMultiplicationCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit.signedMultiplicationCost_difference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit.clearedRayleighCost_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit.original_block_rayleigh_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit.original_block_defect_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit.boundaryDrift_terminal_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit.terminal_clearedRayleighCost_le
