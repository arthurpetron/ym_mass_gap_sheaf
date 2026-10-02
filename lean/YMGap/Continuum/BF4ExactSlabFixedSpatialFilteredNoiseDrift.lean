/-
# The literal original radius-two filtered source is noise minus drift

The two endpoint slices are integrated in the SAME original K/V window.
For g=terminal_n, A=Tg, B=T(gf), C=T(g f²), the filtered numerator is
  ell(AC-B²) - ell((B-Af)²).
Its original symmetric-window partition is ell(g_(n+2)g_n)=ell(A²).
This is an EVEN partition, not the finite odd marginal or its OWN variance.
No finite stationarity, source eigenpin, quartic-kernel identification,
relative estimate, joint-limit or changing-family assertion is made.
-/

import YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
import YMGap.Continuum.SU2QuaternionHeadSeparatedWindows

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadSeparatedWindows
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionHeadWindowBounds (windowMessage_add windowMessage_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (difference)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (squareAt differenceAt)
open YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement (filteredExpression)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage spatialWeight kineticWeight

private theorem step_coeff (w : Q') (K width : Nat) {p r : RatPoly}
    (h : RatPolyCoeffEqv p r) :
    RatPolyCoeffEqv (transferStep w K width p) (transferStep w K width r) :=
  partialHaarHeads_congr (N width)
    ((RatPolyCoeffEqv.refl (kineticWeight w K width)).mul
      ((RatPolyCoeffEqv.refl (spatialWeight w K width)).mul h))

/-- Actual retained one-slice drift; the finite terminal is not an eigenmessage. -/
def driftPolynomial (w : Q') (K width n : Nat) (f : RatPoly) : RatPoly :=
  let g := terminalMessage w K width n
  let A := transferStep w K width g
  let B := transferStep w K width (polyMul g f)
  polyAdd B (polySmul (-1) (polyMul A f))

def driftSquare (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  weightedMass w K width (polyMul (driftPolynomial w K width n f)
    (driftPolynomial w K width n f))

/-- Conditional noise numerator, with every original spatial weight retained. -/
def noise (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  let g := terminalMessage w K width n
  let A := transferStep w K width g
  let B := transferStep w K width (polyMul g f)
  let C := transferStep w K width (polyMul g (polyMul f f))
  weightedMass w K width (polyAdd (polyMul A C) (polySmul (-1) (polyMul B B)))

/-- The ORIGINAL symmetric radius-two denominator, without replacing it by
an odd-edge partition. -/
def evenPartition (w : Q') (K width n : Nat) : Q' :=
  weightedMass w K width
    (polyMul (terminalMessage w K width (n+2)) (terminalMessage w K width n))

theorem evenPartition_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (0 : Q') < evenPartition w K width n :=
  terminalPair_positive hw0 hw1 K width hK (n+2) n

theorem evenPartition_middle_pin (w : Q') (K width n : Nat) :
    evenPartition w K width n ≈ weightedMass w K width
      (polyMul (transferStep w K width (terminalMessage w K width n))
        (transferStep w K width (terminalMessage w K width n))) := by
  unfold evenPartition
  rw [terminalMessage_next w K width n]
  have h := transferStep_weighted_symmetric w K width
    (terminalMessage_supported w K width (n+1)) (terminalMessage_supported w K width n)
  rw [terminalMessage_next w K width n, terminalMessage_next w K width (n+1)] at h
  exact Q'.eqv_trans _ _ _ (weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _)) h

/-- The literal observedMessage numerator of the original (n,2,n) window. -/
def numerator (w : Q') (K width n : Nat) (p : RatPoly) : Q' :=
  weightedMass w K width
    (polyMul (observedMessage w K width n 2 p) (terminalMessage w K width n))

private theorem numerator_coeff (w : Q') (K width n : Nat) {p r : RatPoly}
    (h : RatPolyCoeffEqv p r) : numerator w K width n p ≈ numerator w K width n r :=
  weightedMass_congr w K width
    ((partialHaarHeads_congr (2*(N width))
      (((RatPolyCoeffEqv.refl _).mul h).mul (RatPolyCoeffEqv.refl _))).mul_right _)

private theorem numerator_add (w : Q') (K width n : Nat) (p r : RatPoly) :
    numerator w K width n (polyAdd p r) ≈ numerator w K width n p+numerator w K width n r :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width
    ((windowMessage_add (N width) (kineticWeight w K width) (spatialWeight w K width)
      2 (terminalMessage w K width n) p r).mul_right _))
    (by rw [polyMul_add_left_exact]; exact weightedMass_add w K width _ _)

private theorem numerator_smul (w : Q') (K width n : Nat) (c : Q') (p : RatPoly) :
    numerator w K width n (polySmul c p) ≈ c*numerator w K width n p :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width
    ((windowMessage_smul (N width) (kineticWeight w K width) (spatialWeight w K width)
      2 (terminalMessage w K width n) c p).mul_right _))
    (Q'.eqv_trans _ _ _ (weightedMass_congr w K width
      (RatPolyCoeffEqv.polyMul_smul_left c _ _)) (weightedMass_smul w K width c _))

private theorem observed_middle (w : Q') (K width n : Nat) (p r : RatPoly) :
    RatPolyCoeffEqv
      (observedMessage w K width n 2 (polyMul p (liftBoundary (N width) r)))
      (transferStep w K width (polyMul
        (transferStep w K width (polyMul (terminalMessage w K width n) p)) r)) := by
  have hm := iterateStep_middle (N width) (kineticWeight w K width)
    (spatialWeight w K width) 1 1 (polyMul (terminalMessage w K width n) p) r
  have hm' : RatPolyCoeffEqv
      (transferStep w K width (transferStep w K width
        (polyMul (polyMul (terminalMessage w K width n) p) (liftBoundary (N width) r))))
      (transferStep w K width (polyMul
        (transferStep w K width (polyMul (terminalMessage w K width n) p)) r)) := by
    simpa only [Nat.one_mul, iterateStep] using hm
  exact (windowMessage_iterate (N width) (kineticWeight w K width) (spatialWeight w K width)
    2 (terminalMessage w K width n) _).trans
    ((step_coeff w K width (step_coeff w K width
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm)).trans hm')

private theorem observed_last (w : Q') (K width n : Nat) (p r : RatPoly) :
    RatPolyCoeffEqv
      (observedMessage w K width n 2 (polyMul p (liftBoundary (2*(N width)) r)))
      (polyMul (transferStep w K width (transferStep w K width
        (polyMul (terminalMessage w K width n) p))) r) := by
  have h := windowMessage_iterate (N width) (kineticWeight w K width)
    (spatialWeight w K width) 2 (terminalMessage w K width n)
      (polyMul p (liftBoundary (2*(N width)) r))
  have hc := RatPolyCoeffEqv.mul_assoc (terminalMessage w K width n) p
    (liftBoundary (2*(N width)) r)
  have hi : RatPolyCoeffEqv
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) 2
        (polyMul (terminalMessage w K width n) (polyMul p (liftBoundary (2*(N width)) r))))
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) 2
        (polyMul (polyMul (terminalMessage w K width n) p) (liftBoundary (2*(N width)) r))) :=
    step_coeff w K width (step_coeff w K width hc.symm)
  exact h.trans (hi.trans (iterateStep_mul_lift (N width) (kineticWeight w K width)
    (spatialWeight w K width) 2 (polyMul (terminalMessage w K width n) p) r))

private theorem middle_fold (w : Q') (K width n : Nat) (p r : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) p)
    (hr : SupportedQuaternionBlocks (N width) r) :
    numerator w K width n (polyMul p (liftBoundary (N width) r)) ≈
      weightedMass w K width (polyMul
        (polyMul (transferStep w K width (terminalMessage w K width n))
          (transferStep w K width (polyMul (terminalMessage w K width n) p))) r) :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width ((observed_middle w K width n p r).mul_right _))
    (Q'.eqv_trans _ _ _ (weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (transferStep_weighted_symmetric w K width
        (supported_polyMul (transferStep_supported w K width
          (supported_polyMul (terminalMessage_supported w K width n) hp)) hr)
        (terminalMessage_supported w K width n))
        (weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.mul (.var 2) (.var 0)) (.var 1)) (by decide)
          (fun
            | 0 => transferStep w K width (polyMul (terminalMessage w K width n) p)
            | 1 => r
            | _ => transferStep w K width (terminalMessage w K width n))))))

private theorem last_fold (w : Q') (K width n : Nat) (p r : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) p)
    (hr : SupportedQuaternionBlocks (N width) r) :
    numerator w K width n (polyMul p (liftBoundary (2*(N width)) r)) ≈
      weightedMass w K width (polyMul
        (transferStep w K width (polyMul (terminalMessage w K width n) p))
        (transferStep w K width (polyMul (terminalMessage w K width n) r))) := by
  refine Q'.eqv_trans _ _ _ (weightedMass_congr w K width ((observed_last w K width n p r).mul_right _)) ?_
  refine Q'.eqv_trans _ _ _ (weightedMass_congr w K width
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.mul (.var 2) (.var 1)) (.var 0))
      (by decide) (fun
        | 0 => transferStep w K width (transferStep w K width
            (polyMul (terminalMessage w K width n) p))
        | 1 => r
        | _ => terminalMessage w K width n))) ?_
  exact transferStep_weighted_symmetric w K width
    (transferStep_supported w K width (supported_polyMul (terminalMessage_supported w K width n) hp))
    (supported_polyMul (terminalMessage_supported w K width n) hr)

/-- The actual sourcePolynomial of the existing signed radius-two syntax,
not a separately supplied observable row. -/
theorem filtered_loop_numerator (w : Q') (K width n : Nat)
    (value : SourceLoop width) (spin : Nat) :
    numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 value spin))) ≈
      noise w K width n (sourceCharacter width value.edges spin)-
        driftSquare w K width n (sourceCharacter width value.edges spin) := by
  let f := sourceCharacter width value.edges spin
  let g := terminalMessage w K width n
  let A := transferStep w K width g
  let B := transferStep w K width (polyMul g f)
  let C := transferStep w K width (polyMul g (polyMul f f))
  have hf := sourceCharacter_supported width value.edges spin
  have hff := supported_polyMul hf hf
  let row := polyAdd
    (polyAdd (polyMul polyOne (liftBoundary (2*(N width)) (polyMul f f)))
      (polySmul (-1) (polyMul polyOne (liftBoundary (N width) (polyMul f f)))))
    (polyAdd (polySmul (-2) (polyMul f (liftBoundary (2*(N width)) f)))
      (polySmul 2 (polyMul f (liftBoundary (N width) f))))
  have hrow : RatPolyCoeffEqv (sourcePolynomial (filteredExpression (.loop 0 value spin))) row := by
    have hlift0 (p : RatPoly) : liftBoundary 0 p = p := rfl
    simp only [filteredExpression, squareAt, differenceAt, difference, shift,
      mapOffsets, sourcePolynomial, Nat.zero_add, Nat.zero_mul,
      Nat.one_mul, hlift0]
    change RatPolyCoeffEqv
      (polyAdd (polyMul (polyAdd f (polySmul (-1) (liftBoundary (2*(N width)) f)))
        (polyAdd f (polySmul (-1) (liftBoundary (2*(N width)) f))))
        (polySmul (-1) (polyMul (polyAdd f (polySmul (-1) (liftBoundary (N width) f)))
          (polyAdd f (polySmul (-1) (liftBoundary (N width) f)))))) row
    dsimp only [row]
    rw [lift_product, lift_product]
    have hs1 : RatPolyCoeffEqv
        (polyAdd f (polySmul (-1) (liftBoundary (N width) f)))
        (polyAdd f (polyMul (cap (-1)) (liftBoundary (N width) f))) :=
      (RatPolyCoeffEqv.refl f).add (cap_mul_left (-1) (liftBoundary (N width) f)).symm
    have hs2 : RatPolyCoeffEqv
        (polyAdd f (polySmul (-1) (liftBoundary (2*(N width)) f)))
        (polyAdd f (polyMul (cap (-1)) (liftBoundary (2*(N width)) f))) :=
      (RatPolyCoeffEqv.refl f).add (cap_mul_left (-1) (liftBoundary (2*(N width)) f)).symm
    refine ((hs2.mul hs2).add (((hs1.mul hs1).smul (-1)).trans
      (cap_mul_left (-1) _).symm)).trans ?_
    refine (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.var 0) (.mul (.const (-1)) (.var 2)))
        (.add (.var 0) (.mul (.const (-1)) (.var 2))))
        (.mul (.const (-1)) (.mul (.add (.var 0) (.mul (.const (-1)) (.var 1)))
          (.add (.var 0) (.mul (.const (-1)) (.var 1))))))
      (.add (.add (.mul (.var 2) (.var 2))
        (.mul (.const (-1)) (.mul (.var 1) (.var 1))))
        (.add (.mul (.const (-2)) (.mul (.var 0) (.var 2)))
          (.mul (.const 2) (.mul (.var 0) (.var 1))))) (by decide)
      (fun
        | 0 => f
        | 1 => liftBoundary (N width) f
        | _ => liftBoundary (2*(N width)) f)).trans ?_
    exact ((RatPolyCoeffEqv.one_mul _).symm.add
      ((cap_mul_left (-1) _).trans ((RatPolyCoeffEqv.one_mul _).symm.smul (-1)))).add
      ((cap_mul_left (-2) _).add (cap_mul_left 2 _))
  have hu := step_coeff w K width (RatPolyCoeffEqv.mul_one g)
  have hlast := last_fold w K width n polyOne (polyMul f f) (supported_one _) hff
  have hmid := middle_fold w K width n polyOne (polyMul f f) (supported_one _) hff
  have hcross2 := last_fold w K width n f f hf hf
  have hcross1 := middle_fold w K width n f f hf hf
  have hlast' : numerator w K width n (polyMul polyOne (liftBoundary (2*(N width)) (polyMul f f))) ≈
      weightedMass w K width (polyMul A C) :=
    Q'.eqv_trans _ _ _ hlast (weightedMass_congr w K width (hu.mul_right C))
  have hmid' : numerator w K width n (polyMul polyOne (liftBoundary (N width) (polyMul f f))) ≈
      weightedMass w K width (polyMul (polyMul A A) (polyMul f f)) :=
    Q'.eqv_trans _ _ _ hmid (weightedMass_congr w K width ((hu.mul_left A).mul_right _))
  have hvalues : numerator w K width n row ≈
      (weightedMass w K width (polyMul A C)+(-1)*weightedMass w K width (polyMul (polyMul A A) (polyMul f f)))+
      ((-2)*weightedMass w K width (polyMul B B)+2*weightedMass w K width (polyMul (polyMul A B) f)) :=
    Q'.eqv_trans _ _ _ (numerator_add w K width n _ _) (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (numerator_add w K width n _ _) (Q'.add_eqv_congr' hlast'
        (Q'.eqv_trans _ _ _ (numerator_smul w K width n (-1) _)
          (Q'.mul_eqv_congr_left _ _ _ hmid'))))
      (Q'.eqv_trans _ _ _ (numerator_add w K width n _ _) (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (numerator_smul w K width n (-2) _)
          (Q'.mul_eqv_congr_left _ _ _ hcross2))
        (Q'.eqv_trans _ _ _ (numerator_smul w K width n 2 _)
          (Q'.mul_eqv_congr_left _ _ _ hcross1)))))
  have hd : driftSquare w K width n f ≈ weightedMass w K width
      (polyAdd (polyMul B B) (polyAdd (polySmul (-2) (polyMul (polyMul A B) f))
        (polyMul (polyMul A A) (polyMul f f)))) := by
    have hdelta : RatPolyCoeffEqv (driftPolynomial w K width n f)
        (polyAdd B (polyMul (cap (-1)) (polyMul A f))) :=
      (RatPolyCoeffEqv.refl B).add (cap_mul_left (-1) (polyMul A f)).symm
    apply weightedMass_congr w K width
    refine (hdelta.mul hdelta).trans ?_
    refine (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 1) (.mul (.const (-1)) (.mul (.var 0) (.var 2))))
        (.add (.var 1) (.mul (.const (-1)) (.mul (.var 0) (.var 2)))))
      (.add (.mul (.var 1) (.var 1)) (.add (.mul (.const (-2)) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))))) (by decide)
      (fun | 0 => A | 1 => B | _ => f)).trans ?_
    exact (RatPolyCoeffEqv.refl (polyMul B B)).add
      ((cap_mul_left (-2) (polyMul (polyMul A B) f)).add (RatPolyCoeffEqv.refl _))
  have hn := weightedMass_add w K width (polyMul A C) (polySmul (-1) (polyMul B B))
  have hd' := Q'.eqv_trans _ _ _ hd (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' (weightedMass_smul w K width (-2) _) (Q'.eqv_refl _)))))
  have hn' : noise w K width n f ≈ weightedMass w K width (polyMul A C)+
      (-1)*weightedMass w K width (polyMul B B) :=
    Q'.eqv_trans _ _ _ hn (Q'.add_eqv_congr_left _ _ _ (weightedMass_smul w K width (-1) _))
  exact Q'.eqv_trans _ _ _ (numerator_coeff w K width n hrow)
    (Q'.eqv_trans _ _ _ hvalues (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.const (-1)) (.var 1)))
        (.add (.mul (.const (-2)) (.var 2)) (.mul (.const 2) (.var 3))))
      (.add (.add (.var 0) (.mul (.const (-1)) (.var 2)))
        (.neg (.add (.var 2) (.add (.mul (.const (-2)) (.var 3)) (.var 1)))))
      (by decide) (fun
        | 0 => weightedMass w K width (polyMul A C)
        | 1 => weightedMass w K width (polyMul (polyMul A A) (polyMul f f))
        | 2 => weightedMass w K width (polyMul B B)
        | _ => weightedMass w K width (polyMul (polyMul A B) f)))
      (Q'.add_eqv_congr' (Q'.eqv_symm hn') (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hd')))))

/-- The retained drift square is genuinely nonnegative under the original
spatial certificate. This says nothing about the sign of noise-minus-drift. -/
theorem driftSquare_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    (0 : Q') ≤ driftSquare w K width n f := by
  have ha := transferStep_supported w K width (terminalMessage_supported w K width n)
  have hb := transferStep_supported w K width
    (supported_polyMul (terminalMessage_supported w K width n) hf)
  have hs : SupportedQuaternionBlocks (N width)
      (polySmul (-1) (polyMul (transferStep w K width (terminalMessage w K width n)) f)) := by
    intro t ht
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ht
    exact supported_polyMul ha hf r hr
  exact weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square _ (supported_add hb hs))

/-- Constant shifts cancel in the actual drift polynomial before integration.
In particular no OWN center is substituted by a raw-source center. -/
theorem driftPolynomial_shifted (w : Q') (K width n : Nat) (f : RatPoly) (c : Q') :
    RatPolyCoeffEqv (driftPolynomial w K width n (shifted f c))
      (driftPolynomial w K width n f) := by
  let g := terminalMessage w K width n
  let A := transferStep w K width g
  let B := transferStep w K width (polyMul g f)
  have multiply_shift (p : RatPoly) : RatPolyCoeffEqv (polyMul p (shifted f c))
      (polyAdd (polyMul p f) (polySmul (-c) p)) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right 1 p f).trans (RatPolyCoeffEqv.one_smul _)).add
        ((RatPolyCoeffEqv.polyMul_smul_right (-c) p polyOne).trans
          ((RatPolyCoeffEqv.mul_one p).smul (-c))))
  have hm : RatPolyCoeffEqv (transferStep w K width (polyMul g (shifted f c)))
      (polyAdd B (polySmul (-c) A)) :=
    (step_coeff w K width (multiply_shift g)).trans
      ((transferStep_add w K width _ _).trans
        ((RatPolyCoeffEqv.refl B).add (transferStep_smul w K width (-c) g)))
  refine (hm.add ((multiply_shift A).smul (-1))).trans ?_
  refine (((RatPolyCoeffEqv.refl B).add (RatPolyCoeffEqv.refl (polySmul (-c) A))).add
    (cap_mul_left (-1) (polyAdd (polyMul A f) (polySmul (-c) A))).symm).trans ?_
  refine (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 2)) (.mul (.const (-1)) (.add (.var 1) (.var 2))))
      (.add (.var 0) (.mul (.const (-1)) (.var 1))) (by decide)
      (fun | 0 => B | 1 => polyMul A f | _ => polySmul (-c) A)).trans ?_
  exact (RatPolyCoeffEqv.refl B).add (cap_mul_left (-1) (polyMul A f))

/-- Exact normalized ORIGINAL source in its SAME symmetric radius-two window.
Only the existing positive original EVEN partition is inverted. -/
theorem filtered_loop_windowRatio {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (value : SourceLoop width) (spin : Nat) :
    windowRatio hw0 hw1 K width hK n 2 n
      (sourcePolynomial (filteredExpression (.loop 0 value spin))) ≈
      (noise w K width n (sourceCharacter width value.edges spin)-
        driftSquare w K width n (sourceCharacter width value.edges spin))*
      Q'.recipPos (evenPartition w K width n) (evenPartition_positive hw0 hw1 K width hK n) :=
  Q'.mul_eqv_congr_right _ _ _ (filtered_loop_numerator w K width n value spin)

/-- Direct pin to the SAME original ambient finiteValue, at its original
head-plus-stage cutoff and symmetric external depths. No limit is taken. -/
theorem filtered_loop_originalWindowScalar {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width stage n : Nat) (value : SourceLoop width) (spin : Nat) :
    BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.originalWindowScalar hw0 hw1 2
      (filteredExpression (.loop 0 value spin)) stage n n ≈
      (noise w (headCutoff w+stage) width n (sourceCharacter width value.edges spin)-
        driftSquare w (headCutoff w+stage) width n (sourceCharacter width value.edges spin))*
      Q'.recipPos (evenPartition w (headCutoff w+stage) width n)
        (evenPartition_positive hw0 hw1 (headCutoff w+stage) width
          (Nat.le_add_right _ _) n) :=
  Q'.eqv_trans _ _ _
    (BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.originalWindowScalar_pin hw0 hw1 2
      (filteredExpression (.loop 0 value spin))
      (BF4WilsonAllNomeFilteredIncrement.filteredExpression_within (Nat.le_refl 0)) stage n n)
    (filtered_loop_windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) n value spin)

#print axioms driftPolynomial
#print axioms driftSquare
#print axioms noise
#print axioms evenPartition
#print axioms evenPartition_positive
#print axioms evenPartition_middle_pin
#print axioms numerator
#print axioms filtered_loop_numerator
#print axioms filtered_loop_windowRatio
#print axioms filtered_loop_originalWindowScalar
#print axioms driftSquare_nonnegative
#print axioms driftPolynomial_shifted

end YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
