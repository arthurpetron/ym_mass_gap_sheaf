/-
# Local plaquette nontriviality in the actual odd-chain marginal

The selected six-face variance comparison is joined to the original middle
pairing with unequal depths n+1 and n. The first and second moments retain
the SAME selected action, cutoff and positive original partition. Consequently
the explicit floor starRatio(w) applies to the literal marginal V*u_n*u_(n+1)
of DirichletWindow, independently of width, late cutoff and boundary depth.

This is a finite nontriviality estimate, not an energy coercivity theorem,
stationary-vacuum identification, transfer gap or continuum mass bound. The
different even-chain centralVariance is not used.
-/

import YMGap.Continuum.BF4ExactSlabSelectedStarVariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle
import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOddLocalVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws (middleRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem singleton_sum (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul 1 p) polyZero) p :=
  ((RatPolyCoeffEqv.one_smul p).add (RatPolyCoeffEqv.refl polyZero)).trans
    (RatPolyCoeffEqv.add_zero p)

private theorem singleton_product (C : Z4Plaq → Nat → RatPoly) (p : Z4Plaq) :
    RatPolyCoeffEqv (product C [(p, [(1, 1)])]) (C p 1) :=
  ((singleton_sum (C p 1)).mul (RatPolyCoeffEqv.refl polyOne)).trans
    (RatPolyCoeffEqv.mul_one _)

private theorem double_product (C : Z4Plaq → Nat → RatPoly) (p : Z4Plaq) :
    RatPolyCoeffEqv (product C [(p, [(1, 1)]), (p, [(1, 1)])])
      (polyMul (C p 1) (C p 1)) :=
  (singleton_sum (C p 1)).mul (singleton_product C p)

private theorem finite_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (stage : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    finiteValue w hw0 hw1 extent ids hids p stage ≈
      finiteValue w hw0 hw1 extent ids hids q stage := by
  unfold finiteValue numerator
  exact Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (h.mul_right _))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

-- Reduce only the finite singleton bookkeeping, never the underlying link word.
attribute [local irreducible] plaquette correctedSlabPlaquettePolynomial
  middleRatio terminalMessage weightedMass

private theorem odd_stage_variance_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n stage : Nat) (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    let c := characterPolynomial (plaquette width p).scalar 1
    starRatio w ≤
      middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        (n+1) n (polyMul c c) +
      -(middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
          (n+1) n c *
        middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
          (n+1) n c) := by
  let E := width+((n+1)+n)+1
  let a : FaceFactor := (p, [(1, 1)])
  let c := characterPolynomial (plaquette width p).scalar 1
  let f := timeShiftPlaquette (0+(n+1)) p
  let C := BF4ExactSlabSelectedStarVariance.faceCharacter E f
  have hw : width ≤ E := by dsimp [E]; omega
  have ht : 0+((n+1)+n) ≤ E := by dsimp [E]; omega
  have hsingle : ∀ q, q ∈ [a] → q.1 ∈ spatialFaces width := by
    intro q hq
    have he := List.mem_singleton.mp hq
    subst q
    exact hp
  have hdouble : ∀ q, q ∈ [a, a] → q.1 ∈ spatialFaces width := by
    intro q hq
    rcases List.mem_cons.mp hq with he | he
    · subst q
      exact hp
    · exact hsingle q he
  have hsource : RatPolyCoeffEqv (sourceProbe width [a]) c :=
    singleton_product (fun face spin => characterPolynomial (plaquette width face).scalar spin) p
  have hsourceSquare : RatPolyCoeffEqv (sourceProbe width [a, a]) (polyMul c c) :=
    double_product (fun face spin => characterPolynomial (plaquette width face).scalar spin) p
  have hplaced : RatPolyCoeffEqv
      (sweptProduct E 0 (placeProbes (0+(n+1)) [a])) C := by
    rw [swept_zero]
    exact singleton_product
      (fun face spin => characterPolynomial (correctedSlabPlaquettePolynomial E face).scalar spin) f
  have hplacedSquare : RatPolyCoeffEqv
      (sweptProduct E 0 (placeProbes (0+(n+1)) [a, a])) (polyMul C C) := by
    rw [swept_zero]
    exact double_product
      (fun face spin => characterPolynomial (correctedSlabPlaquettePolynomial E face).scalar spin) f
  have hm : middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      (n+1) n c ≈
      finiteValue w hw0 hw1 E (chainIds E width 0 ((n+1)+n))
        (fun _ hi => chainIds_physical hi) C stage :=
    Q'.eqv_trans _ _ _
      (middleRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) (n+1) n hsource.symm)
      (Q'.eqv_trans _ _ _
        (middleRatio_originalFiniteValue hw0 hw1
          (start := 0) (m := n+1) (n := n) hw ht [a] hsingle stage)
        (finite_congr hw0 hw1 E _ _ stage hplaced))
  have hs : middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      (n+1) n (polyMul c c) ≈
      finiteValue w hw0 hw1 E (chainIds E width 0 ((n+1)+n))
        (fun _ hi => chainIds_physical hi) (polyMul C C) stage :=
    Q'.eqv_trans _ _ _
      (middleRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) (n+1) n hsourceSquare.symm)
      (Q'.eqv_trans _ _ _
        (middleRatio_originalFiniteValue hw0 hw1
          (start := 0) (m := n+1) (n := n) hw ht [a, a] hdouble stage)
        (finite_congr hw0 hw1 E _ _ stage hplacedSquare))
  have hf : f ∈ boundaryCompleteSlabPlaquettes E :=
    spatialFaces_shift_physical (by omega) (by dsimp [E]; omega) hp
  have hl : (f.1, (dirsOf f.2).1) ∈ edgesOf f := List.mem_cons_self
  have h := BF4ExactSlabSelectedStarVariance.finiteValue_variance_floor hw0 hw1 E
    (chainIds E width 0 ((n+1)+n)) (fun _ hi => chainIds_physical hi)
    (chainIds_nodup _ _ _ _) hf _ hl stage
  have he := Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _ (qmul hm hm))
  exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv he)

/-- The explicit local floor for the existing original odd-chain middleRatio.
Every spatial face, width, late cutoff and finite boundary depth is allowed. -/
theorem odd_variance_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    let c := characterPolynomial (plaquette width p).scalar 1
    starRatio w ≤ middleRatio hw0 hw1 K width hK (n+1) n (polyMul c c) +
      -(middleRatio hw0 hw1 K width hK (n+1) n c *
        middleRatio hw0 hw1 K width hK (n+1) n c) := by
  have h := odd_stage_variance_floor hw0 hw1 width n (K-headCutoff w) p hp
  simpa only [Nat.add_sub_of_le hK] using h

/-- The SAME floor for the literal normalized marginal V*u_n*T(u_n).
The reciprocal is the existing oddMass reciprocal, not an even-chain law. -/
theorem odd_marginal_variance_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    let c := characterPolynomial (plaquette width p).scalar 1
    let g := terminalMessage w K width n
    let r := Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)
    starRatio w ≤
      weightedMass w K width
          (polyMul (polyMul g (transferStep w K width g)) (polyMul c c)) * r +
      -((weightedMass w K width (polyMul (polyMul g (transferStep w K width g)) c) * r) *
        (weightedMass w K width (polyMul (polyMul g (transferStep w K width g)) c) * r)) := by
  let c := characterPolynomial (plaquette width p).scalar 1
  have hm := marginal_middleRatio hw0 hw1 K width hK n c
  have hs := marginal_middleRatio hw0 hw1 K width hK n (polyMul c c)
  have he := Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _ (qmul hm hm))
  exact Q'.le_trans' _ _ _ (odd_variance_floor hw0 hw1 K width hK n p hp)
    (Q'.ge_of_eqv he)

end YMGap.Continuum.BF4ExactSlabFixedSpatialOddLocalVariance

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOddLocalVariance.odd_variance_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOddLocalVariance.odd_marginal_variance_floor
