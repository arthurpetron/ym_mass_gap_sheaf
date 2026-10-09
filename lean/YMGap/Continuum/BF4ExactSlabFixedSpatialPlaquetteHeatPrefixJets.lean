/-
# Original fixed-spatial plaquette heat-prefix jets

This adapter keeps the literal selected face scalar and a physical face-edge
block through the finite heat/Jacobi split. The cap and deficit windows hold
under arbitrary insertions on every containing product-Haar carrier. They are
not a curvature sign, conditional-action bound, or scaling estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteJetInterval
import YMGap.Continuum.SU2QuaternionPairedHeatPrefixMixedDeficit
import YMGap.Continuum.QPolyHaarPairedAtFrozenChain

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (face_link_mem_base)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported plaquette_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteJetInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarAngularCarrier (angularDerivative_neg intervalNeg)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (SquareBound)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
  (deficitPolynomial prefixInterval deficitInterval prefix_eq_weighted_add_deficit)
open YMGap.Continuum.QuaternionHaarHeatAngularDerivative
  (heatDerivativeCap heatPrefixAngularIntervalAt)
open YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative
  (heatSecondDerivativeCap heatPrefixSecondAngularIntervalAt)
open YMGap.Continuum.SU2QuaternionPairedFrameAt
  (pairedDerivativeAt pairedDerivativeAt_supported)
open YMGap.Continuum.QPolyHaarPairedAtFrozenChain (pairedAt_congr)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (subst)

local notation:max "N" width:arg => List.length (baseLinks width)

private def firstPlane (i : Fin 3) : Fin 4 × Fin 4 :=
  match i.val with
  | 0 => (0,1)
  | 1 => (0,2)
  | _ => (0,3)

private def secondPlane (i : Fin 3) : Fin 4 × Fin 4 :=
  match i.val with
  | 0 => (2,3)
  | 1 => (1,3)
  | _ => (1,2)

private def planeDerivative (block : Nat) (a : Fin 4 × Fin 4) (p : RatPoly) : RatPoly :=
  angularDerivative (4*block+a.1.val) (4*block+a.2.val) p

private def signedTerm (i : Fin 3) (p : RatPoly) : RatPoly :=
  if i.val=1 then polyNeg p else p

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

private theorem paired_representation (block : Nat) (i : Fin 3) (p : RatPoly) :
    RatPolyCoeffEqv (pairedDerivativeAt block i p)
      (polyAdd (planeDerivative block (firstPlane i) p)
        (signedTerm i (planeDerivative block (secondPlane i) p))) := by
  rcases direction_cases i with rfl | rfl | rfl
  all_goals exact RatPolyCoeffEqv.refl _

private theorem signed_congr (i : Fin 3) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : RatPolyCoeffEqv (signedTerm i p) (signedTerm i q) := by
  unfold signedTerm
  split
  · exact RatPolyCoeffEqv.neg h
  · exact h

private theorem angular_signed (block : Nat) (a : Fin 4 × Fin 4)
    (i : Fin 3) (p : RatPoly) :
    RatPolyCoeffEqv (planeDerivative block a (signedTerm i p))
      (signedTerm i (planeDerivative block a p)) := by
  unfold signedTerm
  split
  · exact angularDerivative_neg _ _ p
  · exact RatPolyCoeffEqv.refl _

private theorem angular_paired (block : Nat) (a : Fin 4 × Fin 4)
    (j : Fin 3) (p : RatPoly) :
    RatPolyCoeffEqv (planeDerivative block a (pairedDerivativeAt block j p))
      (polyAdd (planeDerivative block a (planeDerivative block (firstPlane j) p))
        (signedTerm j (planeDerivative block a
          (planeDerivative block (secondPlane j) p)))) :=
  (angularDerivative_congr _ _ (paired_representation block j p)).trans
    ((angularDerivative_add _ _ _ _).trans
      ((RatPolyCoeffEqv.refl _).add (angular_signed block a j _)))

private def mixedExpansion (block : Nat) (i j : Fin 3) (p : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd (planeDerivative block (firstPlane i)
        (planeDerivative block (firstPlane j) p))
      (signedTerm j (planeDerivative block (firstPlane i)
        (planeDerivative block (secondPlane j) p))))
    (signedTerm i
      (polyAdd (planeDerivative block (secondPlane i)
          (planeDerivative block (firstPlane j) p))
        (signedTerm j (planeDerivative block (secondPlane i)
          (planeDerivative block (secondPlane j) p)))))

/-- All four ordered plane terms of the selected-block paired Hessian. -/
theorem paired_mixed_expansion (block : Nat) (i j : Fin 3) (p : RatPoly) :
    RatPolyCoeffEqv (pairedDerivativeAt block i (pairedDerivativeAt block j p))
      (mixedExpansion block i j p) :=
  (paired_representation block i (pairedDerivativeAt block j p)).trans
    ((angular_paired block (firstPlane i) j p).add
      (signed_congr i (angular_paired block (secondPlane i) j p)))

private def signedInterval {blocks : Nat} {p : RatPoly} {a : Q'}
    (i : Fin 3) (P : Interval blocks p a) : Interval blocks (signedTerm i p) a := by
  unfold signedTerm
  split
  · exact intervalNeg P
  · exact P

private theorem double_pin (a : Q') : Q'.eqv (a+a) (2*a) :=
  poly_identity_of_normal_eq (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
    (by decide) (fun _ => a)

private theorem four_pin (a : Q') : Q'.eqv ((a+a)+(a+a)) (4*a) :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
    (.mul (.const 4) (.var 0)) (by decide) (fun _ => a)

private def firstInterval {blocks block : Nat} {p : RatPoly} {a : Q'}
    (F : ∀ i j : Fin 4,
      Interval blocks (planeDerivative block (i,j) p) a)
    (i : Fin 3) : Interval blocks (pairedDerivativeAt block i p) (2*a) := by
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    exact ((F 0 1).add (F 2 3)).changeCap (double_pin a)
  · by_cases h1 : i.val=1
    · have hi : i=1 := Fin.ext h1
      subst i
      exact ((F 0 2).add (intervalNeg (F 1 3))).changeCap (double_pin a)
    · have hi : i=2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      exact ((F 0 3).add (F 1 2)).changeCap (double_pin a)

/-- The signed four-term assembly retains both middle-direction minus signs. -/
def mixedInterval {blocks block : Nat} {p : RatPoly} {a : Q'}
    (hb : block < blocks) (hp : SupportedQuaternionBlocks blocks p)
    (F : ∀ i j k l : Fin 4,
      Interval blocks (planeDerivative block (i,j)
        (planeDerivative block (k,l) p)) a)
    (i j : Fin 3) :
    Interval blocks (pairedDerivativeAt block i (pairedDerivativeAt block j p))
      (4*a) := by
  have hs := pairedDerivativeAt_supported hb i (pairedDerivativeAt_supported hb j hp)
  refine Interval.ofCoeff hs (paired_mixed_expansion block i j p) ?_
  exact (((F (firstPlane i).1 (firstPlane i).2
      (firstPlane j).1 (firstPlane j).2).add
    (signedInterval j (F (firstPlane i).1 (firstPlane i).2
      (secondPlane j).1 (secondPlane j).2))).add
    (signedInterval i
      ((F (secondPlane i).1 (secondPlane i).2
        (firstPlane j).1 (firstPlane j).2).add
        (signedInterval j (F (secondPlane i).1 (secondPlane i).2
          (secondPlane j).1 (secondPlane j).2))))).changeCap (four_pin a)

/-- Selected-block additivity for the exact original prefix split. -/
theorem pairedAt_add (block : Nat) (i : Fin 3) (p q : RatPoly) :
    RatPolyCoeffEqv (pairedDerivativeAt block i (polyAdd p q))
      (polyAdd (pairedDerivativeAt block i p) (pairedDerivativeAt block i q)) := by
  have hp (a b c d : RatPoly) : RatPolyCoeffEqv
      (polyAdd (polyAdd a b) (polyAdd c d))
      (polyAdd (polyAdd a c) (polyAdd b d)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
      (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)
  have hm (a b c d : RatPoly) : RatPolyCoeffEqv
      (polyAdd (polyAdd a b) (polyNeg (polyAdd c d)))
      (polyAdd (polyAdd a (polyNeg c)) (polyAdd b (polyNeg d))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
      (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)
  rcases direction_cases i with rfl | rfl | rfl
  · exact ((angularDerivative_add _ _ p q).add (angularDerivative_add _ _ p q)).trans
      (hp _ _ _ _)
  · exact ((angularDerivative_add _ _ p q).add
      (RatPolyCoeffEqv.neg (angularDerivative_add _ _ p q))).trans (hm _ _ _ _)
  · exact ((angularDerivative_add _ _ p q).add (angularDerivative_add _ _ p q)).trans
      (hp _ _ _ _)

/-- Same literal scalar in the prefix, Jacobi approximant, and deficit. -/
def facePrefix (w : Q') (K width : Nat) (face : Z4Plaq) : RatPoly :=
  heatPrefix w K (plaquette width face).scalar

def faceJacobi (w : Q') (J width : Nat) (face : Z4Plaq) : RatPoly :=
  subst (polyAdd polyOne (plaquette width face).scalar)
    (JacobiShiftedPositiveCoefficients.heat w J)

def faceDeficit (w : Q') (K width : Nat) (face : Z4Plaq) : RatPoly :=
  deficitPolynomial w (K+1) (plaquette width face).scalar

def pairedDeficitCutoff (w epsilon : Q') : Nat :=
  max (BF4ExactSlabJacobiDeficitInterval.deficitCutoff w epsilon)
    (max (QuaternionHaarHeatAngularDeficit.deficitCutoff w 512 epsilon)
      (QuaternionHaarHeatMixedAngularDeficit.deficitCutoff w 512 512 4096 epsilon))

def prefixValueCap (w : Q') : Q' := BF4ExactSlabAllNomeTailInterval.prefixCap w
def prefixFirstCap (w : Q') : Q' := 2*heatDerivativeCap w 512
def prefixSecondCap (w : Q') : Q' := 4*heatSecondDerivativeCap w 512 512 4096

private def faceSquare {width blocks : Nat} {face : Z4Plaq}
    (hroom : N width ≤ blocks) :
    SquareBound blocks (plaquette width face).scalar 1 :=
  SquareBound.scalar (plaquette_supported width blocks hroom face)
    (plaquette_unit width blocks hroom face)

/-- Coefficientwise decomposition at the exact `K+1` Jacobi degree. -/
theorem prefix_split_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv (facePrefix w K width face)
      (polyAdd (faceJacobi w (K+1) width face) (faceDeficit w K width face)) :=
  (prefix_eq_weighted_add_deficit w K (plaquette width face).scalar).trans
    ((JacobiWeightedHeatPolynomial.shiftedHeat_subst_coeffEqv_weightedPolynomial
      hw0 hw1 (K+1) (plaquette width face).scalar).symm.add (.refl _))

/-- First selected-block derivative of the SAME split. -/
theorem prefix_first_split_pin {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (face : Z4Plaq)
    (block : Nat) (i : Fin 3) :
    RatPolyCoeffEqv (pairedDerivativeAt block i (facePrefix w K width face))
      (polyAdd (pairedDerivativeAt block i (faceJacobi w (K+1) width face))
        (pairedDerivativeAt block i (faceDeficit w K width face))) :=
  (pairedAt_congr block i (prefix_split_pin hw0 hw1 K width face)).trans
    (pairedAt_add block i _ _)

/-- Every ordered selected-block Hessian entry of the SAME split. -/
theorem prefix_mixed_split_pin {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (face : Z4Plaq)
    (block : Nat) (i j : Fin 3) :
    RatPolyCoeffEqv
      (pairedDerivativeAt block i (pairedDerivativeAt block j (facePrefix w K width face)))
      (polyAdd
        (pairedDerivativeAt block i
          (pairedDerivativeAt block j (faceJacobi w (K+1) width face)))
        (pairedDerivativeAt block i
          (pairedDerivativeAt block j (faceDeficit w K width face)))) :=
  (pairedAt_congr block i (prefix_first_split_pin hw0 hw1 K width face block j)).trans
    (pairedAt_add block i _ _)

/-- Original face-prefix value, with the same full Haar carrier. -/
def prefix_value_interval {width blocks : Nat} {face : Z4Plaq}
    (hroom : N width ≤ blocks) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) :
    Interval blocks (facePrefix w K width face) (prefixValueCap w) :=
  prefixInterval hw0 hw1 (faceSquare hroom) K

/-- First selected-edge paired jet at every finite cutoff. -/
def prefix_first_interval {width blocks : Nat} {face : Z4Plaq} {l : Z4Link}
    (hf : face ∈ spatialFaces width) (hl : l ∈ edgesOf face)
    (hroom : N width ≤ blocks) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (i : Fin 3) :
    Interval blocks
      (pairedDerivativeAt ((baseLinks width).idxOf l) i (facePrefix w K width face))
      (prefixFirstCap w) := by
  have hs : (baseLinks width).idxOf l < blocks :=
    Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem (face_link_mem_base hf hl)) hroom
  apply firstInterval (block := (baseLinks width).idxOf l) _ i
  intro a b
  exact heatPrefixAngularIntervalAt (by omega) (by omega) hw0 hw1 (faceSquare hroom)
    (originalFirstInterval (ii := 0) (ij := 1)
      hf hroom hs hs a.isLt b.isLt (by decide) (by decide)) K

/-- Every ordered selected-edge paired prefix Hessian entry, all nine cells. -/
def prefix_mixed_interval {width blocks : Nat} {face : Z4Plaq} {l : Z4Link}
    (hf : face ∈ spatialFaces width) (hl : l ∈ edgesOf face)
    (hroom : N width ≤ blocks) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (i j : Fin 3) :
    Interval blocks
      (pairedDerivativeAt ((baseLinks width).idxOf l) i
        (pairedDerivativeAt ((baseLinks width).idxOf l) j (facePrefix w K width face)))
      (prefixSecondCap w) := by
  have hs : (baseLinks width).idxOf l < blocks :=
    Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem (face_link_mem_base hf hl)) hroom
  let P := prefix_value_interval (face := face) hroom hw0 hw1 K
  apply mixedInterval hs P.support _ i j
  intro a b c d
  exact heatPrefixSecondAngularIntervalAt
    (by omega) (by omega) (by omega) (by omega) hw0 hw1 (faceSquare hroom)
    (originalFirstInterval (ii := 0) (ij := 1)
      hf hroom hs hs a.isLt b.isLt (by decide) (by decide))
    (originalFirstInterval (ii := 0) (ij := 1)
      hf hroom hs hs c.isLt d.isLt (by decide) (by decide))
    (originalMixedInterval hf hroom hs hs a.isLt b.isLt c.isLt d.isLt) K

/-- The original deficit value at the shared explicit cutoff. -/
def deficit_value_interval {width blocks : Nat} {face : Z4Plaq}
    (hroom : N width ≤ blocks) {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (he : (0 : Q') < epsilon) (K : Nat)
    (hK : pairedDeficitCutoff w epsilon ≤ K) :
    Interval blocks (faceDeficit w K width face) epsilon :=
  deficitInterval hw0 hw1 (faceSquare hroom) epsilon he (K+1)
    (by unfold pairedDeficitCutoff at hK; omega)

/-- First selected-edge deficit cap `2 epsilon`, on the same face word. -/
def deficit_first_interval {width blocks : Nat} {face : Z4Plaq} {l : Z4Link}
    (hf : face ∈ spatialFaces width) (hl : l ∈ edgesOf face)
    (hroom : N width ≤ blocks) {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (he : (0 : Q') < epsilon) (K : Nat)
    (hK : pairedDeficitCutoff w epsilon ≤ K) (i : Fin 3) :
    Interval blocks
      (pairedDerivativeAt ((baseLinks width).idxOf l) i (faceDeficit w K width face))
      (2*epsilon) := by
  have hs : (baseLinks width).idxOf l < blocks :=
    Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem (face_link_mem_base hf hl)) hroom
  apply firstInterval (block := (baseLinks width).idxOf l) _ i
  intro a b
  exact QuaternionHaarHeatAngularDeficit.angularDeficitInterval
    (by omega) (by omega) hw0 hw1 (faceSquare hroom)
    (originalFirstInterval (ii := 0) (ij := 1)
      hf hroom hs hs a.isLt b.isLt (by decide) (by decide))
    he (K+1) (by unfold pairedDeficitCutoff at hK; omega)

/-- All nine ordered selected-edge deficit entries, cap `4 epsilon`. -/
def deficit_mixed_interval {width blocks : Nat} {face : Z4Plaq} {l : Z4Link}
    (hf : face ∈ spatialFaces width) (hl : l ∈ edgesOf face)
    (hroom : N width ≤ blocks) {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (he : (0 : Q') < epsilon) (K : Nat)
    (hK : pairedDeficitCutoff w epsilon ≤ K) (i j : Fin 3) :
    Interval blocks
      (pairedDerivativeAt ((baseLinks width).idxOf l) i
        (pairedDerivativeAt ((baseLinks width).idxOf l) j (faceDeficit w K width face)))
      (4*epsilon) := by
  have hs : (baseLinks width).idxOf l < blocks :=
    Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem (face_link_mem_base hf hl)) hroom
  let E := deficit_value_interval (face := face) hroom hw0 hw1 he K hK
  apply mixedInterval hs E.support _ i j
  intro a b c d
  exact QuaternionHaarHeatMixedAngularDeficit.mixedAngularDeficitInterval
    (by omega) (by omega) (by omega) (by omega) hw0 hw1 (faceSquare hroom)
    (originalFirstInterval (ii := 0) (ij := 1)
      hf hroom hs hs a.isLt b.isLt (by decide) (by decide))
    (originalFirstInterval (ii := 0) (ij := 1)
      hf hroom hs hs c.isLt d.isLt (by decide) (by decide))
    (originalMixedInterval hf hroom hs hs a.isLt b.isLt c.isLt d.isLt)
    he (K+1) (by unfold pairedDeficitCutoff at hK; omega)

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.paired_mixed_expansion
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.mixedInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.pairedAt_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.facePrefix
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.faceJacobi
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.faceDeficit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.pairedDeficitCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.prefixValueCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.prefixFirstCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.prefixSecondCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.prefix_split_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.prefix_first_split_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.prefix_mixed_split_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.prefix_value_interval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.prefix_first_interval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.prefix_mixed_interval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.deficit_value_interval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.deficit_first_interval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.deficit_mixed_interval
