/-
# Actual paired jets and Jacobi deficits of the ORIGINAL heat prefix

The original prefix is coefficientwise the literal finite normalized
Jacobi heat at N=K+1 plus its original deficit. Existing value, first and
mixed deficit producers construct the paired caps epsilon, 2*epsilon and
4*epsilon. The second jet retains all FOUR ordered plane derivatives,
including both negative cross terms in the middle paired direction.

The original prefix and its paired jets also receive cutoff-independent
caps at each strict nome. The explicit cutoff is data and does not depend
on the carrier or direction. No floor, curvature premise, interacting
conditional estimate, completed OS or scaling claim occurs here.
-/

import YMGap.Continuum.SU2QuaternionPairedJacobiCurvature
import YMGap.Continuum.QuaternionHaarHeatAngularDeficit
import YMGap.Continuum.QuaternionHaarHeatMixedAngularDeficit
import YMGap.Continuum.SU2QuaternionRelativeHeatSecondAngularBound

namespace YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarAngularCarrier (angularDerivative_neg intervalNeg)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_add)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
  (deficitPolynomial prefixInterval prefix_eq_weighted_add_deficit)
open YMGap.Continuum.QuaternionHaarHeatAngularDerivative
  (heatDerivativeCap heatPrefixAngularIntervalAt)
open YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative
  (heatSecondDerivativeCap heatPrefixSecondAngularIntervalAt)
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection (relativeScalar)
open YMGap.Continuum.SU2QuaternionRelativeHeatAngularBound (scalarAngularInterval)
open YMGap.Continuum.SU2QuaternionRelativeHeatSecondAngularBound (scalarAt_mixedAngularInterval)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (pairedDerivative)
open YMGap.Continuum.SU2QuaternionPairedScalarSquare (relativeScalarSquare)
open YMGap.Continuum.SU2QuaternionPairedJacobiCurvature (pairedHeat)
open YMGap.Continuum.QPolyHaarAngularChain (paired_congr)

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Actual paired differentiation preserves the original finite support. -/
theorem paired_supported {blocks : Nat} (hb : 0 < blocks) (i : Fin 3)
    {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (pairedDerivative i p) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact supported_add (angularDerivative_supported_at (by omega) (by omega) hp)
      (angularDerivative_supported_at (by omega) (by omega) hp)
  · exact supported_add (angularDerivative_supported_at (by omega) (by omega) hp)
      (support_neg (angularDerivative_supported_at (by omega) (by omega) hp))
  · exact supported_add (angularDerivative_supported_at (by omega) (by omega) hp)
      (angularDerivative_supported_at (by omega) (by omega) hp)

/-- Additivity of the literal paired derivative, for arbitrary polynomials. -/
theorem paired_add (i : Fin 3) (p q : RatPoly) :
    RatPolyCoeffEqv (pairedDerivative i (polyAdd p q))
      (polyAdd (pairedDerivative i p) (pairedDerivative i q)) := by
  have hp (a b c d : RatPoly) : RatPolyCoeffEqv
      (polyAdd (polyAdd a b) (polyAdd c d)) (polyAdd (polyAdd a c) (polyAdd b d)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
      (by decide) (fun
        | 0 => a
        | 1 => b
        | 2 => c
        | _ => d)
  have hm (a b c d : RatPoly) : RatPolyCoeffEqv
      (polyAdd (polyAdd a b) (polyNeg (polyAdd c d)))
      (polyAdd (polyAdd a (polyNeg c)) (polyAdd b (polyNeg d))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
      (by decide) (fun
        | 0 => a
        | 1 => b
        | 2 => c
        | _ => d)
  rcases direction_cases i with rfl | rfl | rfl
  · exact ((angularDerivative_add 0 1 p q).add (angularDerivative_add 2 3 p q)).trans (hp _ _ _ _)
  · exact ((angularDerivative_add 0 2 p q).add
      (RatPolyCoeffEqv.neg (angularDerivative_add 1 3 p q))).trans (hm _ _ _ _)
  · exact ((angularDerivative_add 0 3 p q).add (angularDerivative_add 1 2 p q)).trans (hp _ _ _ _)

private def secondPlus (a b c d : Nat) (p : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd (angularDerivative a b (angularDerivative a b p))
      (angularDerivative a b (angularDerivative c d p)))
    (polyAdd (angularDerivative c d (angularDerivative a b p))
      (angularDerivative c d (angularDerivative c d p)))

private def secondMinus (a b c d : Nat) (p : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd (angularDerivative a b (angularDerivative a b p))
      (polyNeg (angularDerivative a b (angularDerivative c d p))))
    (polyNeg (polyAdd (angularDerivative c d (angularDerivative a b p))
      (polyNeg (angularDerivative c d (angularDerivative c d p)))))

/-- Four ordered second derivatives. The nested minus in direction one
preserves the positive final diagonal and BOTH negative cross terms. -/
def secondExpansion (i : Fin 3) (p : RatPoly) : RatPoly :=
  match i.val with
  | 0 => secondPlus 0 1 2 3 p
  | 1 => secondMinus 0 2 1 3 p
  | _ => secondPlus 0 3 1 2 p

theorem paired_second_expansion (i : Fin 3) (p : RatPoly) :
    RatPolyCoeffEqv (pairedDerivative i (pairedDerivative i p)) (secondExpansion i p) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact (angularDerivative_add 0 1 _ _).add (angularDerivative_add 2 3 _ _)
  · exact ((angularDerivative_add 0 2 _ _).trans
      ((RatPolyCoeffEqv.refl _).add (angularDerivative_neg 0 2 _))).add
      (RatPolyCoeffEqv.neg ((angularDerivative_add 1 3 _ _).trans
        ((RatPolyCoeffEqv.refl _).add (angularDerivative_neg 1 3 _))))
  · exact (angularDerivative_add 0 3 _ _).add (angularDerivative_add 1 2 _ _)

private theorem double_pin (a : Q') : Q'.eqv (a+a) (2*a) :=
  poly_identity_of_normal_eq (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
    (by decide) (fun _ => a)

private theorem four_pin (a : Q') : Q'.eqv ((a+a)+(a+a)) (4*a) :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
    (.mul (.const 4) (.var 0)) (by decide) (fun _ => a)

private def firstInterval {blocks : Nat} {p : RatPoly} {a : Q'}
    (hb : 0 < blocks) (hp : SupportedQuaternionBlocks blocks p)
    (F : ∀ i j : Fin 4, Interval blocks (angularDerivative i.val j.val p) a)
    (i : Fin 3) : Interval blocks (pairedDerivative i p) (2*a) := by
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

private def secondInterval {blocks : Nat} {p : RatPoly} {a : Q'}
    (hb : 0 < blocks) (hp : SupportedQuaternionBlocks blocks p)
    (F : ∀ i j k l : Fin 4,
      Interval blocks (angularDerivative i.val j.val (angularDerivative k.val l.val p)) a)
    (i : Fin 3) : Interval blocks (pairedDerivative i (pairedDerivative i p)) (4*a) := by
  have hs := paired_supported hb i (paired_supported hb i hp)
  refine Interval.ofCoeff hs (paired_second_expansion i p) ?_
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    exact (((F 0 1 0 1).add (F 0 1 2 3)).add
      ((F 2 3 0 1).add (F 2 3 2 3))).changeCap (four_pin a)
  · by_cases h1 : i.val=1
    · have hi : i=1 := Fin.ext h1
      subst i
      exact (((F 0 2 0 2).add (intervalNeg (F 0 2 1 3))).add
        (intervalNeg ((F 1 3 0 2).add (intervalNeg (F 1 3 1 3))))).changeCap (four_pin a)
    · have hi : i=2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      exact (((F 0 3 0 3).add (F 0 3 1 2)).add
        ((F 1 2 0 3).add (F 1 2 1 2))).changeCap (four_pin a)

/-- The literal original, unweighted, all-spin heat prefix. -/
def pairedPrefix (w : Q') (K : Nat) : RatPoly := heatPrefix w K relativeScalar

/-- The actual Jacobi deficit, with the required N=K+1 preserved. -/
def pairedDeficit (w : Q') (K : Nat) : RatPoly := deficitPolynomial w (K+1) relativeScalar

/-- One explicit cutoff pays all three original deficit producers. -/
def pairedDeficitCutoff (w epsilon : Q') : Nat :=
  max (BF4ExactSlabJacobiDeficitInterval.deficitCutoff w epsilon)
    (max (QuaternionHaarHeatAngularDeficit.deficitCutoff w 32 epsilon)
      (QuaternionHaarHeatMixedAngularDeficit.deficitCutoff w 32 32 64 epsilon))

/-- SAME polynomial decomposition at the exact K+1 Jacobi prefix. -/
theorem prefix_split_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) :
    RatPolyCoeffEqv (pairedPrefix w K) (polyAdd (pairedHeat w (K+1)) (pairedDeficit w K)) :=
  (prefix_eq_weighted_add_deficit w K relativeScalar).trans
    ((JacobiWeightedHeatPolynomial.shiftedHeat_subst_coeffEqv_weightedPolynomial
      hw0 hw1 (K+1) relativeScalar).symm.add (.refl _))

theorem prefix_first_split_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (i : Fin 3) :
    RatPolyCoeffEqv (pairedDerivative i (pairedPrefix w K))
      (polyAdd (pairedDerivative i (pairedHeat w (K+1))) (pairedDerivative i (pairedDeficit w K))) :=
  (paired_congr i (prefix_split_pin hw0 hw1 K)).trans (paired_add i _ _)

theorem prefix_second_split_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (i : Fin 3) :
    RatPolyCoeffEqv (pairedDerivative i (pairedDerivative i (pairedPrefix w K)))
      (polyAdd (pairedDerivative i (pairedDerivative i (pairedHeat w (K+1))))
        (pairedDerivative i (pairedDerivative i (pairedDeficit w K)))) :=
  (paired_congr i (prefix_first_split_pin hw0 hw1 K i)).trans (paired_add i _ _)

def deficit_value_interval {blocks : Nat} {w epsilon : Q'} (hb : 1 < blocks)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (he : (0 : Q') < epsilon)
    (K : Nat) (hK : pairedDeficitCutoff w epsilon ≤ K) :
    Interval blocks (pairedDeficit w K) epsilon :=
  QuaternionHaarAllNomeHeatCertificate.deficitInterval hw0 hw1 (relativeScalarSquare hb)
    epsilon he (K+1) (by unfold pairedDeficitCutoff at hK; omega)

def deficit_first_interval {blocks : Nat} {w epsilon : Q'} (hb : 1 < blocks)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (he : (0 : Q') < epsilon)
    (K : Nat) (hK : pairedDeficitCutoff w epsilon ≤ K) (i : Fin 3) :
    Interval blocks (pairedDerivative i (pairedDeficit w K)) (2*epsilon) := by
  let E := deficit_value_interval hb hw0 hw1 he K hK
  apply firstInterval (by omega : 0 < blocks) E.support _ i
  intro j k
  exact QuaternionHaarHeatAngularDeficit.angularDeficitInterval
    (by omega) (by omega) hw0 hw1 (relativeScalarSquare hb)
    (scalarAngularInterval (by omega : 0 < blocks) hb (by omega) (by omega))
    he (K+1) (by unfold pairedDeficitCutoff at hK; omega)

def deficit_second_interval {blocks : Nat} {w epsilon : Q'} (hb : 1 < blocks)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (he : (0 : Q') < epsilon)
    (K : Nat) (hK : pairedDeficitCutoff w epsilon ≤ K) (i : Fin 3) :
    Interval blocks (pairedDerivative i (pairedDerivative i (pairedDeficit w K))) (4*epsilon) := by
  let E := deficit_value_interval hb hw0 hw1 he K hK
  apply secondInterval (by omega : 0 < blocks) E.support _ i
  intro j k l m
  simpa only [Nat.mul_zero, Nat.zero_add, pairedDeficit] using
    (QuaternionHaarHeatMixedAngularDeficit.mixedAngularDeficitInterval
    (by omega) (by omega) (by omega) (by omega) hw0 hw1 (relativeScalarSquare hb)
    (scalarAngularInterval (by omega : 0 < blocks) hb (by omega) (by omega))
    (scalarAngularInterval (by omega : 0 < blocks) hb (by omega) (by omega))
    (scalarAt_mixedAngularInterval (by omega : 0 < blocks) hb
      (by omega : 0 < blocks) (by omega : 0 < blocks) j.isLt k.isLt l.isLt m.isLt)
    he (K+1) (by unfold pairedDeficitCutoff at hK; omega))

def prefixValueCap (w : Q') : Q' := BF4ExactSlabAllNomeTailInterval.prefixCap w
def prefixFirstCap (w : Q') : Q' := 2*heatDerivativeCap w 32
def prefixSecondCap (w : Q') : Q' := 4*heatSecondDerivativeCap w 32 32 64

/-- Original value cap, independent of K and the number of Haar blocks. -/
def prefix_value_interval {blocks : Nat} {w : Q'} (hb : 1 < blocks)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) :
    Interval blocks (pairedPrefix w K) (prefixValueCap w) :=
  prefixInterval hw0 hw1 (relativeScalarSquare hb) K

/-- Original first paired-jet cap, at EVERY cutoff. -/
def prefix_first_interval {blocks : Nat} {w : Q'} (hb : 1 < blocks)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (i : Fin 3) :
    Interval blocks (pairedDerivative i (pairedPrefix w K)) (prefixFirstCap w) := by
  let P := prefix_value_interval hb hw0 hw1 K
  apply firstInterval (by omega : 0 < blocks) P.support _ i
  intro j k
  exact heatPrefixAngularIntervalAt (by omega) (by omega) hw0 hw1 (relativeScalarSquare hb)
    (scalarAngularInterval (by omega : 0 < blocks) hb (by omega) (by omega)) K

/-- Original second paired-jet cap, retaining all ordered terms, at EVERY cutoff. -/
def prefix_second_interval {blocks : Nat} {w : Q'} (hb : 1 < blocks)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (i : Fin 3) :
    Interval blocks (pairedDerivative i (pairedDerivative i (pairedPrefix w K))) (prefixSecondCap w) := by
  let P := prefix_value_interval hb hw0 hw1 K
  apply secondInterval (by omega : 0 < blocks) P.support _ i
  intro j k l m
  simpa only [Nat.mul_zero, Nat.zero_add, pairedPrefix] using
    (heatPrefixSecondAngularIntervalAt (by omega) (by omega) (by omega) (by omega)
    hw0 hw1 (relativeScalarSquare hb)
    (scalarAngularInterval (by omega : 0 < blocks) hb (by omega) (by omega))
    (scalarAngularInterval (by omega : 0 < blocks) hb (by omega) (by omega))
    (scalarAt_mixedAngularInterval (by omega : 0 < blocks) hb
      (by omega : 0 < blocks) (by omega : 0 < blocks) j.isLt k.isLt l.isLt m.isLt) K)

end YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit

#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit.paired_supported
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit.paired_add
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit.paired_second_expansion
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit.pairedDeficitCutoff
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit.prefix_split_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit.prefix_first_split_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit.prefix_second_split_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit.deficit_value_interval
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit.deficit_first_interval
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit.deficit_second_interval
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit.prefix_value_interval
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit.prefix_first_interval
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit.prefix_second_interval
