/-
# Every ordered paired mixed jet of the ORIGINAL heat prefix

The original prefix and its literal N=K+1 Jacobi deficit retain all four
ordered plane derivatives for each pair of paired directions. The inner
and outer signs are independent: no mixed order is omitted or commuted.
Existing raw mixed producers give deficit cap 4*epsilon at the SAME named
cutoff, and prefix cap prefixSecondCap at every K. These are actual finite
interval witnesses, not a curvature, conditional or scaling premise.
-/

import YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit

namespace YMGap.Continuum.SU2QuaternionPairedHeatPrefixMixedDeficit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarAngularCarrier (angularDerivative_neg intervalNeg)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (pairedDerivative)
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit
open YMGap.Continuum.SU2QuaternionPairedJacobiCurvature (pairedHeat)
open YMGap.Continuum.SU2QuaternionPairedScalarSquare (relativeScalarSquare)
open YMGap.Continuum.QPolyHaarAngularChain (paired_congr)
open YMGap.Continuum.SU2QuaternionRelativeHeatAngularBound (scalarAngularInterval)
open YMGap.Continuum.SU2QuaternionRelativeHeatSecondAngularBound (scalarAt_mixedAngularInterval)
open YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative
  (heatPrefixSecondAngularIntervalAt)

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

private def planeDerivative (a : Fin 4 × Fin 4) (p : RatPoly) : RatPoly :=
  angularDerivative a.1.val a.2.val p

private def signedTerm (i : Fin 3) (p : RatPoly) : RatPoly :=
  if i.val=1 then polyNeg p else p

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

private theorem paired_representation (i : Fin 3) (p : RatPoly) :
    RatPolyCoeffEqv (pairedDerivative i p)
      (polyAdd (planeDerivative (firstPlane i) p)
        (signedTerm i (planeDerivative (secondPlane i) p))) := by
  rcases direction_cases i with rfl | rfl | rfl
  all_goals exact RatPolyCoeffEqv.refl _

private theorem signed_congr (i : Fin 3) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : RatPolyCoeffEqv (signedTerm i p) (signedTerm i q) := by
  unfold signedTerm
  split
  · exact RatPolyCoeffEqv.neg h
  · exact h

private theorem angular_signed (a : Fin 4 × Fin 4) (i : Fin 3) (p : RatPoly) :
    RatPolyCoeffEqv (planeDerivative a (signedTerm i p))
      (signedTerm i (planeDerivative a p)) := by
  unfold signedTerm
  split
  · exact angularDerivative_neg a.1.val a.2.val p
  · exact RatPolyCoeffEqv.refl _

private theorem angular_paired (a : Fin 4 × Fin 4) (j : Fin 3) (p : RatPoly) :
    RatPolyCoeffEqv (planeDerivative a (pairedDerivative j p))
      (polyAdd (planeDerivative a (planeDerivative (firstPlane j) p))
        (signedTerm j (planeDerivative a (planeDerivative (secondPlane j) p)))) :=
  (angularDerivative_congr a.1.val a.2.val (paired_representation j p)).trans
    ((angularDerivative_add a.1.val a.2.val _ _).trans
      ((RatPolyCoeffEqv.refl _).add (angular_signed a j _)))

/-- All FOUR literal ordered plane jets; each paired direction retains
its own sign, including the positive double-minus term. -/
def mixedExpansion (i j : Fin 3) (p : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd (planeDerivative (firstPlane i) (planeDerivative (firstPlane j) p))
      (signedTerm j (planeDerivative (firstPlane i) (planeDerivative (secondPlane j) p))))
    (signedTerm i
      (polyAdd (planeDerivative (secondPlane i) (planeDerivative (firstPlane j) p))
        (signedTerm j (planeDerivative (secondPlane i) (planeDerivative (secondPlane j) p)))))

/-- Coefficientwise expansion of the actual ordered Ji(Jj p). -/
theorem paired_mixed_expansion (i j : Fin 3) (p : RatPoly) :
    RatPolyCoeffEqv (pairedDerivative i (pairedDerivative j p)) (mixedExpansion i j p) :=
  (paired_representation i (pairedDerivative j p)).trans
    ((angular_paired (firstPlane i) j p).add
      (signed_congr i (angular_paired (secondPlane i) j p)))

private def signedInterval {blocks : Nat} {p : RatPoly} {a : Q'}
    (i : Fin 3) (P : Interval blocks p a) : Interval blocks (signedTerm i p) a := by
  unfold signedTerm
  split
  · exact intervalNeg P
  · exact P

private theorem four_pin (a : Q') : Q'.eqv ((a+a)+(a+a)) (4*a) :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
    (.mul (.const 4) (.var 0)) (by decide) (fun _ => a)

/-- A constructive four-term interval assembly for EVERY ordered paired
mixed jet. The raw interval family is an existing finite producer. -/
def mixedInterval {blocks : Nat} {p : RatPoly} {a : Q'}
    (hb : 0 < blocks) (hp : SupportedQuaternionBlocks blocks p)
    (F : ∀ i j k l : Fin 4,
      Interval blocks (angularDerivative i.val j.val (angularDerivative k.val l.val p)) a)
    (i j : Fin 3) : Interval blocks (pairedDerivative i (pairedDerivative j p)) (4*a) := by
  have hs := paired_supported hb i (paired_supported hb j hp)
  refine Interval.ofCoeff hs (paired_mixed_expansion i j p) ?_
  exact (((F (firstPlane i).1 (firstPlane i).2 (firstPlane j).1 (firstPlane j).2).add
    (signedInterval j (F (firstPlane i).1 (firstPlane i).2 (secondPlane j).1 (secondPlane j).2))).add
    (signedInterval i
      ((F (secondPlane i).1 (secondPlane i).2 (firstPlane j).1 (firstPlane j).2).add
        (signedInterval j (F (secondPlane i).1 (secondPlane i).2
          (secondPlane j).1 (secondPlane j).2))))).changeCap (four_pin a)

/-- The SAME original-prefix split after both ordered paired derivatives. -/
theorem prefix_mixed_split_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (i j : Fin 3) :
    RatPolyCoeffEqv (pairedDerivative i (pairedDerivative j (pairedPrefix w K)))
      (polyAdd (pairedDerivative i (pairedDerivative j (pairedHeat w (K+1))))
        (pairedDerivative i (pairedDerivative j (pairedDeficit w K)))) :=
  (paired_congr i (prefix_first_split_pin hw0 hw1 K j)).trans (paired_add i _ _)

/-- Actual ordered paired deficit cap, at the EXISTING shared cutoff. -/
def deficit_mixed_interval {blocks : Nat} {w epsilon : Q'} (hb : 1 < blocks)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (he : (0 : Q') < epsilon)
    (K : Nat) (hK : pairedDeficitCutoff w epsilon ≤ K) (i j : Fin 3) :
    Interval blocks (pairedDerivative i (pairedDerivative j (pairedDeficit w K))) (4*epsilon) := by
  let E := deficit_value_interval hb hw0 hw1 he K hK
  apply mixedInterval (by omega : 0 < blocks) E.support _ i j
  intro a b c d
  simpa only [Nat.mul_zero, Nat.zero_add, pairedDeficit] using
    (QuaternionHaarHeatMixedAngularDeficit.mixedAngularDeficitInterval
      (by omega) (by omega) (by omega) (by omega) hw0 hw1 (relativeScalarSquare hb)
      (scalarAngularInterval (by omega : 0 < blocks) hb (by omega) (by omega))
      (scalarAngularInterval (by omega : 0 < blocks) hb (by omega) (by omega))
      (scalarAt_mixedAngularInterval (by omega : 0 < blocks) hb
        (by omega : 0 < blocks) (by omega : 0 < blocks) a.isLt b.isLt c.isLt d.isLt)
      he (K+1) (by unfold pairedDeficitCutoff at hK; omega))

/-- Actual ordered paired prefix cap, independent of K and carrier size. -/
def prefix_mixed_interval {blocks : Nat} {w : Q'} (hb : 1 < blocks)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (i j : Fin 3) :
    Interval blocks (pairedDerivative i (pairedDerivative j (pairedPrefix w K))) (prefixSecondCap w) := by
  let P := prefix_value_interval hb hw0 hw1 K
  apply mixedInterval (by omega : 0 < blocks) P.support _ i j
  intro a b c d
  simpa only [Nat.mul_zero, Nat.zero_add, pairedPrefix] using
    (heatPrefixSecondAngularIntervalAt (by omega) (by omega) (by omega) (by omega)
      hw0 hw1 (relativeScalarSquare hb)
      (scalarAngularInterval (by omega : 0 < blocks) hb (by omega) (by omega))
      (scalarAngularInterval (by omega : 0 < blocks) hb (by omega) (by omega))
      (scalarAt_mixedAngularInterval (by omega : 0 < blocks) hb
        (by omega : 0 < blocks) (by omega : 0 < blocks) a.isLt b.isLt c.isLt d.isLt) K)

end YMGap.Continuum.SU2QuaternionPairedHeatPrefixMixedDeficit

#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixMixedDeficit.paired_mixed_expansion
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixMixedDeficit.mixedInterval
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixMixedDeficit.prefix_mixed_split_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixMixedDeficit.deficit_mixed_interval
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixMixedDeficit.prefix_mixed_interval
