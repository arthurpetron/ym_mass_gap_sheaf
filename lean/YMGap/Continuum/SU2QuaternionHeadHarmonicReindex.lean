/-
# Head harmonicity under head-fixing block reindexing

Transport the literal coefficient Laplacian, not merely its Haar pairing.
The intended consumer inserts a retained heat partner into an exposed
plaquette chart without expanding the degree-eight polynomial.
-/

import YMGap.Continuum.SU2QuaternionAngularReindex
import YMGap.Continuum.SU2QuaternionTranslationWordComposition

namespace YMGap.Continuum.SU2QuaternionHeadHarmonicReindex

set_option autoImplicit false

open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

/-- A block involution fixing zero commutes with the four-coordinate head
Laplacian at coefficient level. -/
theorem headLaplacian_reindex {blocks : Nat} (hb : 0 < blocks)
    (s : QuaternionBlockInvolution blocks) (hs : s.map 0 = 0) (p : RatPoly) :
    RatPolyCoeffEqv (reindexQuaternionPolynomial s (headLaplacian p))
      (headLaplacian (reindexQuaternionPolynomial s p)) := by
  have hd (i : Fin 4) (q : RatPoly) :
      RatPolyCoeffEqv (reindexQuaternionPolynomial s (ratDerivative i.val q))
        (ratDerivative i.val (reindexQuaternionPolynomial s q)) := by
    have hi := i.isLt
    have h := reindex_ratDerivative s i.val (by omega) q
    simpa only [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, hs,
      Nat.mul_zero, Nat.zero_add] using h
  have hdd (i : Fin 4) :
      RatPolyCoeffEqv
        (reindexQuaternionPolynomial s (ratDerivative i.val (ratDerivative i.val p)))
        (ratDerivative i.val (ratDerivative i.val (reindexQuaternionPolynomial s p))) :=
    (hd i (ratDerivative i.val p)).trans ((hd i p).derivative i.val)
  unfold headLaplacian
  simp only [reindexQuaternionPolynomial_add]
  exact (hdd 0).add ((hdd 1).add ((hdd 2).add (hdd 3)))

/-- Coefficient harmonicity survives one explicitly head-fixing involution. -/
theorem harmonic_reindex {blocks : Nat} (hb : 0 < blocks)
    (s : QuaternionBlockInvolution blocks) (hs : s.map 0 = 0) {p : RatPoly}
    (hp : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    RatPolyCoeffEqv (headLaplacian (reindexQuaternionPolynomial s p)) polyZero :=
  (headLaplacian_reindex hb s hs p).symm.trans (RatPolyCoeffEqv.reindex s hp)

/-- Finite tail-coordinate changes preserve the same literal head harmonicity. -/
theorem harmonic_swapChain {blocks : Nat} (hb : 0 < blocks) :
    ∀ (steps : List (QuaternionBlockInvolution blocks)),
      (∀ s, s ∈ steps → s.map 0 = 0) → ∀ {p : RatPoly},
      RatPolyCoeffEqv (headLaplacian p) polyZero →
      RatPolyCoeffEqv (headLaplacian (applyQuaternionBlockSwapChain steps p)) polyZero
  | [], _, _, hp => hp
  | s::steps, hs, _, hp =>
      harmonic_swapChain hb steps (fun t ht => hs t (List.mem_cons_of_mem s ht))
        (harmonic_reindex hb s (hs s List.mem_cons_self) hp)

end YMGap.Continuum.SU2QuaternionHeadHarmonicReindex

#print axioms YMGap.Continuum.SU2QuaternionHeadHarmonicReindex.headLaplacian_reindex
#print axioms YMGap.Continuum.SU2QuaternionHeadHarmonicReindex.harmonic_reindex
#print axioms YMGap.Continuum.SU2QuaternionHeadHarmonicReindex.harmonic_swapChain
