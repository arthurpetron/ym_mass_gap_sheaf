/-
# A certified reverse comparison for the one-step form

`PositiveContractionOneStepCompletion` supplies the easy direction: the
identity on representatives maps the original completion into the one-step
form completion because the latter distance is bounded above by the former.
It deliberately does not claim an equivalence of the two norms.

This file records the missing direction as an explicit, constructive
certificate.  A supplied positive coercivity modulus `κ` transports Cauchy
moduli and null witnesses back to the original carrier and therefore gives a
well-defined map on the quotient completions.  No coercivity theorem for a
particular Yang--Mills kernel is asserted here; producing such a certificate
remains a physical obligation.
-/

import YMGap.Continuum.PositiveContractionOneStepCompletion

namespace YMGap.Continuum.PositiveContractionReverseComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.PositiveContractionOneStepForm
open YMGap.Continuum.PositiveContractionOneStepCompletion

local infix:50 " ≈ " => Q'.eqv

/-- A constructive lower comparison between the original and one-step
quadratic distances.  The carrier is unchanged, but the one-step form is
allowed to have a different norm. -/
structure ReverseComparisonCoercivity
    (D : SmulGNSData) (S : DiagonalTransferSymbol D)
    (hsa : ∀ a b, D.toGNSData.B a (S.Dv b) ≈ D.toGNSData.B (S.Dv a) b)
    (hpos : ∀ a, (0 : Q') ≤ D.toGNSData.B a (S.Dv a)) : Type where
  κ : Q'
  κ_pos : (0 : Q') < κ
  lower : ∀ a b : D.toGNSData.V,
    κ * D.toGNSData.distSqQ a b ≤
      (oneStepSmulGNSData D S.Dv hsa hpos).toGNSData.distSqQ a b

/-- Reverse transport of a one-step-form Cauchy sequence.  Its modulus is
rescaled by the supplied coercivity constant. -/
def reverseComparisonCauchy
    {D : SmulGNSData} {S : DiagonalTransferSymbol D}
    {hsa : ∀ a b, D.toGNSData.B a (S.Dv b) ≈ D.toGNSData.B (S.Dv a) b}
    {hpos : ∀ a, (0 : Q') ≤ D.toGNSData.B a (S.Dv a)}
    (certificate : ReverseComparisonCoercivity D S hsa hpos)
    (Y : CauchyGNS (oneStepSmulGNSData D S.Dv hsa hpos).toGNSData) :
    CauchyGNS D.toGNSData where
  seq := Y.seq
  modulus := fun ε => Y.modulus (certificate.κ * ε)
  isCauchy := by
    intro ε hε p q hp hq
    have hκε : (0 : Q') < certificate.κ * ε :=
      Q'.mul_pos certificate.κ_pos hε
    have hY := Y.isCauchy (certificate.κ * ε) hκε p q hp hq
    have hlower := certificate.lower (Y.seq p) (Y.seq q)
    apply Q'.le_of_mul_le_mul_left (c := certificate.κ) _ certificate.κ_pos
    exact Q'.le_trans' _ _ _ hlower hY

theorem reverseComparisonCauchy_null
    {D : SmulGNSData} {S : DiagonalTransferSymbol D}
    {hsa : ∀ a b, D.toGNSData.B a (S.Dv b) ≈ D.toGNSData.B (S.Dv a) b}
    {hpos : ∀ a, (0 : Q') ≤ D.toGNSData.B a (S.Dv a)}
    (certificate : ReverseComparisonCoercivity D S hsa hpos)
    {X Y : CauchyGNS (oneStepSmulGNSData D S.Dv hsa hpos).toGNSData}
    (h : CauchyNull (oneStepSmulGNSData D S.Dv hsa hpos).toGNSData X Y) :
    CauchyNull D.toGNSData
      (reverseComparisonCauchy certificate X)
      (reverseComparisonCauchy certificate Y) := by
  intro ε hε
  have hκε : (0 : Q') < certificate.κ * ε :=
    Q'.mul_pos certificate.κ_pos hε
  obtain ⟨N, hN⟩ := h (certificate.κ * ε) hκε
  refine ⟨N, fun n hn => ?_⟩
  have hlower := certificate.lower (X.seq n) (Y.seq n)
  apply Q'.le_of_mul_le_mul_left (c := certificate.κ) _ certificate.κ_pos
  exact Q'.le_trans' _ _ _ hlower (hN n hn)

/-- The reverse comparison descends through the Cauchy quotient. -/
def reverseComparison
    {D : SmulGNSData} {S : DiagonalTransferSymbol D}
    {hsa : ∀ a b, D.toGNSData.B a (S.Dv b) ≈ D.toGNSData.B (S.Dv a) b}
    {hpos : ∀ a, (0 : Q') ≤ D.toGNSData.B a (S.Dv a)}
    (certificate : ReverseComparisonCoercivity D S hsa hpos) :
    GNSCompletionSpace (oneStepSmulGNSData D S.Dv hsa hpos).toGNSData →
      GNSCompletionSpace D.toGNSData :=
  Quotient.lift
    (fun Y => Quotient.mk (cauchySetoid D.toGNSData)
      (reverseComparisonCauchy certificate Y))
    (fun _ _ h => Quotient.sound (reverseComparisonCauchy_null certificate h))

theorem reverseComparison_embed
    {D : SmulGNSData} {S : DiagonalTransferSymbol D}
    {hsa : ∀ a b, D.toGNSData.B a (S.Dv b) ≈ D.toGNSData.B (S.Dv a) b}
    {hpos : ∀ a, (0 : Q') ≤ D.toGNSData.B a (S.Dv a)}
    (certificate : ReverseComparisonCoercivity D S hsa hpos)
    (a : D.toGNSData.V) :
    reverseComparison certificate
        (embedV (oneStepSmulGNSData D S.Dv hsa hpos).toGNSData a) =
      embedV D.toGNSData a := rfl

/-- Once both comparison certificates are supplied, the reverse and forward
maps agree with the identity on the original quotient completion.  The proof
uses only that both maps retain the same representative sequence; it does not
claim an unproved norm equivalence. -/
theorem reverseComparison_comparison
    {D : SmulGNSData} {S : DiagonalTransferSymbol D}
    {hsa : ∀ a b, D.toGNSData.B a (S.Dv b) ≈ D.toGNSData.B (S.Dv a) b}
    {hpos : ∀ a, (0 : Q') ≤ D.toGNSData.B a (S.Dv a)}
    {hupper : ∀ a, D.toGNSData.B a (S.Dv a) ≤ D.toGNSData.B a a}
    (certificate : ReverseComparisonCoercivity D S hsa hpos)
    (x : GNSCompletionSpace D.toGNSData) :
    reverseComparison certificate
        (comparison D S hsa hpos hupper x) = x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  change CauchyNull D.toGNSData X
      (reverseComparisonCauchy certificate
      (comparisonCauchy D S hsa hpos hupper X))
  exact cauchyNull_refl D.toGNSData X

/-- The same representative-sequence argument gives the identity on the
one-step-form quotient completion. -/
theorem comparison_reverseComparison
    {D : SmulGNSData} {S : DiagonalTransferSymbol D}
    {hsa : ∀ a b, D.toGNSData.B a (S.Dv b) ≈ D.toGNSData.B (S.Dv a) b}
    {hpos : ∀ a, (0 : Q') ≤ D.toGNSData.B a (S.Dv a)}
    {hupper : ∀ a, D.toGNSData.B a (S.Dv a) ≤ D.toGNSData.B a a}
    (certificate : ReverseComparisonCoercivity D S hsa hpos)
    (y : GNSCompletionSpace (oneStepSmulGNSData D S.Dv hsa hpos).toGNSData) :
    comparison D S hsa hpos hupper
        (reverseComparison certificate y) = y := by
  refine Quotient.inductionOn y ?_
  intro Y
  apply Quotient.sound
  change CauchyNull (oneStepSmulGNSData D S.Dv hsa hpos).toGNSData
    (comparisonCauchy D S hsa hpos hupper
      (reverseComparisonCauchy certificate Y)) Y
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  change (oneStepSmulGNSData D S.Dv hsa hpos).toGNSData.distSqQ
      (Y.seq n) (Y.seq n) ≤ ε
  exact Q'.le_trans' _ 0 ε
    (Q'.le_of_eqv
      ((oneStepSmulGNSData D S.Dv hsa hpos).toGNSData.rad_refl (Y.seq n)))
    (Q'.le_of_lt hε)

/-- The reverse map also intertwines the same diagonal action.  This is the
operator-level form of the round-trip bridge and again uses only the shared
representative sequence, not a spectral or norm argument. -/
theorem reverseComparison_intertwines
    {D : SmulGNSData} {S : DiagonalTransferSymbol D}
    {hsub : ∀ a b, D.toGNSData.veq (S.Dv (D.toGNSData.sub a b))
      (D.toGNSData.sub (S.Dv a) (S.Dv b))}
    {hsa : ∀ a b, D.toGNSData.B a (S.Dv b) ≈ D.toGNSData.B (S.Dv a) b}
    {hpos : ∀ a, (0 : Q') ≤ D.toGNSData.B a (S.Dv a)}
    {hupper : ∀ a, D.toGNSData.B a (S.Dv a) ≤ D.toGNSData.B a a}
    (certificate : ReverseComparisonCoercivity D S hsa hpos)
    (x : GNSCompletionSpace (oneStepSmulGNSData D S.Dv hsa hpos).toGNSData) :
    reverseComparison certificate
        ((oneStepSymbol D S hsub hsa hpos hupper).TqSymb x) =
      S.TqSymb (reverseComparison certificate x) := by
  refine Quotient.inductionOn x ?_
  intro Y
  apply Quotient.sound
  change CauchyNull D.toGNSData
    (reverseComparisonCauchy certificate
      ((oneStepSymbol D S hsub hsa hpos hupper).cDiagCauchy Y))
    (S.cDiagCauchy (reverseComparisonCauchy certificate Y))
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  change D.toGNSData.distSqQ (S.Dv (Y.seq n)) (S.Dv (Y.seq n)) ≤ ε
  exact Q'.le_trans' _ 0 ε
    (Q'.le_of_eqv (D.toGNSData.rad_refl (S.Dv (Y.seq n))))
    (Q'.le_of_lt hε)

end YMGap.Continuum.PositiveContractionReverseComparison

#print axioms YMGap.Continuum.PositiveContractionReverseComparison.reverseComparisonCauchy
#print axioms YMGap.Continuum.PositiveContractionReverseComparison.reverseComparisonCauchy_null
#print axioms YMGap.Continuum.PositiveContractionReverseComparison.reverseComparison
#print axioms YMGap.Continuum.PositiveContractionReverseComparison.reverseComparison_embed
#print axioms YMGap.Continuum.PositiveContractionReverseComparison.reverseComparison_comparison
#print axioms YMGap.Continuum.PositiveContractionReverseComparison.comparison_reverseComparison
#print axioms YMGap.Continuum.PositiveContractionReverseComparison.reverseComparison_intertwines
