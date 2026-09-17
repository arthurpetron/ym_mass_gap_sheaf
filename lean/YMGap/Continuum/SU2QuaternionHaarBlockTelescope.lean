/-
# A finite ordinary-Haar projection telescope

The terms are computed by successively integrating the original quaternion
coordinates. Each term has exactly zero conditional Haar projection in its
own coordinate. Their sum is coefficient-equivalent to the input minus its
full in-place projection.

Full projection is constant under supported Haar testing, not necessarily
in the raw coefficient relation: clearing exponents retains trailing-zero
monomial aliases. The centered endpoint below preserves that distinction.
This constructs ordinary-Haar test pieces only; it proves neither weighted
approximation nor a uniform bound for the interacting temporal energy.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Continuum.QPolyHaarPositiveSubstitution

namespace YMGap.Continuum.SU2QuaternionHaarBlockTelescope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QPolyHaarPositiveSubstitution (haar_one)

local infix:50 " ≈ " => Q'.eqv

/-- The first `count` integrations, retaining all original coordinate slots. -/
def partialProjection (count : Nat) (p : RatPoly) : RatPoly :=
  integrateQuaternionBlocks (List.range count) p

/-- A directly indexed polynomial, with no extraction from a membership proof. -/
def term (index : Nat) (p : RatPoly) : RatPoly :=
  fluctuation index (partialProjection index p)

/-- The finite sum of the explicit conditionally centered pieces. -/
def telescope (count : Nat) (p : RatPoly) : RatPoly :=
  polySum ((List.range count).map (fun index => term index p))

private theorem integrate_append (left right : List Nat) (p : RatPoly) :
    integrateQuaternionBlocks (left ++ right) p =
      integrateQuaternionBlocks right (integrateQuaternionBlocks left p) := by
  induction left generalizing p with
  | nil => rfl
  | cons i left ih => exact ih (project i p)

theorem partialProjection_succ (count : Nat) (p : RatPoly) :
    partialProjection (count + 1) p = project count (partialProjection count p) := by
  unfold partialProjection
  rw [List.range_succ, integrate_append]
  rfl

theorem partialProjection_supported {blocks : Nat} (count : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (partialProjection count p) :=
  integrateBlocks_supported (List.range count) hp

theorem term_supported {blocks : Nat} (index : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (term index p) :=
  fluctuation_supported index (partialProjection_supported index hp)

/-- Exact centering is coefficientwise, before any full Haar evaluation. -/
theorem project_term_zero (index : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (project index (term index p)) polyZero :=
  project_fluctuation_zero index (partialProjection index p)

private theorem sum_supported {blocks : Nat} : ∀ ps : List RatPoly,
    (∀ p, p ∈ ps → SupportedQuaternionBlocks blocks p) →
    SupportedQuaternionBlocks blocks (polySum ps)
  | [], _ => by intro t ht; cases ht
  | p :: ps, hp => supported_add (hp p List.mem_cons_self)
      (sum_supported ps (fun q hq => hp q (List.mem_cons_of_mem p hq)))

theorem telescope_supported {blocks : Nat} (count : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (telescope count p) := by
  apply sum_supported
  intro q hq
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  exact term_supported i hp

private theorem telescope_succ (count : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (telescope (count + 1) p)
      (polyAdd (telescope count p) (term count p)) := by
  unfold telescope
  rw [List.range_succ, List.map_append, List.map_singleton]
  exact (RatPolyCoeffEqv.polySum_append _ _).symm.trans
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _))

private theorem cancel (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd p (polyNeg p)) polyZero :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide) (fun _ => p)).trans
    (RatPolyCoeffEqv.zero_smul polyOne)

private theorem consecutive_difference (p q r : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyAdd p (polyNeg q)) (polyAdd q (polyNeg r)))
      (polyAdd p (polyNeg r)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
    (.add (.var 0) (.neg (.var 2))) (by decide)
    (fun | 0 => p | 1 => q | _ => r)

/-- The exact raw-polynomial endpoint is the in-place projection, not a
silently canonicalized constant. This holds even for an empty schedule. -/
theorem telescope_coeff (count : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (telescope count p)
      (polyAdd p (polyNeg (partialProjection count p))) := by
  induction count with
  | zero => exact (cancel p).symm
  | succ count ih =>
      rw [partialProjection_succ]
      exact (telescope_succ count p).trans
        ((ih.add (RatPolyCoeffEqv.refl _)).trans
          (consecutive_difference p (partialProjection count p)
            (project count (partialProjection count p))))

/-- Every full finite Haar mean is preserved, with the carrier bound explicit. -/
theorem partialProjection_mean (blocks count : Nat) (p : RatPoly) (hc : count ≤ blocks) :
    quaternionHaar blocks (partialProjection count p) ≈ quaternionHaar blocks p :=
  Q'.eqv_trans _ _ _ (quaternionHaar_eq_finiteProductHaar blocks _)
    (Q'.eqv_trans _ _ _
      (finiteProductHaar_integrateQuaternionBlocks blocks (List.range count) p
        (fun _i hi => Nat.lt_of_lt_of_le (List.mem_range.mp hi) hc))
      (Q'.eqv_symm (quaternionHaar_eq_finiteProductHaar blocks p)))

private def eraseMonomials (p : RatPoly) : RatPoly := p.map (fun t => ([], t.2))
private def coefficientSum (p : RatPoly) : Q' := qListSum (p.map Prod.snd)

private theorem erase_supported (blocks : Nat) (p : RatPoly) :
    SupportedQuaternionBlocks blocks (eraseMonomials p) := by
  intro t ht
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
  exact Nat.zero_le _

private theorem singleton_cap (c : Q') : RatPolyCoeffEqv [([], c)] (cap c) :=
  fun weight => ratWeightedSum_termwise_eqv weight
    ⟨rfl, Q'.eqv_symm (Q'.mul_one_eqv c), True.intro⟩

private theorem erase_coeff : ∀ p : RatPoly,
    RatPolyCoeffEqv (eraseMonomials p) (cap (coefficientSum p))
  | [] => (RatPolyCoeffEqv.zero_smul polyOne).symm
  | t :: rest => ((singleton_cap t.2).add (erase_coeff rest)).trans
      (cap_add t.2 (coefficientSum rest))

private theorem erase_prefix (blocks : Nat) : ∀ p : RatPoly,
    (∀ t, t ∈ p → ∀ coordinate, coordinate < 4 * blocks →
      exponentAt t.1 coordinate = 0) →
    QuaternionPrefixPolynomialEqv blocks p (eraseMonomials p)
  | [], _ => .nil
  | t :: rest, hz => by
      refine .cons ⟨Q'.eqv_refl _, ?_⟩
        (erase_prefix blocks rest (fun s hs => hz s (List.mem_cons_of_mem t hs)))
      intro coordinate hc
      simpa [exponentAt] using hz t List.mem_cons_self coordinate hc

private theorem full_zero (blocks : Nat) (p : RatPoly) :
    ∀ t, t ∈ partialProjection blocks p →
      ∀ coordinate, coordinate < 4 * blocks → exponentAt t.1 coordinate = 0 := by
  intro t ht coordinate hc
  have hb : coordinate / 4 < blocks := by omega
  have he : 4 * (coordinate / 4) + coordinate % 4 = coordinate := by omega
  have hz := integrateBlocks_zero blocks (List.range blocks) p t ht
    (coordinate / 4) hb (List.mem_range.mpr hb)
    (coordinate % 4) (Nat.mod_lt _ (by decide : 0 < 4))
  simpa only [he] using hz

private theorem cap_supported (blocks : Nat) (c : Q') :
    SupportedQuaternionBlocks blocks (cap c) := by
  intro t ht
  have he : t = ([], c * 1) := List.mem_singleton.mp ht
  subst t
  exact Nat.zero_le _

private theorem haar_cap (blocks : Nat) (c : Q') : quaternionHaar blocks (cap c) ≈ c :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks c polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (haar_one blocks)) (Q'.mul_one_eqv c))

/-- Full projection is the Haar mean after common padding, which is the
correct coefficient relation for raw trailing-zero monomial aliases. -/
theorem partialProjection_constant_padded (blocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    PaddedPolynomialCoeffEqv blocks (partialProjection blocks p)
      (cap (quaternionHaar blocks p)) := by
  have hf := partialProjection_supported blocks hp
  have he := erase_prefix blocks (partialProjection blocks p) (full_zero blocks p)
  have hc : quaternionHaar blocks (partialProjection blocks p) ≈
      coefficientSum (partialProjection blocks p) :=
    Q'.eqv_trans _ _ _
      (quaternionHaar_prefixPolynomialEqv blocks he hf (erase_supported blocks _))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (erase_coeff _)) (haar_cap blocks _))
  have hm : coefficientSum (partialProjection blocks p) ≈ quaternionHaar blocks p :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hc) (partialProjection_mean blocks blocks p (Nat.le_refl _))
  exact (PaddedPolynomialCoeffEqv.of_prefix he).trans
    ((PaddedPolynomialCoeffEqv.of_coeff (erase_coeff _)).trans
      (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.smul_coefficient hm polyOne)))

/-- The endpoint is constant against every supported insertion on this
same finite Haar carrier, including the zero-block carrier. -/
theorem partialProjection_constant (blocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedHaarEqv blocks (partialProjection blocks p) (cap (quaternionHaar blocks p)) :=
  SupportedHaarEqv.of_padded (partialProjection_constant_padded blocks p hp)
    (partialProjection_supported blocks hp) (cap_supported blocks _)

private theorem padded_neg {blocks : Nat} {p q : RatPoly}
    (h : PaddedPolynomialCoeffEqv blocks p q) :
    PaddedPolynomialCoeffEqv blocks (polyNeg p) (polyNeg q) := by
  unfold PaddedPolynomialCoeffEqv
  rw [reindexQuaternionPolynomial_neg, reindexQuaternionPolynomial_neg]
  exact RatPolyCoeffEqv.neg h

/-- A supported Haar-centered input is the sum of the explicit centered
pieces under every supported Haar test. No raw alias equality is asserted. -/
theorem centered_telescope (blocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (hz : quaternionHaar blocks p ≈ 0) :
    SupportedHaarEqv blocks (telescope blocks p) p := by
  have hzero : PaddedPolynomialCoeffEqv blocks (partialProjection blocks p) polyZero :=
    (partialProjection_constant_padded blocks p hp).trans
      (PaddedPolynomialCoeffEqv.of_coeff
        ((RatPolyCoeffEqv.smul_coefficient hz polyOne).trans (RatPolyCoeffEqv.zero_smul polyOne)))
  have hsum : PaddedPolynomialCoeffEqv blocks (telescope blocks p) p :=
    (PaddedPolynomialCoeffEqv.of_coeff (telescope_coeff blocks p)).trans
      (((PaddedPolynomialCoeffEqv.refl blocks p).add (padded_neg hzero)).trans
        (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.add_zero p)))
  exact SupportedHaarEqv.of_padded hsum (telescope_supported blocks hp) hp

#print axioms partialProjection_succ
#print axioms partialProjection_supported
#print axioms term_supported
#print axioms project_term_zero
#print axioms telescope_supported
#print axioms telescope_coeff
#print axioms partialProjection_mean
#print axioms partialProjection_constant_padded
#print axioms partialProjection_constant
#print axioms centered_telescope

end YMGap.Continuum.SU2QuaternionHaarBlockTelescope
