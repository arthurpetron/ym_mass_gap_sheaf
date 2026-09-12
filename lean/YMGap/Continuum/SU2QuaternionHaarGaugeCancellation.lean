/-
# Ordered gauge cancellation on the original polynomial Haar carrier

Vertex gauges telescope in a plaquette without commuting Hamilton factors.
Unit norm is used only through the existing arbitrary-insertion Haar ideal,
so surrounding face factors and shared links are never discarded.

The crossing-face identity substitutes C by D^-1 C B in A B C^-1 D^-1;
the two fixed-time factors then cancel. A separate substitution/geometry
theorem must realize these simultaneous shears on the physical slab.
-/

import YMGap.Continuum.BF4ExactSlabPlaquettePathGram

namespace YMGap.Continuum.SU2QuaternionHaarGaugeCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction

local infixl:70 " *q " => PolyQuaternion.mul
local prefix:80 "bar " => PolyQuaternion.conj

private theorem lift {blocks : Nat} {p q : PolyQuaternion} (h : PolyQuaternionCoeffEqv p q) :
    PolyQuaternionHaarCarrierEqv blocks p q := PolyQuaternionHaarCarrierEqv.of_coeff h

private theorem ref (blocks : Nat) (p : PolyQuaternion) : PolyQuaternionHaarCarrierEqv blocks p p :=
  PolyQuaternionHaarCarrierEqv.refl blocks p

/-- Character recurrence respects the full arbitrary-insertion Haar ideal. -/
theorem character_haar_congr {blocks : Nat} {p q : RatPoly}
    (h : HaarCarrierEqv blocks p q) : ∀ n : Nat,
    HaarCarrierEqv blocks (characterPolynomial p n) (characterPolynomial q n)
  | 0 => HaarCarrierEqv.refl blocks polyOne
  | 1 => HaarCarrierEqv.smul 2 h
  | n + 2 => HaarCarrierEqv.add
      (HaarCarrierEqv.mul (HaarCarrierEqv.smul 2 h) (character_haar_congr h (n + 1)))
      (HaarCarrierEqv.smul (-1) (character_haar_congr h n))

private theorem scalar_unit {blocks : Nat} {r : RatPoly}
    (h : HaarCarrierEqv blocks r polyOne) :
    PolyQuaternionHaarCarrierEqv blocks (scalarPolyQuaternion r) PolyQuaternion.one :=
  ⟨h, HaarCarrierEqv.refl blocks polyZero, HaarCarrierEqv.refl blocks polyZero,
    HaarCarrierEqv.refl blocks polyZero⟩

theorem haarUnit_mul_conj {blocks : Nat} {q : PolyQuaternion}
    (h : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    PolyQuaternionHaarCarrierEqv blocks (q *q bar q) PolyQuaternion.one :=
  (lift (PolyQuaternionCoeffEqv.mul_conj q)).trans (scalar_unit h)

theorem haarUnit_conj_mul {blocks : Nat} {q : PolyQuaternion}
    (h : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    PolyQuaternionHaarCarrierEqv blocks (bar q *q q) PolyQuaternion.one :=
  (lift (PolyQuaternionCoeffEqv.conj_mul q)).trans (scalar_unit h)

private theorem cancel_middle {blocks : Nat} {g : PolyQuaternion}
    (hg : HaarCarrierEqv blocks (polyQuaternionNorm g) polyOne) (p q : PolyQuaternion) :
    PolyQuaternionHaarCarrierEqv blocks ((p *q g) *q (bar g *q q)) (p *q q) := by
  refine (lift (PolyQuaternionCoeffEqv.mul_assoc p g (bar g *q q))).trans ?_
  apply (ref blocks p).mul
  exact (lift (PolyQuaternionCoeffEqv.mul_assoc g (bar g) q).symm).trans
    (((haarUnit_mul_conj hg).mul (ref blocks q)).trans (lift (PolyQuaternionCoeffEqv.one_mul q)))

private theorem cancel_right {blocks : Nat} {g : PolyQuaternion}
    (hg : HaarCarrierEqv blocks (polyQuaternionNorm g) polyOne) (p : PolyQuaternion) :
    PolyQuaternionHaarCarrierEqv blocks ((p *q g) *q bar g) p :=
  (lift (PolyQuaternionCoeffEqv.mul_assoc p g (bar g))).trans
    (((ref blocks p).mul (haarUnit_mul_conj hg)).trans (lift (PolyQuaternionCoeffEqv.mul_one p)))

private theorem double_conj (q : PolyQuaternion) : PolyQuaternionCoeffEqv (bar (bar q)) q := by
  have hn (p : RatPoly) : RatPolyCoeffEqv (polyNeg (polyNeg p)) p := by
    exact coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0)
      (by decide) (fun _ => p)
  exact ⟨RatPolyCoeffEqv.refl q.scalar, hn q.iPart, hn q.jPart, hn q.kPart⟩

/-- The ordered edge substitution g_start^-1 U g_end. -/
def gaugeLink (start u finish : PolyQuaternion) : PolyQuaternion := (bar start *q u) *q finish

/-- Reversing a gauge-transformed edge reverses its endpoints. -/
theorem gaugeLink_conj (start u finish : PolyQuaternion) :
    PolyQuaternionCoeffEqv (bar (gaugeLink start u finish)) (gaugeLink finish (bar u) start) :=
  (conjugate_product (bar start *q u) finish).trans
    (((PolyQuaternionCoeffEqv.refl (bar finish)).mul
      ((conjugate_product (bar start) u).trans
        ((PolyQuaternionCoeffEqv.refl (bar u)).mul (double_conj start)))).trans
      (PolyQuaternionCoeffEqv.mul_assoc (bar finish) (bar u) start).symm)

/-- Adjacent vertex gauges cancel under Haar, with every insertion retained. -/
theorem gaugeLink_compose {blocks : Nat} {middle : PolyQuaternion}
    (hm : HaarCarrierEqv blocks (polyQuaternionNorm middle) polyOne)
    (start u v finish : PolyQuaternion) :
    PolyQuaternionHaarCarrierEqv blocks
      (gaugeLink start u middle *q gaugeLink middle v finish)
      (gaugeLink start (u *q v) finish) := by
  refine (lift (PolyQuaternionCoeffEqv.mul_assoc
    (bar start *q u *q middle) (bar middle *q v) finish).symm).trans ?_
  exact (((cancel_middle hm (bar start *q u) v).mul (ref blocks finish)).trans
    (lift ((PolyQuaternionCoeffEqv.mul_assoc (bar start) u v).mul
      (PolyQuaternionCoeffEqv.refl finish))))

/-- A closed vertex conjugation preserves the actual scalar holonomy. -/
theorem gaugeLink_closed_scalar {blocks : Nat} {g : PolyQuaternion}
    (hg : HaarCarrierEqv blocks (polyQuaternionNorm g) polyOne) (p : PolyQuaternion) :
    HaarCarrierEqv blocks (gaugeLink g p g).scalar p.scalar :=
  HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternion_mul_scalar_cyclic (bar g *q p) g))
    ((lift (PolyQuaternionCoeffEqv.mul_assoc g (bar g) p).symm).trans
      (((haarUnit_mul_conj hg).mul (ref blocks p)).trans (lift (PolyQuaternionCoeffEqv.one_mul p)))).scalar

/-- The original ordered boundary, without a redundant initial unit. -/
def plaquetteWord (a b c d : PolyQuaternion) : PolyQuaternion := ((a *q b) *q bar c) *q bar d

/-- The four endpoint gauges telescope to the starting-vertex conjugation.
The third and fourth links retain the ORIGINAL inverse orientations. -/
theorem plaquette_gauge_word {blocks : Nat} (g0 g1 g2 g3 a b c d : PolyQuaternion)
    (h1 : HaarCarrierEqv blocks (polyQuaternionNorm g1) polyOne)
    (h2 : HaarCarrierEqv blocks (polyQuaternionNorm g2) polyOne)
    (h3 : HaarCarrierEqv blocks (polyQuaternionNorm g3) polyOne) :
    PolyQuaternionHaarCarrierEqv blocks
      (plaquetteWord (gaugeLink g0 a g1) (gaugeLink g1 b g2)
        (gaugeLink g3 c g2) (gaugeLink g0 d g3))
      (gaugeLink g0 (plaquetteWord a b c d) g0) := by
  have hab := gaugeLink_compose h1 g0 a b g2
  have hc := lift (gaugeLink_conj g3 c g2) (blocks := blocks)
  have hd := lift (gaugeLink_conj g0 d g3) (blocks := blocks)
  exact (((hab.mul hc).trans (gaugeLink_compose h2 g0 (a *q b) (bar c) g3)).mul hd).trans
    (gaugeLink_compose h3 g0 ((a *q b) *q bar c) (bar d) g0)

/-- All-spin character invariance of the ordered plaquette under vertex
gauges, in the SAME arbitrary-insertion Haar carrier. -/
theorem plaquette_gauge_character {blocks : Nat} (g0 g1 g2 g3 a b c d : PolyQuaternion)
    (h0 : HaarCarrierEqv blocks (polyQuaternionNorm g0) polyOne)
    (h1 : HaarCarrierEqv blocks (polyQuaternionNorm g1) polyOne)
    (h2 : HaarCarrierEqv blocks (polyQuaternionNorm g2) polyOne)
    (h3 : HaarCarrierEqv blocks (polyQuaternionNorm g3) polyOne) (spin : Nat) :
    HaarCarrierEqv blocks
      (characterPolynomial (plaquetteWord (gaugeLink g0 a g1) (gaugeLink g1 b g2)
        (gaugeLink g3 c g2) (gaugeLink g0 d g3)).scalar spin)
      (characterPolynomial (plaquetteWord a b c d).scalar spin) :=
  character_haar_congr (HaarCarrierEqv.trans
    (plaquette_gauge_word g0 g1 g2 g3 a b c d h1 h2 h3).scalar
    (gaugeLink_closed_scalar h0 (plaquetteWord a b c d))) spin

/-- The crossing-face temporal shear cancels BOTH fixed links. No link
independence is assumed; unit norms hold under every spectator insertion. -/
theorem crossing_temporal_shear {blocks : Nat} (a b c d : PolyQuaternion)
    (hb : HaarCarrierEqv blocks (polyQuaternionNorm b) polyOne)
    (hd : HaarCarrierEqv blocks (polyQuaternionNorm d) polyOne) :
    PolyQuaternionHaarCarrierEqv blocks (plaquetteWord a b (gaugeLink d c b) d) (a *q bar c) := by
  refine (((ref blocks (a *q b)).mul (lift (gaugeLink_conj d c b))).mul (ref blocks (bar d))).trans ?_
  refine ((lift (PolyQuaternionCoeffEqv.mul_assoc (a *q b) (bar b *q bar c) d).symm).mul
    (ref blocks (bar d))).trans ?_
  have hc := ((cancel_middle hb a (bar c)).mul (ref blocks d)).mul (ref blocks (bar d))
  exact hc.trans (cancel_right hd (a *q bar c))

end YMGap.Continuum.SU2QuaternionHaarGaugeCancellation

#print axioms YMGap.Continuum.SU2QuaternionHaarGaugeCancellation.character_haar_congr
#print axioms YMGap.Continuum.SU2QuaternionHaarGaugeCancellation.haarUnit_mul_conj
#print axioms YMGap.Continuum.SU2QuaternionHaarGaugeCancellation.haarUnit_conj_mul
#print axioms YMGap.Continuum.SU2QuaternionHaarGaugeCancellation.gaugeLink
#print axioms YMGap.Continuum.SU2QuaternionHaarGaugeCancellation.gaugeLink_conj
#print axioms YMGap.Continuum.SU2QuaternionHaarGaugeCancellation.gaugeLink_compose
#print axioms YMGap.Continuum.SU2QuaternionHaarGaugeCancellation.gaugeLink_closed_scalar
#print axioms YMGap.Continuum.SU2QuaternionHaarGaugeCancellation.plaquetteWord
#print axioms YMGap.Continuum.SU2QuaternionHaarGaugeCancellation.plaquette_gauge_word
#print axioms YMGap.Continuum.SU2QuaternionHaarGaugeCancellation.plaquette_gauge_character
#print axioms YMGap.Continuum.SU2QuaternionHaarGaugeCancellation.crossing_temporal_shear
