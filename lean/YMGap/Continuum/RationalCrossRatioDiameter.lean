/-
# Exact rational projective-diameter certificates

This module isolates the finite, certificate-shaped part of a possible
Birkhoff--Hopf route for the compact-dual block-spin map.

A positive kernel has finite Hilbert-projective image diameter when all of
its matrix cross-ratios are uniformly bounded.  We record that condition
without logarithms or square roots:

    K(x,y) K(x',y') <= spread^2 K(x,y') K(x',y).

The square on `spread` is deliberate.  Classically it gives
`Delta <= 2 log spread`, so Birkhoff--Hopf gives the exact rational candidate

    q = (spread - 1) / (spread + 1).

What is proved here is the constructive rational algebra: strict positivity,
the cross-multiplied diameter certificate, restriction to smaller sectors,
and `0 <= q < 1`.  No Hilbert metric or contraction theorem is asserted.
The analytic Birkhoff--Hopf bridge remains a separate input.

This is also NOT the elementary heat-kernel transfer treated by
`BirkhoffContraction.lean`, whose exact ratio `w^3 -> 1` proves that its
one-step contraction is not uniform.  The intended consumer is an
unnormalized positive linear lift of the dual block-spin activity map on a
local, unbranched cone.  Neither linearity of that lift nor a
cutoff/volume-independent `spread` is assumed here.  In particular, applying
this certificate to a full finite-volume tensor-product cone would not by
itself prevent the diameter from growing with volume.

## Axiom gate

Exact `Q'` arithmetic and finite membership only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.RationalCrossRatioDiameter

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

universe u v

/-- A finite, log-free certificate for a bounded projective image.

Strict positivity is required on the selected rectangle.  Fusion zeros in a
larger physical kernel therefore force the caller to select an unbranched
positive sector (or to certify a positive primitive iterate) before this
structure can be inhabited. -/
structure FiniteCrossRatioDiameterCertificate
    {Source : Type u} {Target : Type v}
    (kernel : Source → Target → Q')
    (sources : List Source) (targets : List Target) : Type (max u v) where
  /-- Rational square-root majorant for all matrix cross-ratios. -/
  spread : Q'
  one_le_spread : (1 : Q') ≤ spread
  /-- Every selected matrix entry lies in the strict interior of the cone. -/
  strictlyPositive :
    ∀ source, source ∈ sources →
      ∀ target, target ∈ targets →
        (0 : Q') < kernel source target
  /-- The finite cross-ratio bound, in division-free exact arithmetic. -/
  crossRatioBound :
    ∀ first, first ∈ sources →
      ∀ second, second ∈ sources →
        ∀ left, left ∈ targets →
          ∀ right, right ∈ targets →
            kernel first left * kernel second right ≤
              (spread * spread) *
                (kernel first right * kernel second left)

namespace FiniteCrossRatioDiameterCertificate

/-- `spread` is strictly positive because it is at least one. -/
theorem spread_pos
    {Source : Type u} {Target : Type v}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets) :
    (0 : Q') < certificate.spread :=
  Q'.pos_of_lt_of_le (by decide) certificate.one_le_spread

/-- The denominator `spread + 1` of the rational candidate is positive. -/
theorem candidateDenominator_pos
    {Source : Type u} {Target : Type v}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets) :
    (0 : Q') < certificate.spread + 1 :=
  Q'.add_pos certificate.spread_pos (by decide)

/-- The exact rational rate associated with the squared cross-ratio bound.

This is only a candidate contraction rate until a constructive
Birkhoff--Hopf bridge identifies the relevant activity map and Hilbert
projective distance. -/
def candidateRate
    {Source : Type u} {Target : Type v}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets) : Q' :=
  Q'.divPos
    (certificate.spread + -(1 : Q'))
    (certificate.spread + 1)
    certificate.candidateDenominator_pos

/-- The exact rational candidate rate is nonnegative. -/
theorem candidateRate_nonnegative
    {Source : Type u} {Target : Type v}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets) :
    (0 : Q') ≤ certificate.candidateRate := by
  unfold candidateRate Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.sub_nonneg_of_le certificate.one_le_spread)
    (Q'.le_of_lt
      (Q'.recipPos_pos _ certificate.candidateDenominator_pos))

private theorem q_lt_of_lt_of_le {a b c : Q'}
    (hab : a < b) (hbc : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := hab
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := hbc
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
      < (b.num * (a.den : Int)) * (c.den : Int) := by
    have hscaled := Int.mul_lt_mul_of_pos_right e1
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have hreorder :
        (a.num * (b.den : Int)) * (c.den : Int) =
          (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hreorder] at hscaled
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
      ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have hscaled := Int.mul_le_mul_of_nonneg_right e2
      (by exact_mod_cast Nat.zero_le a.den :
        (0 : Int) ≤ (a.den : Int))
    have hleft :
        (b.num * (c.den : Int)) * (a.den : Int) =
          (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (c.den : Int) (a.den : Int)]
    have hright :
        (c.num * (b.den : Int)) * (a.den : Int) =
          (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (b.den : Int) (a.den : Int)]
    rwa [hleft, hright] at hscaled
  have schain :
      (a.num * (c.den : Int)) * (b.den : Int) <
        (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right schain
    (by exact_mod_cast Nat.zero_le b.den)

private theorem lt_add_of_pos_right (a b : Q')
    (hb : (0 : Q') < b) : a < a + b := by
  show a.num * ((a + b).den : Int) <
    (a + b).num * (a.den : Int)
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int) <
    (a.num * (b.den : Int) + b.num * (a.den : Int)) *
      (a.den : Int)
  have hcast :
      ((a.den * b.den : Nat) : Int) =
        (a.den : Int) * (b.den : Int) := by
    push_cast
    rfl
  rw [hcast]
  have hadenpos : (0 : Int) < (a.den : Int) := by
    exact_mod_cast a.den_pos
  have key :
      (0 : Int) < b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hadenpos) hadenpos
  have hexpand :
      (a.num * (b.den : Int) + b.num * (a.den : Int)) *
          (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) +
          b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have hfirst :
        a.num * (b.den : Int) * (a.den : Int) =
          a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc,
        Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [hfirst]
  rw [hexpand]
  omega

private theorem numerator_lt_denominator (spread : Q') :
    spread + -(1 : Q') < spread + 1 := by
  have hgrow :
      spread + -(1 : Q') <
        (spread + -(1 : Q')) + (2 : Q') :=
    lt_add_of_pos_right _ _ (by decide)
  have hrecombine :
      ((spread + -(1 : Q')) + (2 : Q')) ≈ spread + 1 := by
    refine Q'.eqv_trans _ (spread + (-(1 : Q') + 2)) _
      (Q'.add_assoc_eqv _ _ _) ?_
    exact Q'.add_eqv_congr_left spread _ _ (by decide)
  exact q_lt_of_lt_of_le hgrow (Q'.le_of_eqv hrecombine)

private theorem divPos_lt_one_of_lt
    (numerator denominator : Q')
    (hdenominator : (0 : Q') < denominator)
    (hlt : numerator < denominator) :
    Q'.divPos numerator denominator hdenominator < (1 : Q') := by
  unfold Q'.divPos
  have hreciprocal :
      (0 : Q') < Q'.recipPos denominator hdenominator :=
    Q'.recipPos_pos denominator hdenominator
  have hscaled :
      Q'.recipPos denominator hdenominator * numerator <
        Q'.recipPos denominator hdenominator * denominator :=
    Q'.mul_lt_mul_of_pos_left hreciprocal hlt
  have hleft :
      (numerator * Q'.recipPos denominator hdenominator) ≈
        Q'.recipPos denominator hdenominator * numerator :=
    Q'.mul_comm_eqv _ _
  have hright :
      (Q'.recipPos denominator hdenominator * denominator) ≈
        (1 : Q') :=
    Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv _ _)
      (Q'.mul_recipPos_eqv denominator hdenominator)
  exact q_lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv hleft) hscaled)
    (Q'.le_of_eqv hright)

/-- The exact rational candidate is strictly below one, independently of the
number of selected source or target coordinates. -/
theorem candidateRate_lt_one
    {Source : Type u} {Target : Type v}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets) :
    certificate.candidateRate < (1 : Q') :=
  divPos_lt_one_of_lt _ _ certificate.candidateDenominator_pos
    (numerator_lt_denominator certificate.spread)

/-- Restricting to smaller certified source and target lists cannot enlarge
the recorded cross-ratio spread. -/
def restrict
    {Source : Type u} {Target : Type v}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets)
    (smallerSources : List Source) (smallerTargets : List Target)
    (source_subset :
      ∀ source, source ∈ smallerSources → source ∈ sources)
    (target_subset :
      ∀ target, target ∈ smallerTargets → target ∈ targets) :
    FiniteCrossRatioDiameterCertificate
      kernel smallerSources smallerTargets where
  spread := certificate.spread
  one_le_spread := certificate.one_le_spread
  strictlyPositive := by
    intro source hsource target htarget
    exact certificate.strictlyPositive
      source (source_subset source hsource)
      target (target_subset target htarget)
  crossRatioBound := by
    intro first hfirst second hsecond left hleft right hright
    exact certificate.crossRatioBound
      first (source_subset first hfirst)
      second (source_subset second hsecond)
      left (target_subset left hleft)
      right (target_subset right hright)

theorem restrict_candidateRate_eqv
    {Source : Type u} {Target : Type v}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets)
    (smallerSources : List Source) (smallerTargets : List Target)
    (source_subset :
      ∀ source, source ∈ smallerSources → source ∈ sources)
    (target_subset :
      ∀ target, target ∈ smallerTargets → target ∈ targets) :
    (certificate.restrict
        smallerSources smallerTargets source_subset target_subset).candidateRate
      ≈ certificate.candidateRate :=
  Q'.eqv_refl _

end FiniteCrossRatioDiameterCertificate

/-! ## One common spread across cutoff and volume -/

/-- A uniform family of finite cross-ratio certificates.

The common `spread` is data shared by every regulator index.  This structure
does not claim that the index is a physical cutoff/volume pair; a physical
specialization must provide that identification and must use a local activity
cone rather than silently tensoring the full configuration cone. -/
structure UniformCrossRatioDiameterCertificate
    (Index : Type u)
    (Source Target : Index → Type v)
    (kernel : ∀ index, Source index → Target index → Q')
    (sources : ∀ index, List (Source index))
    (targets : ∀ index, List (Target index)) : Type (max u v) where
  spread : Q'
  one_le_spread : (1 : Q') ≤ spread
  strictlyPositive :
    ∀ index source, source ∈ sources index →
      ∀ target, target ∈ targets index →
        (0 : Q') < kernel index source target
  crossRatioBound :
    ∀ index first, first ∈ sources index →
      ∀ second, second ∈ sources index →
        ∀ left, left ∈ targets index →
          ∀ right, right ∈ targets index →
            kernel index first left * kernel index second right ≤
              (spread * spread) *
                (kernel index first right *
                  kernel index second left)

/-- Extract the finite certificate at one regulator index.  Its spread is
definitionally the common uniform spread, not merely propositionally equal to
it. -/
def UniformCrossRatioDiameterCertificate.atIndex
    {Index : Type u}
    {Source Target : Index → Type v}
    {kernel : ∀ index, Source index → Target index → Q'}
    {sources : ∀ index, List (Source index)}
    {targets : ∀ index, List (Target index)}
    (certificate :
      UniformCrossRatioDiameterCertificate
        Index Source Target kernel sources targets)
    (index : Index) :
    FiniteCrossRatioDiameterCertificate
      (kernel index) (sources index) (targets index) where
  spread := certificate.spread
  one_le_spread := certificate.one_le_spread
  strictlyPositive := certificate.strictlyPositive index
  crossRatioBound := certificate.crossRatioBound index

/-- Every regulator index has the same exact rational candidate rate. -/
theorem UniformCrossRatioDiameterCertificate.candidateRate_eqv
    {Index : Type u}
    {Source Target : Index → Type v}
    {kernel : ∀ index, Source index → Target index → Q'}
    {sources : ∀ index, List (Source index)}
    {targets : ∀ index, List (Target index)}
    (certificate :
      UniformCrossRatioDiameterCertificate
        Index Source Target kernel sources targets)
    (first second : Index) :
    (certificate.atIndex first).candidateRate ≈
      (certificate.atIndex second).candidateRate :=
  Q'.eqv_refl _

#print axioms FiniteCrossRatioDiameterCertificate.spread_pos
#print axioms FiniteCrossRatioDiameterCertificate.candidateDenominator_pos
#print axioms FiniteCrossRatioDiameterCertificate.candidateRate_nonnegative
#print axioms FiniteCrossRatioDiameterCertificate.candidateRate_lt_one
#print axioms FiniteCrossRatioDiameterCertificate.restrict
#print axioms FiniteCrossRatioDiameterCertificate.restrict_candidateRate_eqv
#print axioms UniformCrossRatioDiameterCertificate.atIndex
#print axioms UniformCrossRatioDiameterCertificate.candidateRate_eqv

end YMGap.Continuum.RationalCrossRatioDiameter
