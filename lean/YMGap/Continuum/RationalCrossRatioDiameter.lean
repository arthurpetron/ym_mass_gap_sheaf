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

/-- A finite, log-free certificate for a bounded projective image.

Strict positivity is required on the selected rectangle.  Fusion zeros in a
larger physical kernel therefore force the caller to select an unbranched
positive sector (or to certify a positive primitive iterate) before this
structure can be inhabited. -/
structure FiniteCrossRatioDiameterCertificate
    {Source : Type} {Target : Type}
    (kernel : Source → Target → Q')
    (sources : List Source) (targets : List Target) : Type where
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
    {Source : Type} {Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets) :
    (0 : Q') < certificate.spread :=
  Q'.pos_of_lt_of_le (by decide) certificate.one_le_spread

/-- The denominator `spread + 1` of the rational candidate is positive. -/
theorem candidateDenominator_pos
    {Source : Type} {Target : Type}
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
    {Source : Type} {Target : Type}
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
    {Source : Type} {Target : Type}
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
    {Source : Type} {Target : Type}
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
    {Source : Type} {Target : Type}
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
    {Source : Type} {Target : Type}
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

/-! ## Monotone enlargement of a recorded spread -/

/-- A valid cross-ratio certificate remains valid after increasing its
recorded spread.  This is what turns a regulator-dependent active-face
product into one common cutoff/volume-independent diameter bound. -/
def widen
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets)
    (largerSpread : Q')
    (hspread : certificate.spread ≤ largerSpread) :
    FiniteCrossRatioDiameterCertificate kernel sources targets where
  spread := largerSpread
  one_le_spread :=
    Q'.le_trans' _ _ _
      certificate.one_le_spread hspread
  strictlyPositive := certificate.strictlyPositive
  crossRatioBound := by
    intro first hfirst second hsecond left hleft right hright
    let reverseProduct :=
      kernel first right * kernel second left
    have hlargerNonnegative : (0 : Q') ≤ largerSpread :=
      Q'.le_trans' _ _ _
        Q'.zero_le_one
        (Q'.le_trans' _ _ _
          certificate.one_le_spread hspread)
    have hcertificateNonnegative :
        (0 : Q') ≤ certificate.spread :=
      Q'.le_of_lt certificate.spread_pos
    have hsquare :
        certificate.spread * certificate.spread ≤
          largerSpread * largerSpread :=
      Q'.mul_le_mul_of_nonneg hspread hspread
        hlargerNonnegative hcertificateNonnegative
    have hreverseNonnegative : (0 : Q') ≤ reverseProduct :=
      Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (certificate.strictlyPositive
            first hfirst right hright))
        (Q'.le_of_lt
          (certificate.strictlyPositive
            second hsecond left hleft))
    exact Q'.le_trans' _ _ _
      (certificate.crossRatioBound
        first hfirst second hsecond left hleft right hright)
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        hsquare hreverseNonnegative)

theorem widen_spread_eq
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets)
    (largerSpread : Q')
    (hspread : certificate.spread ≤ largerSpread) :
    (certificate.widen largerSpread hspread).spread = largerSpread :=
  rfl

private theorem mul_swap4_local (a b c d : Q') :
    ((a * b) * (c * d)) ≈ ((a * c) * (b * d)) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    ?_ (Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d)))
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv b c d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d
      (Q'.mul_comm_eqv b c)) ?_
  exact Q'.mul_assoc_eqv c b d

/-! ## Projective invariance under row normalization -/

/-- Multiply each kernel row by an exact rational scale. -/
def rowRescaledKernel
    {Source Target : Type}
    (rowScale : Source → Q')
    (kernel : Source → Target → Q')
    (source : Source) (target : Target) : Q' :=
  rowScale source * kernel source target

/-- Positive row rescaling preserves the same cross-ratio certificate.

This is the exact algebra needed to pass from unnormalized block weights to
row-normalized conditional probabilities: every row denominator cancels from
all matrix cross-ratios. -/
def rowRescale
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets)
    (rowScale : Source → Q')
    (rowScale_pos :
      ∀ source, source ∈ sources →
        (0 : Q') < rowScale source) :
    FiniteCrossRatioDiameterCertificate
      (rowRescaledKernel rowScale kernel) sources targets where
  spread := certificate.spread
  one_le_spread := certificate.one_le_spread
  strictlyPositive := by
    intro source hsource target htarget
    exact Q'.mul_pos
      (rowScale_pos source hsource)
      (certificate.strictlyPositive source hsource target htarget)
  crossRatioBound := by
    intro first hfirst second hsecond left hleft right hright
    let rowFactor := rowScale first * rowScale second
    have hrowFactor : (0 : Q') ≤ rowFactor :=
      Q'.mul_nonneg _ _
        (Q'.le_of_lt (rowScale_pos first hfirst))
        (Q'.le_of_lt (rowScale_pos second hsecond))
    have hcross :=
      certificate.crossRatioBound
        first hfirst second hsecond left hleft right hright
    have hscaled :
        rowFactor *
            (kernel first left * kernel second right) ≤
          rowFactor *
            ((certificate.spread * certificate.spread) *
              (kernel first right * kernel second left)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hcross hrowFactor
    have hleftReindex :
        rowRescaledKernel rowScale kernel first left *
            rowRescaledKernel rowScale kernel second right ≈
          rowFactor *
            (kernel first left * kernel second right) := by
      unfold rowRescaledKernel rowFactor
      exact mul_swap4_local _ _ _ _
    have hscaledRightReindex :
        rowFactor *
            ((certificate.spread * certificate.spread) *
              (kernel first right * kernel second left)) ≈
          (certificate.spread * certificate.spread) *
            (rowFactor *
              (kernel first right * kernel second left)) := by
      calc
        rowFactor *
              ((certificate.spread * certificate.spread) *
                (kernel first right * kernel second left)) ≈
            (rowFactor *
                (certificate.spread * certificate.spread)) *
              (kernel first right * kernel second left) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
        _ ≈ ((certificate.spread * certificate.spread) *
                rowFactor) *
              (kernel first right * kernel second left) :=
          Q'.mul_eqv_congr_right _ _
            (kernel first right * kernel second left)
            (Q'.mul_comm_eqv _ _)
        _ ≈ (certificate.spread * certificate.spread) *
              (rowFactor *
                (kernel first right * kernel second left)) :=
          Q'.mul_assoc_eqv _ _ _
    have hrightReindex :
        (certificate.spread * certificate.spread) *
            (rowFactor *
              (kernel first right * kernel second left)) ≈
          (certificate.spread * certificate.spread) *
            (rowRescaledKernel rowScale kernel first right *
              rowRescaledKernel rowScale kernel second left) := by
      apply Q'.mul_eqv_congr_left
      exact Q'.eqv_symm (mul_swap4_local _ _ _ _)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hleftReindex)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv
          (Q'.eqv_trans _ _ _
            hscaledRightReindex hrightReindex)))

theorem rowRescale_candidateRate_eqv
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets)
    (rowScale : Source → Q')
    (rowScale_pos :
      ∀ source, source ∈ sources →
        (0 : Q') < rowScale source) :
    (certificate.rowRescale rowScale rowScale_pos).candidateRate ≈
      certificate.candidateRate :=
  Q'.eqv_refl _

/-! ## Projective invariance under target-column scaling -/

/-- Multiply each kernel column by an exact rational scale. -/
def columnRescaledKernel
    {Source Target : Type}
    (columnScale : Target → Q')
    (kernel : Source → Target → Q')
    (source : Source) (target : Target) : Q' :=
  kernel source target * columnScale target

/-- Positive target-column rescaling preserves the same cross-ratio
certificate.  This is the exact cancellation used when a globally glued link
multiplicity depends only on the retained coarse target. -/
def columnRescale
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets)
    (columnScale : Target → Q')
    (columnScale_pos :
      ∀ target, target ∈ targets →
        (0 : Q') < columnScale target) :
    FiniteCrossRatioDiameterCertificate
      (columnRescaledKernel columnScale kernel) sources targets where
  spread := certificate.spread
  one_le_spread := certificate.one_le_spread
  strictlyPositive := by
    intro source hsource target htarget
    exact Q'.mul_pos
      (certificate.strictlyPositive source hsource target htarget)
      (columnScale_pos target htarget)
  crossRatioBound := by
    intro first hfirst second hsecond left hleft right hright
    let columnFactor := columnScale left * columnScale right
    have hcolumnFactor : (0 : Q') ≤ columnFactor :=
      Q'.mul_nonneg _ _
        (Q'.le_of_lt (columnScale_pos left hleft))
        (Q'.le_of_lt (columnScale_pos right hright))
    have hcross :=
      certificate.crossRatioBound
        first hfirst second hsecond left hleft right hright
    have hscaled :
        (kernel first left * kernel second right) * columnFactor ≤
          ((certificate.spread * certificate.spread) *
            (kernel first right * kernel second left)) *
              columnFactor :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hcross hcolumnFactor
    have hleftReindex :
        columnRescaledKernel columnScale kernel first left *
            columnRescaledKernel columnScale kernel second right ≈
          (kernel first left * kernel second right) *
            columnFactor := by
      unfold columnRescaledKernel columnFactor
      exact mul_swap4_local _ _ _ _
    have hrightReindex :
        ((certificate.spread * certificate.spread) *
            (kernel first right * kernel second left)) *
              columnFactor ≈
          (certificate.spread * certificate.spread) *
            (columnRescaledKernel columnScale kernel first right *
              columnRescaledKernel columnScale kernel second left) := by
      refine Q'.eqv_trans _
        ((certificate.spread * certificate.spread) *
          ((kernel first right * kernel second left) *
            columnFactor)) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      apply Q'.mul_eqv_congr_left
      unfold columnRescaledKernel columnFactor
      calc
        (kernel first right * kernel second left) *
              (columnScale left * columnScale right) ≈
            (kernel first right * kernel second left) *
              (columnScale right * columnScale left) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_comm_eqv _ _)
        _ ≈ (kernel first right * columnScale right) *
              (kernel second left * columnScale left) :=
          Q'.eqv_symm (mul_swap4_local _ _ _ _)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hleftReindex)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv hrightReindex))

theorem columnRescale_candidateRate_eqv
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets)
    (columnScale : Target → Q')
    (columnScale_pos :
      ∀ target, target ∈ targets →
        (0 : Q') < columnScale target) :
    (certificate.columnRescale
        columnScale columnScale_pos).candidateRate ≈
      certificate.candidateRate :=
  Q'.eqv_refl _

/-! ## Projective diameter of pointwise products -/

/-- Multiply two positive kernels coordinatewise.  This is the algebraic
operation underlying a factorized local face activity. -/
def pointwiseProductKernel
    {Source Target : Type}
    (left right : Source → Target → Q')
    (source : Source) (target : Target) : Q' :=
  left source target * right source target

/-- Cross-ratio spreads multiply under pointwise products.

Consequently, a factor which is independent of the source has spread one
and contributes nothing to the accumulated projective diameter.  Repeated
use localizes a factorized slab certificate to its genuinely active face
fibers. -/
def pointwiseMul
    {Source Target : Type}
    {leftKernel rightKernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (leftCertificate :
      FiniteCrossRatioDiameterCertificate
        leftKernel sources targets)
    (rightCertificate :
      FiniteCrossRatioDiameterCertificate
        rightKernel sources targets) :
    FiniteCrossRatioDiameterCertificate
      (pointwiseProductKernel leftKernel rightKernel)
      sources targets where
  spread := leftCertificate.spread * rightCertificate.spread
  one_le_spread := by
    have hmul := Q'.mul_le_mul_of_nonneg
      leftCertificate.one_le_spread
      rightCertificate.one_le_spread
      (Q'.le_of_lt leftCertificate.spread_pos)
      Q'.zero_le_one
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv 1)) hmul
  strictlyPositive := by
    intro source hsource target htarget
    exact Q'.mul_pos
      (leftCertificate.strictlyPositive source hsource target htarget)
      (rightCertificate.strictlyPositive source hsource target htarget)
  crossRatioBound := by
    intro first hfirst second hsecond left hleft right hright
    let leftForward :=
      leftKernel first left * leftKernel second right
    let leftReverse :=
      leftKernel first right * leftKernel second left
    let rightForward :=
      rightKernel first left * rightKernel second right
    let rightReverse :=
      rightKernel first right * rightKernel second left
    let leftSpreadSquare :=
      leftCertificate.spread * leftCertificate.spread
    let rightSpreadSquare :=
      rightCertificate.spread * rightCertificate.spread
    have hleftCross :=
      leftCertificate.crossRatioBound
        first hfirst second hsecond left hleft right hright
    have hrightCross :=
      rightCertificate.crossRatioBound
        first hfirst second hsecond left hleft right hright
    have hleftUpperNonnegative :
        (0 : Q') ≤ leftSpreadSquare * leftReverse :=
      Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.le_of_lt leftCertificate.spread_pos)
          (Q'.le_of_lt leftCertificate.spread_pos))
        (Q'.mul_nonneg _ _
          (Q'.le_of_lt
            (leftCertificate.strictlyPositive
              first hfirst right hright))
          (Q'.le_of_lt
            (leftCertificate.strictlyPositive
              second hsecond left hleft)))
    have hrightForwardNonnegative :
        (0 : Q') ≤ rightForward :=
      Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (rightCertificate.strictlyPositive
            first hfirst left hleft))
        (Q'.le_of_lt
          (rightCertificate.strictlyPositive
            second hsecond right hright))
    have hproduct :
        leftForward * rightForward ≤
          (leftSpreadSquare * leftReverse) *
            (rightSpreadSquare * rightReverse) :=
      Q'.mul_le_mul_of_nonneg hleftCross hrightCross
        hleftUpperNonnegative hrightForwardNonnegative
    have hleftReindex :
        pointwiseProductKernel leftKernel rightKernel first left *
            pointwiseProductKernel leftKernel rightKernel second right ≈
          leftForward * rightForward := by
      unfold pointwiseProductKernel leftForward rightForward
      exact mul_swap4_local _ _ _ _
    have hspreadReindex :
        leftSpreadSquare * rightSpreadSquare ≈
          (leftCertificate.spread * rightCertificate.spread) *
            (leftCertificate.spread * rightCertificate.spread) := by
      unfold leftSpreadSquare rightSpreadSquare
      exact mul_swap4_local _ _ _ _
    have hreverseReindex :
        leftReverse * rightReverse ≈
          pointwiseProductKernel leftKernel rightKernel first right *
            pointwiseProductKernel leftKernel rightKernel second left := by
      unfold leftReverse rightReverse pointwiseProductKernel
      exact mul_swap4_local _ _ _ _
    have hrightReindex :
        (leftSpreadSquare * leftReverse) *
              (rightSpreadSquare * rightReverse) ≈
          ((leftCertificate.spread * rightCertificate.spread) *
              (leftCertificate.spread * rightCertificate.spread)) *
            (pointwiseProductKernel leftKernel rightKernel first right *
              pointwiseProductKernel leftKernel rightKernel second left) := by
      refine Q'.eqv_trans _
        ((leftSpreadSquare * rightSpreadSquare) *
          (leftReverse * rightReverse)) _
        (mul_swap4_local _ _ _ _) ?_
      refine Q'.eqv_trans _
        (((leftCertificate.spread * rightCertificate.spread) *
            (leftCertificate.spread * rightCertificate.spread)) *
          (leftReverse * rightReverse)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          hspreadReindex
      · exact Q'.mul_eqv_congr_left _ _ _
          hreverseReindex
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hleftReindex)
      (Q'.le_trans' _ _ _ hproduct
        (Q'.le_of_eqv hrightReindex))

theorem pointwiseMul_spread_eq
    {Source Target : Type}
    {leftKernel rightKernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (leftCertificate :
      FiniteCrossRatioDiameterCertificate
        leftKernel sources targets)
    (rightCertificate :
      FiniteCrossRatioDiameterCertificate
        rightKernel sources targets) :
    (leftCertificate.pointwiseMul rightCertificate).spread =
      leftCertificate.spread * rightCertificate.spread :=
  rfl

/-- A strictly positive source-independent factor is a projective gauge and
has the exact unit-spread certificate. -/
def sourceIndependentCertificate
    {Source Target : Type}
    (column : Target → Q')
    (sources : List Source) (targets : List Target)
    (column_pos :
      ∀ target, target ∈ targets → (0 : Q') < column target) :
    FiniteCrossRatioDiameterCertificate
      (fun _ target => column target) sources targets where
  spread := 1
  one_le_spread := Q'.le_refl' 1
  strictlyPositive := by
    intro _ _ target htarget
    exact column_pos target htarget
  crossRatioBound := by
    intro _ _ _ _ left hleft right hright
    have hcomm :
        column left * column right ≈
          column right * column left :=
      Q'.mul_comm_eqv _ _
    have hunit :
        ((1 : Q') * 1) * (column right * column left) ≈
          column right * column left := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right
          ((1 : Q') * 1) 1 (column right * column left)
          (Q'.mul_one_eqv 1))
        (Q'.one_mul_eqv (column right * column left))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hcomm)
      (Q'.le_of_eqv (Q'.eqv_symm hunit))

theorem sourceIndependentCertificate_candidateRate_eqv_zero
    {Source Target : Type}
    (column : Target → Q')
    (sources : List Source) (targets : List Target)
    (column_pos :
      ∀ target, target ∈ targets → (0 : Q') < column target) :
    (sourceIndependentCertificate
      column sources targets column_pos).candidateRate ≈ 0 := by
  unfold sourceIndependentCertificate candidateRate
  exact Q'.zero_mul_eqv _

/-! ## Finite products of local factors -/

/-- The pointwise product of a finite list of local kernels.  The empty
product is the positive unit kernel. -/
def factorizedKernel
    {Factor Source Target : Type}
    (localKernel : Factor → Source → Target → Q') :
    List Factor → Source → Target → Q'
  | [], _, _ => 1
  | factor :: rest, source, target =>
      localKernel factor source target *
        factorizedKernel localKernel rest source target

/-- Assemble local exact certificates into a certificate for their finite
pointwise product.  Its spread is the product of the local spreads, with no
factor involving the ambient source or target dimensions. -/
def factorizedCertificate
    {Factor Source Target : Type}
    (localKernel : Factor → Source → Target → Q')
    (sources : List Source) (targets : List Target) :
    ∀ factors : List Factor,
      (∀ factor, factor ∈ factors →
        FiniteCrossRatioDiameterCertificate
          (localKernel factor) sources targets) →
      FiniteCrossRatioDiameterCertificate
        (factorizedKernel localKernel factors) sources targets
  | [], _ =>
      sourceIndependentCertificate
        (fun _ => 1) sources targets
        (fun _ _ =>
          show (0 : Q') < (1 : Q') from by decide)
  | factor :: rest, localCertificate => by
      let headCertificate :=
        localCertificate factor List.mem_cons_self
      let tailCertificate :=
        factorizedCertificate localKernel sources targets rest
          (fun item hitem =>
            localCertificate item
              (List.mem_cons_of_mem factor hitem))
      exact headCertificate.pointwiseMul tailCertificate

/-- Exact ordered product of the recorded local spreads. -/
def factorSpreadProduct {Factor : Type}
    (recordedSpread : Factor → Q') : List Factor → Q'
  | [] => 1
  | factor :: rest =>
      recordedSpread factor *
        factorSpreadProduct recordedSpread rest

/-- Left-associated-by-recursion power matching the exact representation
used by `factorSpreadProduct` for a constant local spread. -/
def spreadPower (spread : Q') : Nat → Q'
  | 0 => 1
  | n + 1 => spread * spreadPower spread n

theorem factorSpreadProduct_const_eq_spreadPower
    {Factor : Type} (spread : Q') :
    ∀ factors : List Factor,
      factorSpreadProduct (fun _ => spread) factors =
        spreadPower spread factors.length
  | [] => rfl
  | _ :: tail => by
      change spread *
          factorSpreadProduct (fun _ => spread) tail =
        spread * spreadPower spread tail.length
      rw [factorSpreadProduct_const_eq_spreadPower spread tail]

theorem one_le_spreadPower
    (spread : Q') (hone : (1 : Q') ≤ spread) :
    ∀ n, (1 : Q') ≤ spreadPower spread n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      have hmul := Q'.mul_le_mul_of_nonneg
        hone (one_le_spreadPower spread hone n)
        (Q'.le_trans' _ _ _ Q'.zero_le_one hone)
        Q'.zero_le_one
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.one_mul_eqv 1)) hmul

theorem spreadPower_nonnegative
    (spread : Q') (hone : (1 : Q') ≤ spread)
    (n : Nat) :
    (0 : Q') ≤ spreadPower spread n :=
  Q'.le_trans' _ _ _
    Q'.zero_le_one
    (one_le_spreadPower spread hone n)

theorem spreadPower_le_succ
    (spread : Q') (hone : (1 : Q') ≤ spread)
    (n : Nat) :
    spreadPower spread n ≤ spreadPower spread (n + 1) := by
  change spreadPower spread n ≤
    spread * spreadPower spread n
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.one_mul_eqv (spreadPower spread n))))
    (Q'.mul_le_mul_of_nonneg_right
      1 spread (spreadPower spread n)
      hone (spreadPower_nonnegative spread hone n))

theorem spreadPower_mono
    (spread : Q') (hone : (1 : Q') ≤ spread)
    {smaller larger : Nat} (hsize : smaller ≤ larger) :
    spreadPower spread smaller ≤ spreadPower spread larger := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hsize
  clear hsize
  induction extra with
  | zero =>
      simp only [Nat.add_zero]
      exact Q'.le_refl' _
  | succ extra ih =>
      exact Q'.le_trans' _ _ _
        ih
        (by
          simpa only [Nat.add_assoc] using
            spreadPower_le_succ spread hone (smaller + extra))

/-- The assembled certificate's spread is semantically the ordered product
of any pointwise-equivalent recorded local spreads. -/
theorem factorizedCertificate_spread_eqv_product
    {Factor Source Target : Type}
    (localKernel : Factor → Source → Target → Q')
    (sources : List Source) (targets : List Target)
    (recordedSpread : Factor → Q') :
    ∀ (factors : List Factor)
      (localCertificate :
        ∀ factor, factor ∈ factors →
          FiniteCrossRatioDiameterCertificate
            (localKernel factor) sources targets),
      (∀ factor hfactor,
        (localCertificate factor hfactor).spread ≈
          recordedSpread factor) →
      (factorizedCertificate localKernel sources targets
          factors localCertificate).spread ≈
        factorSpreadProduct recordedSpread factors
  | [], _, _ => Q'.eqv_refl 1
  | head :: tail, localCertificate, hspread => by
      change
        (localCertificate head List.mem_cons_self).spread *
              (factorizedCertificate localKernel sources targets tail
                (fun item hitem =>
                  localCertificate item
                    (List.mem_cons_of_mem head hitem))).spread ≈
          recordedSpread head *
            factorSpreadProduct recordedSpread tail
      refine Q'.eqv_trans _
        (recordedSpread head *
          (factorizedCertificate localKernel sources targets tail
            (fun item hitem =>
              localCertificate item
                (List.mem_cons_of_mem head hitem))).spread) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (hspread head List.mem_cons_self)
      · apply Q'.mul_eqv_congr_left
        exact factorizedCertificate_spread_eqv_product
          localKernel sources targets recordedSpread tail
          (fun item hitem =>
            localCertificate item
              (List.mem_cons_of_mem head hitem))
          (fun item hitem =>
            hspread item
              (List.mem_cons_of_mem head hitem))

/-- Unit-spread inactive factors disappear exactly from the spread ledger. -/
theorem factorSpreadProduct_mask_eqv_filter
    {Factor : Type}
    (active : Factor → Bool)
    (recordedSpread : Factor → Q') :
    ∀ factors : List Factor,
      factorSpreadProduct
          (fun factor =>
            if active factor then recordedSpread factor else 1)
          factors ≈
        factorSpreadProduct recordedSpread
          (factors.filter active)
  | [] => Q'.eqv_refl 1
  | head :: tail => by
      cases hactive : active head with
      | false =>
          simp only [factorSpreadProduct, List.filter, hactive,
            Bool.false_eq_true, ↓reduceIte]
          exact Q'.eqv_trans _ _ _
            (Q'.one_mul_eqv _)
            (factorSpreadProduct_mask_eqv_filter
              active recordedSpread tail)
      | true =>
          simp only [factorSpreadProduct, List.filter, hactive,
            ↓reduceIte]
          apply Q'.mul_eqv_congr_left
          exact factorSpreadProduct_mask_eqv_filter
            active recordedSpread tail

/-- Complete active-factor pruning theorem.  If every inactive local factor
has recorded spread one, the global certificate spread is the product over
the active filter only. -/
theorem factorizedCertificate_spread_eqv_activeProduct
    {Factor Source Target : Type}
    (localKernel : Factor → Source → Target → Q')
    (sources : List Source) (targets : List Target)
    (active : Factor → Bool)
    (recordedSpread : Factor → Q')
    (factors : List Factor)
    (localCertificate :
      ∀ factor, factor ∈ factors →
        FiniteCrossRatioDiameterCertificate
          (localKernel factor) sources targets)
    (hspread :
      ∀ factor hfactor,
        (localCertificate factor hfactor).spread ≈
          if active factor then recordedSpread factor else 1) :
    (factorizedCertificate localKernel sources targets
        factors localCertificate).spread ≈
      factorSpreadProduct recordedSpread
        (factors.filter active) := by
  exact Q'.eqv_trans _ _ _
    (factorizedCertificate_spread_eqv_product
      localKernel sources targets
      (fun factor =>
        if active factor then recordedSpread factor else 1)
      factors localCertificate hspread)
    (factorSpreadProduct_mask_eqv_filter
      active recordedSpread factors)

theorem factorizedCertificate_nil_spread
    {Factor Source Target : Type}
    (localKernel : Factor → Source → Target → Q')
    (sources : List Source) (targets : List Target)
    (localCertificate :
      ∀ factor, factor ∈ ([] : List Factor) →
        FiniteCrossRatioDiameterCertificate
          (localKernel factor) sources targets) :
    (factorizedCertificate localKernel sources targets []
      localCertificate).spread = 1 :=
  rfl

theorem factorizedCertificate_cons_spread
    {Factor Source Target : Type}
    (localKernel : Factor → Source → Target → Q')
    (sources : List Source) (targets : List Target)
    (factor : Factor) (rest : List Factor)
    (localCertificate :
      ∀ item, item ∈ factor :: rest →
        FiniteCrossRatioDiameterCertificate
          (localKernel item) sources targets) :
    (factorizedCertificate localKernel sources targets
        (factor :: rest) localCertificate).spread =
      (localCertificate factor List.mem_cons_self).spread *
        (factorizedCertificate localKernel sources targets rest
          (fun item hitem =>
            localCertificate item
              (List.mem_cons_of_mem factor hitem))).spread :=
  rfl

/-! ## The certified finite image has the recorded log-free diameter -/

/-- Apply a finite kernel linearly to an exact rational activity. -/
def finiteKernelAction
    {Source : Type} {Target : Type}
    (kernel : Source → Target → Q')
    (sources : List Source)
    (activity : Source → Q')
    (target : Target) : Q' :=
  listQSum
    (fun source => kernel source target * activity source)
    sources

/-- The division-free form of a Hilbert-projective spread bound between two
positive rays.  When all coordinates are positive, this says their Hilbert
distance is at most `2 log spread`, without introducing a logarithm into the
exact certificate layer. -/
def ProjectiveSpreadBound
    {Target : Type}
    (spread : Q') (targets : List Target)
    (first second : Target → Q') : Prop :=
  ∀ left, left ∈ targets →
    ∀ right, right ∈ targets →
      first left * second right ≤
        (spread * spread) * (first right * second left)

/-- A nonzero point of the closed positive activity cone, with its positive
coordinate retained as Type-level witness data. -/
structure NonzeroNonnegativeActivity
    {Source : Type}
    (sources : List Source) (activity : Source → Q') : Type where
  nonnegative :
    ∀ source, source ∈ sources →
      (0 : Q') ≤ activity source
  positiveSource : Source
  positiveSource_mem : positiveSource ∈ sources
  positiveSource_value : (0 : Q') < activity positiveSource

private theorem listQSum_mono_on
    {A : Type} (lower upper : A → Q') :
    ∀ xs : List A,
      (∀ x, x ∈ xs → lower x ≤ upper x) →
        listQSum lower xs ≤ listQSum upper xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hbound => by
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _
          (hbound head List.mem_cons_self))
        (Q'.add_le_add_left _ _ _
          (listQSum_mono_on lower upper tail
            (fun x hx =>
              hbound x (List.mem_cons_of_mem head hx))))

private theorem listQSum_member_le
    {A : Type} (value : A → Q') :
    ∀ (xs : List A),
      (∀ x, x ∈ xs → (0 : Q') ≤ value x) →
      ∀ {selected : A}, selected ∈ xs →
      value selected ≤ listQSum value xs
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hvalue, selected, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail
            (fun x hx =>
              hvalue x (List.mem_cons_of_mem selected hx)))
      · have hinductive :=
          listQSum_member_le value tail
            (fun x hx =>
              hvalue x (List.mem_cons_of_mem head hx))
            htail
        have hmono :
            listQSum value tail ≤
              value head + listQSum value tail := by
          have hstep :=
            Q'.add_le_add_right
              (0 : Q') (value head)
              (listQSum value tail)
              (hvalue head List.mem_cons_self)
          rwa [Q'.zero_add'] at hstep
        exact Q'.le_trans' _ _ _ hinductive hmono

private theorem nested_scale_left
    {A B : Type}
    (scale : Q') (value : A → B → Q')
    (first : List A) (second : List B) :
    listQSum
        (fun x =>
          listQSum (fun y => scale * value x y) second)
        first ≈
      scale *
        listQSum
          (fun x => listQSum (value x) second)
          first := by
  refine Q'.eqv_trans _
    (listQSum
      (fun x => scale * listQSum (value x) second)
      first) _ ?_ ?_
  · exact listQSum_congr_on _ _ first
      (fun x _ => listQSum_mul_left scale (value x) second)
  · exact listQSum_mul_left scale
      (fun x => listQSum (value x) second) first

private theorem weightedCrossRatioTerm
    {Source : Type} {Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets)
    (first second : Source)
    (hfirst : first ∈ sources) (hsecond : second ∈ sources)
    (left right : Target)
    (hleft : left ∈ targets) (hright : right ∈ targets)
    (firstActivity secondActivity : Source → Q')
    (hfirstActivity : (0 : Q') ≤ firstActivity first)
    (hsecondActivity : (0 : Q') ≤ secondActivity second) :
    (kernel first left * firstActivity first) *
        (kernel second right * secondActivity second) ≤
      (certificate.spread * certificate.spread) *
        ((kernel first right * firstActivity first) *
          (kernel second left * secondActivity second)) := by
  let activityFactor :=
    firstActivity first * secondActivity second
  have hactivityFactor : (0 : Q') ≤ activityFactor :=
    Q'.mul_nonneg _ _
      hfirstActivity hsecondActivity
  have hcross :=
    certificate.crossRatioBound
      first hfirst second hsecond left hleft right hright
  have hscaled :
      (kernel first left * kernel second right) * activityFactor ≤
        ((certificate.spread * certificate.spread) *
          (kernel first right * kernel second left)) *
            activityFactor :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcross hactivityFactor
  have hleftReindex :
      (kernel first left * firstActivity first) *
          (kernel second right * secondActivity second) ≈
        (kernel first left * kernel second right) *
          activityFactor :=
    mul_swap4_local _ _ _ _
  have hrightReindex :
      ((certificate.spread * certificate.spread) *
          (kernel first right * kernel second left)) *
            activityFactor ≈
        (certificate.spread * certificate.spread) *
          ((kernel first right * firstActivity first) *
            (kernel second left * secondActivity second)) := by
    refine Q'.eqv_trans _
      ((certificate.spread * certificate.spread) *
        ((kernel first right * kernel second left) *
          activityFactor)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    exact Q'.mul_eqv_congr_left
      (certificate.spread * certificate.spread) _ _
      (mul_swap4_local _ _ _ _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hleftReindex)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv hrightReindex))

/-- The cross-ratio certificate bounds the complete finite image diameter.

The result quantifies over arbitrary nonnegative input activities and contains
no factor depending on `sources.length` or `targets.length`.  This is the
finite exact statement behind the phrase "dimension-free."  It remains
conditional on the supplied `spread`; proving that one common spread works
for the physical local activity cone is the analytic RG-I7 gate. -/
theorem finiteKernelAction_projectiveSpread
    {Source : Type} {Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets)
    (firstActivity secondActivity : Source → Q')
    (hfirstActivity :
      ∀ source, source ∈ sources →
        (0 : Q') ≤ firstActivity source)
    (hsecondActivity :
      ∀ source, source ∈ sources →
        (0 : Q') ≤ secondActivity source) :
    ProjectiveSpreadBound certificate.spread targets
      (finiteKernelAction kernel sources firstActivity)
      (finiteKernelAction kernel sources secondActivity) := by
  intro left hleft right hright
  let leftTerm : Source → Q' :=
    fun first =>
      kernel first left * firstActivity first
  let rightTerm : Source → Q' :=
    fun second =>
      kernel second right * secondActivity second
  let crossedLeftTerm : Source → Q' :=
    fun first =>
      kernel first right * firstActivity first
  let crossedRightTerm : Source → Q' :=
    fun second =>
      kernel second left * secondActivity second
  let crossedProduct : Source → Source → Q' :=
    fun first second =>
      crossedLeftTerm first * crossedRightTerm second
  have hdouble :
      listQSum
          (fun first =>
            listQSum
              (fun second => leftTerm first * rightTerm second)
              sources)
          sources ≤
        listQSum
          (fun first =>
            listQSum
              (fun second =>
                (certificate.spread * certificate.spread) *
                  crossedProduct first second)
              sources)
          sources := by
    apply listQSum_mono_on
    intro first hfirst
    apply listQSum_mono_on
    intro second hsecond
    exact weightedCrossRatioTerm
      certificate first second hfirst hsecond
      left right hleft hright
      firstActivity secondActivity
      (hfirstActivity first hfirst)
      (hsecondActivity second hsecond)
  have hleftProduct :
      listQSum
          (fun first =>
            listQSum
              (fun second => leftTerm first * rightTerm second)
              sources)
          sources ≈
        finiteKernelAction kernel sources firstActivity left *
          finiteKernelAction kernel sources secondActivity right := by
    exact listQSum_product leftTerm rightTerm sources sources
  have hcrossedProduct :
      listQSum
          (fun first =>
            listQSum (crossedProduct first) sources)
          sources ≈
        finiteKernelAction kernel sources firstActivity right *
          finiteKernelAction kernel sources secondActivity left := by
    exact listQSum_product
      crossedLeftTerm crossedRightTerm sources sources
  have hscaledProduct :
      listQSum
          (fun first =>
            listQSum
              (fun second =>
                (certificate.spread * certificate.spread) *
                  crossedProduct first second)
              sources)
          sources ≈
        (certificate.spread * certificate.spread) *
          (finiteKernelAction kernel sources firstActivity right *
            finiteKernelAction kernel sources secondActivity left) := by
    exact Q'.eqv_trans _ _ _
      (nested_scale_left
        (certificate.spread * certificate.spread)
        crossedProduct sources sources)
      (Q'.mul_eqv_congr_left
        (certificate.spread * certificate.spread) _ _
        hcrossedProduct)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hleftProduct)
    (Q'.le_trans' _ _ _ hdouble
      (Q'.le_of_eqv hscaledProduct))

/-- A certified strictly-positive kernel sends every nonzero nonnegative
activity into the strict interior on every selected target coordinate. -/
theorem finiteKernelAction_pos
    {Source : Type} {Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets)
    {activity : Source → Q'}
    (hactivity : NonzeroNonnegativeActivity sources activity)
    {target : Target} (htarget : target ∈ targets) :
    (0 : Q') <
      finiteKernelAction kernel sources activity target := by
  let term : Source → Q' :=
    fun source => kernel source target * activity source
  have htermNonnegative :
      ∀ source, source ∈ sources →
        (0 : Q') ≤ term source := by
    intro source hsource
    exact Q'.mul_nonneg _ _
      (Q'.le_of_lt
        (certificate.strictlyPositive source hsource
          target htarget))
      (hactivity.nonnegative source hsource)
  have hwitness :
      (0 : Q') <
        term hactivity.positiveSource :=
    Q'.mul_pos
      (certificate.strictlyPositive
        hactivity.positiveSource
        hactivity.positiveSource_mem target htarget)
      hactivity.positiveSource_value
  have hle :
      term hactivity.positiveSource ≤
        listQSum term sources :=
    listQSum_member_le term sources htermNonnegative
      hactivity.positiveSource_mem
  exact Q'.pos_of_lt_of_le hwitness hle

end FiniteCrossRatioDiameterCertificate

/-! ## One common spread across cutoff and volume -/

/-- A uniform family of finite cross-ratio certificates.

The common `spread` is data shared by every regulator index.  This structure
does not claim that the index is a physical cutoff/volume pair; a physical
specialization must provide that identification and must use a local activity
cone rather than silently tensoring the full configuration cone. -/
structure UniformCrossRatioDiameterCertificate
    (Index : Type)
    (Source Target : Index → Type)
    (kernel : ∀ index, Source index → Target index → Q')
    (sources : ∀ index, List (Source index))
    (targets : ∀ index, List (Target index)) : Type where
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
    {Index : Type}
    {Source Target : Index → Type}
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
    {Index : Type}
    {Source Target : Index → Type}
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
#print axioms FiniteCrossRatioDiameterCertificate.widen
#print axioms FiniteCrossRatioDiameterCertificate.rowRescale
#print axioms FiniteCrossRatioDiameterCertificate.rowRescale_candidateRate_eqv
#print axioms FiniteCrossRatioDiameterCertificate.columnRescale
#print axioms FiniteCrossRatioDiameterCertificate.columnRescale_candidateRate_eqv
#print axioms FiniteCrossRatioDiameterCertificate.pointwiseMul
#print axioms FiniteCrossRatioDiameterCertificate.sourceIndependentCertificate
#print axioms FiniteCrossRatioDiameterCertificate.sourceIndependentCertificate_candidateRate_eqv_zero
#print axioms FiniteCrossRatioDiameterCertificate.factorizedCertificate
#print axioms FiniteCrossRatioDiameterCertificate.factorizedCertificate_cons_spread
#print axioms FiniteCrossRatioDiameterCertificate.factorizedCertificate_spread_eqv_product
#print axioms FiniteCrossRatioDiameterCertificate.factorSpreadProduct_mask_eqv_filter
#print axioms FiniteCrossRatioDiameterCertificate.factorizedCertificate_spread_eqv_activeProduct
#print axioms FiniteCrossRatioDiameterCertificate.spreadPower_mono
#print axioms FiniteCrossRatioDiameterCertificate.finiteKernelAction_projectiveSpread
#print axioms FiniteCrossRatioDiameterCertificate.finiteKernelAction_pos
#print axioms UniformCrossRatioDiameterCertificate.atIndex
#print axioms UniformCrossRatioDiameterCertificate.candidateRate_eqv

end YMGap.Continuum.RationalCrossRatioDiameter
