/-
# Exact Cayley split for the plaquette vector jet

For a unit plaquette quaternion with scalar coordinate `r`, the vector jet is
`1-r^2`.  The exact Cayley deficit is `delta=2*(1-r)`, hence

  4*(1-r^2) = 4*delta-delta^2.

Combining this elementary identity with the existing cleared Cayley theorem
gives a division-free formula whose leading term is the finite-Gaussian
quadratic `H2`.  The explicit residual retains the complete cubic-through-
sixth Cayley deficit and the nonlinear deficit square.  No measure comparison,
sign estimate, cutoff removal, continuum theory, or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCayleyVectorJet

set_option autoImplicit false
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCommutatorDefect (plaquetteWord)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem addCongr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a + c ≈ b + d :=
  Q'.add_eqv_congr' hab hcd

private theorem mulCongr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

/-- Squared vector-coordinate norm of one rational unit quaternion. -/
def unitQuaternionVectorJet (word : UnitNorm) : Q' :=
  (word.val.i * word.val.i + word.val.j * word.val.j) +
    word.val.k * word.val.k

/-- Every rational unit-quaternion vector jet is the complement of its scalar
square.  Keeping the unit quaternion abstract prevents expansion of later
noncommutative words inside the commutative ring normalizer. -/
theorem unitQuaternionVectorJet_scalar_complement (word : UnitNorm) :
    unitQuaternionVectorJet word ≈
      1 + -(word.val.r * word.val.r) := by
  let R := word.val.r * word.val.r
  let I := word.val.i * word.val.i
  let J := word.val.j * word.val.j
  let K := word.val.k * word.val.k
  have hunit : normSq word.val ≈ 1 := word.unitNorm
  change (I + J) + K ≈ 1 + -R
  have hreorder : ((I + J) + K) + R ≈ normSq word.val := by
    change ((I + J) + K) + R ≈ (R + I) + (J + K)
    calc
      ((I + J) + K) + R ≈ (I + J) + (K + R) :=
        Q'.add_assoc_eqv _ _ _
      _ ≈ (I + J) + (R + K) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)
      _ ≈ I + (J + (R + K)) :=
        Q'.add_assoc_eqv _ _ _
      _ ≈ I + (R + (J + K)) := by
        apply Q'.add_eqv_congr_left
        exact Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv J R K))
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv J R))
            (Q'.add_assoc_eqv R J K))
      _ ≈ (I + R) + (J + K) :=
        Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
      _ ≈ (R + I) + (J + K) :=
        Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv I R)
  have hplus : ((I + J) + K) + R ≈ 1 :=
    Q'.eqv_trans _ _ _ hreorder hunit
  calc
    (I + J) + K ≈ ((I + J) + K) + 0 :=
      Q'.eqv_symm (QPoly.q_add_zero_eqv _)
    _ ≈ ((I + J) + K) + (R + -R) :=
      Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_neg_self_eqv R))
    _ ≈ (((I + J) + K) + R) + -R :=
      Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
    _ ≈ 1 + -R :=
      Q'.add_eqv_congr_right _ _ _ hplus

/-- Squared vector-coordinate norm of the actual stereographic plaquette word. -/
def plaquetteWordVectorJet (e : Q') (a b c d : Triple) : Q' :=
  unitQuaternionVectorJet
    (plaquetteWord
      (stereographic (scale3 e a))
      (stereographic (scale3 e b))
      (stereographic (scale3 e c))
      (stereographic (scale3 e d)))

/-- Specialization of the generic unit-norm complement to the actual
stereographic plaquette word. -/
theorem plaquetteWordVectorJet_scalar_complement
    (e : Q') (a b c d : Triple) :
    plaquetteWordVectorJet e a b c d ≈
      1 + -((plaquetteWord
        (stereographic (scale3 e a))
        (stereographic (scale3 e b))
        (stereographic (scale3 e c))
        (stereographic (scale3 e d))).val.r *
          (plaquetteWord
            (stereographic (scale3 e a))
            (stereographic (scale3 e b))
            (stereographic (scale3 e c))
            (stereographic (scale3 e d))).val.r) := by
  exact unitQuaternionVectorJet_scalar_complement
    (plaquetteWord
      (stereographic (scale3 e a))
      (stereographic (scale3 e b))
      (stereographic (scale3 e c))
      (stereographic (scale3 e d)))

/-- Exact Cayley terms beyond the quadratic `H2` contribution. -/
def cayleyDeficitHigher (e : Q') (a b c d : Triple) : Q' :=
  ((((e * e) * e) * H3 a b c d +
      ((e * e) * (e * e)) * H4 a b c d) +
    (((e * e) * (e * e)) * e) * H5 a b c d) +
  (((e * e) * (e * e)) * (e * e)) * H6 a b c d

theorem cayleyDeficit_quadratic_higher
    (e : Q') (a b c d : Triple) :
    cayleyDeficit e a b c d ≈
      (e * e) * H2 a b c d + cayleyDeficitHigher e a b c d := by
  unfold cayleyDeficit cayleyDeficitHigher
  exact poly_identity_of_normal_eq
    (((((.var 0 * .var 0) * .var 1 +
        ((.var 0 * .var 0) * .var 0) * .var 2) +
      ((.var 0 * .var 0) * (.var 0 * .var 0)) * .var 3) +
      (((.var 0 * .var 0) * (.var 0 * .var 0)) * .var 0) * .var 4) +
      (((.var 0 * .var 0) * (.var 0 * .var 0)) *
        (.var 0 * .var 0)) * .var 5)
    ((.var 0 * .var 0) * .var 1 +
      (((((.var 0 * .var 0) * .var 0) * .var 2 +
        ((.var 0 * .var 0) * (.var 0 * .var 0)) * .var 3) +
        (((.var 0 * .var 0) * (.var 0 * .var 0)) * .var 0) * .var 4) +
        (((.var 0 * .var 0) * (.var 0 * .var 0)) *
          (.var 0 * .var 0)) * .var 5))
    (by decide)
    (fun index =>
      if index = 0 then e
      else if index = 1 then H2 a b c d
      else if index = 2 then H3 a b c d
      else if index = 3 then H4 a b c d
      else if index = 4 then H5 a b c d
      else H6 a b c d)

/-- Residual after extracting the exact quadratic Cayley contribution from
the denominator-cleared vector jet. -/
def cayleyVectorJetRemainder (e : Q') (a b c d : Triple) : Q' :=
  let denominator := cayleyDenominator e a b c d
  let deficit := cayleyDeficit e a b c d
  4 * denominator * cayleyDeficitHigher e a b c d +
    -(deficit * deficit)

/-- Exact denominator-cleared vector-jet identity for the actual ordered
stereographic plaquette word. -/
theorem plaquetteWordVectorJet_cayley_cleared
    (e : Q') (a b c d : Triple) :
    let denominator := cayleyDenominator e a b (neg3 c) (neg3 d)
    let deficit := cayleyDeficit e a b (neg3 c) (neg3 d)
    4 * (denominator * denominator) * plaquetteWordVectorJet e a b c d ≈
      4 * denominator * deficit + -(deficit * deficit) := by
  dsimp only
  let word := plaquetteWord
    (stereographic (scale3 e a))
    (stereographic (scale3 e b))
    (stereographic (scale3 e c))
    (stereographic (scale3 e d))
  let denominator := cayleyDenominator e a b (neg3 c) (neg3 d)
  let deficit := cayleyDeficit e a b (neg3 c) (neg3 d)
  let delta := 2 + -(2 * word.val.r)
  have hjet := plaquetteWordVectorJet_scalar_complement e a b c d
  change plaquetteWordVectorJet e a b c d ≈
    1 + -(word.val.r * word.val.r) at hjet
  have hdeficit := plaquetteWord_cayley_cleared e a b c d
  change denominator * delta ≈ deficit at hdeficit
  have hleft :
      4 * (denominator * denominator) * plaquetteWordVectorJet e a b c d ≈
        4 * (denominator * denominator) *
          (1 + -(word.val.r * word.val.r)) :=
    Q'.mul_eqv_congr_left (4 * (denominator * denominator)) _ _ hjet
  have hcore :
      4 * (denominator * denominator) *
          (1 + -(word.val.r * word.val.r)) ≈
        4 * denominator * (denominator * delta) +
          -((denominator * delta) * (denominator * delta)) := by
    unfold delta
    exact poly_identity_of_normal_eq
      ((4 * (.var 0 * .var 0)) * (1 + -(.var 1 * .var 1)))
      ((4 * .var 0) * (.var 0 * (2 + -(2 * .var 1))) +
        -((.var 0 * (2 + -(2 * .var 1))) *
          (.var 0 * (2 + -(2 * .var 1)))))
      (by decide) (fun | 0 => denominator | _ => word.val.r)
  have hright :
      4 * denominator * (denominator * delta) +
          -((denominator * delta) * (denominator * delta)) ≈
        4 * denominator * deficit + -(deficit * deficit) :=
    addCongr
      (mulCongr (Q'.eqv_refl (4 * denominator)) hdeficit)
      (Q'.neg_eqv_congr _ _ (mulCongr hdeficit hdeficit))
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_trans _ _ _ hcore hright)

/-- The same exact identity with the finite-Gaussian quadratic `H2` separated
from one explicit residual. -/
theorem plaquetteWordVectorJet_quadratic_remainder
    (e : Q') (a b c d : Triple) :
    let denominator := cayleyDenominator e a b (neg3 c) (neg3 d)
    4 * (denominator * denominator) * plaquetteWordVectorJet e a b c d ≈
      4 * denominator * ((e * e) * H2 a b (neg3 c) (neg3 d)) +
        cayleyVectorJetRemainder e a b (neg3 c) (neg3 d) := by
  dsimp only
  let denominator := cayleyDenominator e a b (neg3 c) (neg3 d)
  let deficit := cayleyDeficit e a b (neg3 c) (neg3 d)
  let leading := (e * e) * H2 a b (neg3 c) (neg3 d)
  let higher := cayleyDeficitHigher e a b (neg3 c) (neg3 d)
  have hbase := plaquetteWordVectorJet_cayley_cleared e a b c d
  change 4 * (denominator * denominator) * plaquetteWordVectorJet e a b c d ≈
    4 * denominator * deficit + -(deficit * deficit) at hbase
  have hsplit := cayleyDeficit_quadratic_higher e a b (neg3 c) (neg3 d)
  change deficit ≈ leading + higher at hsplit
  have hreplace :
      4 * denominator * deficit + -(deficit * deficit) ≈
        4 * denominator * (leading + higher) + -(deficit * deficit) :=
    addCongr
      (mulCongr (Q'.eqv_refl (4 * denominator)) hsplit)
      (Q'.eqv_refl _)
  have hregroup :
      4 * denominator * (leading + higher) + -(deficit * deficit) ≈
        4 * denominator * leading +
          (4 * denominator * higher + -(deficit * deficit)) :=
    poly_identity_of_normal_eq
      ((4 * .var 0) * (.var 1 + .var 2) + -(.var 3 * .var 3))
      ((4 * .var 0) * .var 1 +
        ((4 * .var 0) * .var 2 + -(.var 3 * .var 3)))
      (by decide)
      (fun | 0 => denominator | 1 => leading | 2 => higher | _ => deficit)
  unfold cayleyVectorJetRemainder
  exact Q'.eqv_trans _ _ _ hbase
    (Q'.eqv_trans _ _ _ hreplace hregroup)

end YMGap.Continuum.BF4ExactSlabPlaquetteCayleyVectorJet

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyVectorJet.plaquetteWordVectorJet_scalar_complement
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyVectorJet.unitQuaternionVectorJet_scalar_complement
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyVectorJet.cayleyDeficit_quadratic_higher
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyVectorJet.plaquetteWordVectorJet_cayley_cleared
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyVectorJet.plaquetteWordVectorJet_quadratic_remainder
