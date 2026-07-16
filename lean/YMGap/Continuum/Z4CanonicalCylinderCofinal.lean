/-
# Cofinal limits for finite canonical cylinder events

Canonical transport composes on every marked root.  The finite-cylinder
boundary modulus therefore compares any two sufficiently large boxes, with a
finite prefactor depending only on the number of marked local polymers.  This
module packages the resulting sequence as a constructive real and records its
probability bounds.
-/

import YMGap.Continuum.Z4CanonicalCylinderStability

namespace YMGap.Continuum.Z4CanonicalCylinderCofinal

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalOccurrenceCofinal
open YMGap.Continuum.Z4CanonicalOccurrenceStability
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Coordinatewise transport coherence -/

theorem transportedCylinderRoots_canonical
    {base outer : Nat} (hbaseOuter : base ≤ outer)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ root, root ∈ transportedCylinderRoots base outer roots →
      root ∈ canonicalSurfacePolymers outer := by
  intro root hroot
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hroot
  subst root
  exact transportPolymer_mem_canonicalSurfacePolymers
    hbaseOuter (hroots source hsource)

theorem transportedCylinderRoots_inside_source
    {base outer : Nat} (hbaseOuter : base ≤ outer)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ root, root ∈ transportedCylinderRoots base outer roots →
      PolymerInsideBox base outer root := by
  intro root hroot
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hroot
  subst root
  exact transportPolymer_inside_source_box
    hbaseOuter (hroots source hsource)

theorem transportedCylinderRoots_trans
    {base middle outer : Nat}
    (hbaseMiddle : base ≤ middle)
    (hmiddleOuter : middle ≤ outer) :
    ∀ {roots : List (List Nat)},
      (∀ root, root ∈ roots →
        root ∈ canonicalSurfacePolymers base) →
      transportedCylinderRoots middle outer
          (transportedCylinderRoots base middle roots) =
        transportedCylinderRoots base outer roots
  | [], _ => rfl
  | root :: roots, hroots => by
      simp only [transportedCylinderRoots, List.map_cons]
      rw [transportPolymer_trans hbaseMiddle hmiddleOuter
        (hroots root List.mem_cons_self)]
      exact congrArg
        (List.cons (transportPolymer base outer root))
        (transportedCylinderRoots_trans hbaseMiddle hmiddleOuter
          (fun tailRoot htail =>
            hroots tailRoot (List.mem_cons_of_mem root htail)))

theorem targetCylinderEvent_trans
    {base middle outer : Nat}
    (hbaseMiddle : base ≤ middle)
    (hmiddleOuter : middle ≤ outer)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    targetCylinderEvent middle outer
        (transportedCylinderRoots base middle roots) predicate =
      targetCylinderEvent base outer roots predicate := by
  funext family
  unfold targetCylinderEvent cylinderEvent
  rw [transportedCylinderRoots_trans
    hbaseMiddle hmiddleOuter hroots]

/-! ## 2. Pairwise cofinal modulus -/

theorem anchorCylinderProbability_cofinal_abs_sub_le
    {base n m : Nat} (hbaseN : base ≤ n) (hnm : n ≤ m)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (anchorEventProbability m
            (targetCylinderEvent base m roots predicate) -
          anchorEventProbability n
            (targetCylinderEvent base n roots predicate)) ≤
      cylinderBoundaryEpsilon roots.length (n - base) := by
  let middleRoots := transportedCylinderRoots base n roots
  have hmiddleCanonical : ∀ root, root ∈ middleRoots →
      root ∈ canonicalSurfacePolymers n :=
    transportedCylinderRoots_canonical hbaseN hroots
  have hmiddleInside : ∀ root, root ∈ middleRoots →
      PolymerInsideBox base n root :=
    transportedCylinderRoots_inside_source hbaseN hroots
  have hbox : base + (n - base) = n := Nat.add_sub_of_le hbaseN
  have hraw :=
    anchorCylinderProbability_abs_sub_le_boundaryEpsilon_of_inside
      hnm hmiddleCanonical hmiddleInside predicate hbox
  have htarget := targetCylinderEvent_trans
    hbaseN hnm hroots predicate
  rw [htarget] at hraw
  have hlength : middleRoots.length = roots.length := by
    simp [middleRoots, transportedCylinderRoots]
  rw [hlength] at hraw
  exact hraw

def cylinderBoundaryCoefficient (rootCount : Nat) : Q' :=
  Q'.ofNat rootCount * Q'.ofNat 2

private theorem ofNat_nonnegative_local (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

theorem cylinderBoundaryCoefficient_nonnegative (rootCount : Nat) :
    (0 : Q') ≤ cylinderBoundaryCoefficient rootCount := by
  unfold cylinderBoundaryCoefficient
  exact Q'.mul_nonneg _ _
    (ofNat_nonnegative_local rootCount) (ofNat_nonnegative_local 2)

private theorem two_mul_eqv_add_self_local (x : Q') :
    Q'.ofNat 2 * x ≈ x + x := by
  have htwo : Q'.ofNat 2 ≈ (1 : Q') + 1 := by decide
  refine Q'.eqv_trans _ (((1 : Q') + 1) * x) _
    (Q'.mul_eqv_congr_right (Q'.ofNat 2) ((1 : Q') + 1) x htwo) ?_
  refine Q'.eqv_trans _ ((1 : Q') * x + (1 : Q') * x) _
    (Q'.add_mul_eqv 1 1 x) ?_
  exact Q'.add_eqv_congr'
    (Q'.one_mul_eqv x) (Q'.one_mul_eqv x)

theorem cylinderBoundaryEpsilon_le_coefficient_half_pow
    (rootCount distance : Nat) :
    cylinderBoundaryEpsilon rootCount distance ≤
      cylinderBoundaryCoefficient rootCount * HalfPow.half ^ distance := by
  have htail := occurrenceBoundaryEpsilon_le_half_pow distance
  have hsum :
      occurrenceBoundaryEpsilon distance + occurrenceBoundaryEpsilon distance ≤
        HalfPow.half ^ distance + HalfPow.half ^ distance :=
    Q'.add_le_add htail htail
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (occurrenceBoundaryEpsilon distance + occurrenceBoundaryEpsilon distance)
    (HalfPow.half ^ distance + HalfPow.half ^ distance)
    (Q'.ofNat rootCount) hsum (ofNat_nonnegative_local rootCount)
  have hreorder :
      Q'.ofNat rootCount *
          (HalfPow.half ^ distance + HalfPow.half ^ distance) ≈
        cylinderBoundaryCoefficient rootCount * HalfPow.half ^ distance := by
    unfold cylinderBoundaryCoefficient
    have hrhs :
        (Q'.ofNat rootCount * Q'.ofNat 2) * HalfPow.half ^ distance ≈
          Q'.ofNat rootCount *
            (HalfPow.half ^ distance + HalfPow.half ^ distance) := by
      refine Q'.eqv_trans _
        (Q'.ofNat rootCount *
          (Q'.ofNat 2 * HalfPow.half ^ distance)) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      exact Q'.mul_eqv_congr_left (Q'.ofNat rootCount) _ _
        (two_mul_eqv_add_self_local (HalfPow.half ^ distance))
    exact Q'.eqv_symm hrhs
  unfold cylinderBoundaryEpsilon
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hreorder)

theorem anchorCylinderProbability_cofinal_abs_sub_le_half_pow
    {base precision n m : Nat}
    (hprecision : base + precision ≤ n) (hnm : n ≤ m)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (anchorEventProbability m
            (targetCylinderEvent base m roots predicate) -
          anchorEventProbability n
            (targetCylinderEvent base n roots predicate)) ≤
      cylinderBoundaryCoefficient roots.length *
        HalfPow.half ^ precision := by
  have hbaseN : base ≤ n :=
    Nat.le_trans (Nat.le_add_right base precision) hprecision
  have hraw := anchorCylinderProbability_cofinal_abs_sub_le
    hbaseN hnm hroots predicate
  have htail := cylinderBoundaryEpsilon_le_coefficient_half_pow
    roots.length (n - base)
  have hprecisionSub : precision ≤ n - base :=
    Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hprecision)
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hprecisionSub
  have hhalf : HalfPow.half ^ (n - base) ≤
      HalfPow.half ^ precision := by
    rw [hoffset]
    exact ExpNeg.pow_half_antitone precision offset
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (HalfPow.half ^ (n - base)) (HalfPow.half ^ precision)
    (cylinderBoundaryCoefficient roots.length) hhalf
    (cylinderBoundaryCoefficient_nonnegative roots.length)
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ htail hscaled)

/-! ## 3. Constructive-real cylinder limits -/

private theorem two_sided_add_of_abs_sub_le {a b epsilon : Q'}
    (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

def anchorCylinderCofinalSequence
    (base : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) (stage : Nat) : Q' :=
  anchorEventProbability (base + stage)
    (targetCylinderEvent base (base + stage) roots predicate)

def anchorCylinderCofinalLimit
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) : CReal where
  approx := anchorCylinderCofinalSequence base roots predicate
  cauchy := by
    intro epsilon hepsilon
    let coefficient := cylinderBoundaryCoefficient roots.length
    let scaledTolerance :=
      epsilon * Q'.invSucc coefficient.num.toNat
    have hcoefficient : (0 : Q') ≤ coefficient :=
      cylinderBoundaryCoefficient_nonnegative roots.length
    have hscaledPositive : (0 : Q') < scaledTolerance :=
      Q'.mul_pos hepsilon (Q'.invSucc_pos coefficient.num.toNat)
    have hscaledFinal : coefficient * scaledTolerance ≤ epsilon :=
      ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
        hcoefficient (Q'.le_of_lt hepsilon)
    refine ⟨scaledTolerance.den, fun m n hm hn => ?_⟩
    rcases Nat.le_total m n with hmn | hnm
    · have hdyadic :=
        anchorCylinderProbability_cofinal_abs_sub_le_half_pow
          (base := base) (precision := scaledTolerance.den)
          (n := base + m) (m := base + n)
          (by omega) (by omega) hroots predicate
      have hhalf := HalfPow.pow_half_le
        scaledTolerance hscaledPositive
      have hscaledHalf := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ scaledTolerance.den) scaledTolerance
        coefficient hhalf hcoefficient
      have habs : Q'.abs
          (anchorCylinderCofinalSequence base roots predicate n -
            anchorCylinderCofinalSequence base roots predicate m) ≤
          epsilon :=
        Q'.le_trans' _ _ _ hdyadic
          (Q'.le_trans' _ _ _ hscaledHalf hscaledFinal)
      have hpair := two_sided_add_of_abs_sub_le habs
      exact ⟨hpair.2, hpair.1⟩
    · have hdyadic :=
        anchorCylinderProbability_cofinal_abs_sub_le_half_pow
          (base := base) (precision := scaledTolerance.den)
          (n := base + n) (m := base + m)
          (by omega) (by omega) hroots predicate
      have hhalf := HalfPow.pow_half_le
        scaledTolerance hscaledPositive
      have hscaledHalf := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ scaledTolerance.den) scaledTolerance
        coefficient hhalf hcoefficient
      have habs : Q'.abs
          (anchorCylinderCofinalSequence base roots predicate m -
            anchorCylinderCofinalSequence base roots predicate n) ≤
          epsilon :=
        Q'.le_trans' _ _ _ hdyadic
          (Q'.le_trans' _ _ _ hscaledHalf hscaledFinal)
      exact two_sided_add_of_abs_sub_le habs

@[simp] theorem anchorCylinderCofinalLimit_approx
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    (anchorCylinderCofinalLimit hroots predicate).approx stage =
      anchorCylinderCofinalSequence base roots predicate stage := rfl

theorem anchorCylinderCofinalSequence_converges
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        (anchorCylinderCofinalSequence base roots predicate stage))
      (anchorCylinderCofinalLimit hroots predicate) :=
  CReal.convergesTo_self (anchorCylinderCofinalLimit hroots predicate)

/-- Positivity of the finite-cylinder thermodynamic-limit functional on
indicator events. -/
theorem anchorCylinderCofinalLimit_nonnegative
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.ofQ' 0 ≤ anchorCylinderCofinalLimit hroots predicate := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  exact anchorEventProbability_nonnegative (base + stage) _

theorem anchorCylinderCofinalLimit_le_one
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    anchorCylinderCofinalLimit hroots predicate ≤ CReal.ofQ' 1 := by
  apply CReal.le_ofQ'_of_approx_le
  intro stage
  exact anchorEventProbability_le_one (base + stage) _

end YMGap.Continuum.Z4CanonicalCylinderCofinal

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalCylinderCofinal.transportedCylinderRoots_trans
#print axioms YMGap.Continuum.Z4CanonicalCylinderCofinal.anchorCylinderProbability_cofinal_abs_sub_le
#print axioms YMGap.Continuum.Z4CanonicalCylinderCofinal.anchorCylinderProbability_cofinal_abs_sub_le_half_pow
#print axioms YMGap.Continuum.Z4CanonicalCylinderCofinal.anchorCylinderCofinalLimit
#print axioms YMGap.Continuum.Z4CanonicalCylinderCofinal.anchorCylinderCofinalLimit_nonnegative
#print axioms YMGap.Continuum.Z4CanonicalCylinderCofinal.anchorCylinderCofinalLimit_le_one
