/-
# Computed intervals for every supported rational quaternion polynomial

Every one of the four coordinates of each Haar-unit quaternion has square
cap one. Products retain that cap, including shared variables and arbitrary
degrees. A signed rational coefficient contributes its square plus one to
the final interval cap; summing the literal term list gives the computed
polynomialCap. This deliberately coarse cap depends on the presentation,
not on the number of carrier blocks or on monomial degrees.

The reconstruction is on the actual raw exponent lists. Only trailing zero
padding is transported, using equality under EVERY Haar insertion, including
insertions not syntactically supported on the declared carrier. No pointwise
evaluation bound is substituted for a polynomial certificate. Empty carriers,
empty polynomials, repeated monomials and zero or negative coefficients are
included. The consumer is the signed polynomial middle-bracket construction;
no stationary, cutoff-limit, OS or continuum conclusion is made here.
-/

import YMGap.Continuum.QuaternionHaarPolynomialInterval
import YMGap.Continuum.SU2QuaternionHaarSparseEquality

namespace YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarSparseEquality
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

private def squareExpr (i : Nat) : PolyExpr := .mul (.var i) (.var i)

private def componentEnvironment (p : PolyQuaternion) : Nat → RatPoly
  | 0 => p.scalar
  | 1 => p.iPart
  | 2 => p.jPart
  | 3 => p.kPart
  | _ => polyZero

private def iSquare {blocks : Nat} {p : PolyQuaternion}
    (hp : Supported blocks p)
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne) :
    SquareBound blocks p.iPart 1 :=
  SquareBound.scalar (p := ⟨p.iPart, p.scalar, p.jPart, p.kPart⟩)
    ⟨hp.iPart, hp.scalar, hp.jPart, hp.kPart⟩
    ((RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
      (.add (squareExpr 1) (.add (squareExpr 0) (.add (squareExpr 2) (squareExpr 3))))
      (.add (squareExpr 0) (.add (squareExpr 1) (.add (squareExpr 2) (squareExpr 3))))
      (by decide) (componentEnvironment p))).trans hnorm)

private def jSquare {blocks : Nat} {p : PolyQuaternion}
    (hp : Supported blocks p)
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne) :
    SquareBound blocks p.jPart 1 :=
  SquareBound.scalar (p := ⟨p.jPart, p.iPart, p.scalar, p.kPart⟩)
    ⟨hp.jPart, hp.iPart, hp.scalar, hp.kPart⟩
    ((RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
      (.add (squareExpr 2) (.add (squareExpr 1) (.add (squareExpr 0) (squareExpr 3))))
      (.add (squareExpr 0) (.add (squareExpr 1) (.add (squareExpr 2) (squareExpr 3))))
      (by decide) (componentEnvironment p))).trans hnorm)

private def kSquare {blocks : Nat} {p : PolyQuaternion}
    (hp : Supported blocks p)
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne) :
    SquareBound blocks p.kPart 1 :=
  SquareBound.scalar (p := ⟨p.kPart, p.iPart, p.jPart, p.scalar⟩)
    ⟨hp.kPart, hp.iPart, hp.jPart, hp.scalar⟩
    ((RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
      (.add (squareExpr 3) (.add (squareExpr 1) (.add (squareExpr 2) (squareExpr 0))))
      (.add (squareExpr 0) (.add (squareExpr 1) (.add (squareExpr 2) (squareExpr 3))))
      (by decide) (componentEnvironment p))).trans hnorm)

/-- All four real coordinates, with the literal carrier-support guard. -/
def coordinateSquareBound (blocks coordinate : Nat) (h : coordinate < 4 * blocks) :
    SquareBound blocks (polyVar coordinate) 1 := by
  have hmod := Nat.mod_lt coordinate (by decide : 0 < 4)
  have hdivision := Nat.mod_add_div coordinate 4
  have hb : coordinate / 4 < blocks := by omega
  have hp := Supported.coordinate hb
  have hn := haarNorm_coordinate hb
  by_cases h0 : coordinate % 4 = 0
  · have hi : 4 * (coordinate / 4) = coordinate := by omega
    simpa only [PolyQuaternion.coordinateVariable, hi] using SquareBound.scalar hp hn
  · by_cases h1 : coordinate % 4 = 1
    · have hi : 4 * (coordinate / 4) + 1 = coordinate := by omega
      simpa only [PolyQuaternion.coordinateVariable, hi] using iSquare hp hn
    · by_cases h2 : coordinate % 4 = 2
      · have hi : 4 * (coordinate / 4) + 2 = coordinate := by omega
        simpa only [PolyQuaternion.coordinateVariable, hi] using jSquare hp hn
      · have hi : 4 * (coordinate / 4) + 3 = coordinate := by omega
        simpa only [PolyQuaternion.coordinateVariable, hi] using kSquare hp hn

private def squareOfCarrier {blocks : Nat} {p q : RatPoly} {c : Q'}
    (hp : SupportedQuaternionBlocks blocks p) (he : HaarCarrierEqv blocks p q)
    (Q : SquareBound blocks q c) : SquareBound blocks p c where
  support := hp
  nonnegative := Q.nonnegative
  certificate := .transport
    (HaarCarrierEqv.add (HaarCarrierEqv.refl blocks (cap c))
      (HaarCarrierEqv.neg (HaarCarrierEqv.mul he he))) Q.certificate

private theorem singleton_supported (blocks : Nat) (m : List Nat) (c : Q')
    (hm : m.length ≤ 4 * blocks) : SupportedQuaternionBlocks blocks [(m, c)] := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  exact hm

private theorem zeros_exponent (start i : Nat) :
    exponentAt (List.replicate start 0) i = 0 := by
  induction start generalizing i with
  | zero => simp [exponentAt]
  | succ start ih =>
    cases i with
    | zero => simp [List.replicate_succ, exponentAt]
    | succ i => simpa only [List.replicate_succ, exponentAt, List.getD_cons_succ] using ih i

private theorem power_exponent (start exponent i : Nat) :
    exponentAt (List.replicate start 0 ++ [exponent]) i =
      if i = start then exponent else 0 := by
  induction start generalizing i with
  | zero =>
    cases i <;> rfl
  | succ start ih =>
    cases i with
    | zero =>
      rw [List.replicate_succ]
      change 0 = if 0 = start + 1 then exponent else 0
      exact (if_neg (Nat.zero_ne_add_one start)).symm
    | succ i =>
      rw [List.replicate_succ]
      change exponentAt (List.replicate start 0 ++ [exponent]) i =
        if Nat.succ i = Nat.succ start then exponent else 0
      rw [ih i]
      by_cases hi : i = start
      · rw [if_pos hi, if_pos (congrArg Nat.succ hi)]
      · rw [if_neg hi, if_neg (fun he => hi (Nat.succ.inj he))]

private theorem singletonCarrier (blocks : Nat) (m n : List Nat)
    (h : ∀ i, exponentAt m i = exponentAt n i) :
    HaarCarrierEqv blocks [(m, 1)] [(n, 1)] := by
  intro insertion
  apply haar_of_all_prefix blocks
  intro b
  exact (QuaternionPrefixPolynomialEqv.refl b insertion).mul
    (.cons ⟨Q'.eqv_refl 1, fun i _ => h i⟩ .nil)

private theorem power_step_mono (start exponent : Nat) :
    monoMul (List.replicate start 0 ++ [exponent]) (varMono start) =
      List.replicate start 0 ++ [exponent + 1] := by
  induction start with
  | zero => rfl
  | succ start ih => simpa [varMono, List.replicate_succ, monoMul] using congrArg (List.cons 0) ih

private theorem power_step (start exponent : Nat) :
    polyMul [(List.replicate start 0 ++ [exponent], 1)] (polyVar start) =
      [(List.replicate start 0 ++ [exponent + 1], 1)] := by
  simp only [polyMul, polyVar, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.append_nil, power_step_mono] <;> rfl

private def powerSquare (blocks start : Nat) (h : start + 1 ≤ 4 * blocks) :
    (exponent : Nat) → SquareBound blocks [(List.replicate start 0 ++ [exponent], 1)] 1
  | 0 => squareOfCarrier
      (singleton_supported blocks _ 1 (by simpa only [List.length_append,
        List.length_replicate, List.length_singleton] using h))
      (singletonCarrier blocks _ [] (fun i => by
        rw [power_exponent]
        simp [exponentAt]))
      (SquareBound.one blocks)
  | exponent + 1 => by
      rw [← power_step start exponent]
      exact SquareBound.changeCap (Q'.mul_one_eqv 1)
        ((powerSquare blocks start h exponent).mul (coordinateSquareBound blocks start (by omega)))

private theorem power_tail_mono (start exponent : Nat) (tail : List Nat) :
    monoMul (List.replicate start 0 ++ [exponent])
      (List.replicate (start + 1) 0 ++ tail) =
      List.replicate start 0 ++ exponent :: tail := by
  induction start with
  | zero => simp [List.replicate_succ, monoMul]
  | succ start ih => simpa [List.replicate_succ, monoMul] using congrArg (List.cons 0) ih

private theorem power_tail (start exponent : Nat) (tail : List Nat) :
    polyMul [(List.replicate start 0 ++ [exponent], 1)]
      [(List.replicate (start + 1) 0 ++ tail, 1)] =
      [(List.replicate start 0 ++ exponent :: tail, 1)] := by
  simp only [polyMul, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.append_nil, power_tail_mono] <;> rfl

private def monomialFromSquare (blocks : Nat) :
    (m : List Nat) → (start : Nat) → start + m.length ≤ 4 * blocks →
      SquareBound blocks [(List.replicate start 0 ++ m, 1)] 1
  | [], start, h => squareOfCarrier
      (singleton_supported blocks _ 1 (by simpa using h))
      (singletonCarrier blocks _ [] (fun i => by
        simpa only [List.append_nil, exponentAt, List.getD_nil] using zeros_exponent start i))
      (SquareBound.one blocks)
  | exponent :: tail, start, h => by
      rw [← power_tail start exponent tail]
      exact SquareBound.changeCap (Q'.mul_one_eqv 1)
        ((powerSquare blocks start (by simp only [List.length_cons] at h; omega) exponent).mul
          (monomialFromSquare blocks tail (start + 1) (by simp only [List.length_cons] at h; omega)))

/-- The actual raw coordinate monomial, not an evaluation-only substitute. -/
def monomialSquareBound (blocks : Nat) (m : List Nat) (hm : m.length ≤ 4 * blocks) :
    SquareBound blocks [(m, 1)] 1 := by
  simpa only [List.replicate_zero, List.nil_append, Nat.zero_add] using
    monomialFromSquare blocks m 0 (by simpa only [Nat.zero_add] using hm)

private theorem singleton_scale (m : List Nat) (c : Q') :
    RatPolyCoeffEqv [(m, c)] (polySmul c [(m, 1)]) := by
  intro weight
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv c))) (Q'.eqv_refl 0)

private def termInterval (blocks : Nat) (term : RatTerm)
    (ht : term.1.length ≤ 4 * blocks) :
    Interval blocks [term] (term.2 * term.2 + 1) :=
  Interval.ofSquare (SquareBound.changeCap (Q'.mul_one_eqv (term.2 * term.2))
    (SquareBound.ofCoeff (singleton_supported blocks term.1 term.2 ht)
      (singleton_scale term.1 term.2) ((monomialSquareBound blocks term.1 ht).smul term.2)))

/-- Explicit signed-coefficient cap; duplicate and zero terms remain visible.
There is no hidden dependence on carrier size, degree, nome or heat cutoff. -/
def polynomialCap : RatPoly → Q'
  | [] => 0
  | term :: rest => (term.2 * term.2 + 1) + polynomialCap rest

theorem polynomialCap_nonnegative (p : RatPoly) : (0 : Q') ≤ polynomialCap p := by
  induction p with
  | nil => exact Q'.le_refl' 0
  | cons term rest ih =>
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg term.2) Q'.zero_le_one) ih

/-- Constructed two-sided certificates for EVERY supported rational polynomial.
Only the original syntactic support proof is required. -/
def polynomialInterval (blocks : Nat) : (p : RatPoly) →
    SupportedQuaternionBlocks blocks p → Interval blocks p (polynomialCap p)
  | [], _ => Interval.zero blocks
  | term :: rest, hp =>
      (termInterval blocks term (hp term List.mem_cons_self)).add
        (polynomialInterval blocks rest (fun t ht => hp t (List.mem_cons_of_mem term ht)))

end YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

#print axioms YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval.coordinateSquareBound
#print axioms YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval.monomialSquareBound
#print axioms YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval.polynomialCap
#print axioms YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval.polynomialCap_nonnegative
#print axioms YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval.polynomialInterval
