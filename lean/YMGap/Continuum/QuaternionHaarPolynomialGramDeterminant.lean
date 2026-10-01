/- Constructive polynomial SOS certificate for the determinant of a finite
two-column Gram matrix.  The recursive Lagrange identity retains every pair,
including repetitions and overlapping variables. -/
import YMGap.Continuum.QuaternionHaarSquareCertificate
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.QuaternionHaarPolynomialGramDeterminant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)

local infix:50 " ≈ " => Q'.eqv

abbrev PolyPair := RatPoly × RatPoly

def squareFirst : List PolyPair → RatPoly
  | [] => polyZero
  | r :: rs => polyAdd (polyMul r.1 r.1) (squareFirst rs)

def squareSecond : List PolyPair → RatPoly
  | [] => polyZero
  | r :: rs => polyAdd (polyMul r.2 r.2) (squareSecond rs)

def mixedSum : List PolyPair → RatPoly
  | [] => polyZero
  | r :: rs => polyAdd (polyMul r.1 r.2) (mixedSum rs)

theorem squareFirst_eq (pairs : List PolyPair) :
    squareFirst pairs = polySum (pairs.map fun r => polyMul r.1 r.1) := by
  induction pairs with
  | nil => rfl
  | cons r rs ih => simp only [squareFirst, polySum, List.map_cons, ih]

theorem squareSecond_eq (pairs : List PolyPair) :
    squareSecond pairs = polySum (pairs.map fun r => polyMul r.2 r.2) := by
  induction pairs with
  | nil => rfl
  | cons r rs ih => simp only [squareSecond, polySum, List.map_cons, ih]

theorem mixedSum_eq (pairs : List PolyPair) :
    mixedSum pairs = polySum (pairs.map fun r => polyMul r.1 r.2) := by
  induction pairs with
  | nil => rfl
  | cons r rs ih => simp only [mixedSum, polySum, List.map_cons, ih]

def gramDeterminant (pairs : List PolyPair) : RatPoly :=
  polyAdd (polyMul (squareFirst pairs) (squareSecond pairs))
    (polyNeg (polyMul (mixedSum pairs) (mixedSum pairs)))

private def crossSquares (a b : RatPoly) : List PolyPair → RatPoly
  | [] => polyZero
  | r :: rs =>
      let d := polyAdd (polyMul a r.2) (polyNeg (polyMul b r.1))
      polyAdd (polyMul d d) (crossSquares a b rs)

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_difference {blocks : Nat} {a b c d : RatPoly}
    (ha : SupportedQuaternionBlocks blocks a) (hb : SupportedQuaternionBlocks blocks b)
    (hc : SupportedQuaternionBlocks blocks c) (hd : SupportedQuaternionBlocks blocks d) :
    SupportedQuaternionBlocks blocks
      (polyAdd (polyMul a b) (polyNeg (polyMul c d))) :=
  supported_add (supported_polyMul ha hb)
    (support_neg (supported_polyMul hc hd))

private def crossSquaresCertificate {blocks : Nat} (a b : RatPoly)
    (ha : SupportedQuaternionBlocks blocks a) (hb : SupportedQuaternionBlocks blocks b) :
    (pairs : List PolyPair) →
    (∀ r, r ∈ pairs → SupportedQuaternionBlocks blocks r.1 ∧
      SupportedQuaternionBlocks blocks r.2) → Certificate blocks (crossSquares a b pairs)
  | [], _ => Certificate.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
      (.smul 0 (by decide) (Certificate.one blocks))
  | r :: rs, hs => by
      let d := polyAdd (polyMul a r.2) (polyNeg (polyMul b r.1))
      have hr := hs r List.mem_cons_self
      exact .add (.square d (support_difference ha hr.2 hb hr.1))
        (crossSquaresCertificate a b ha hb rs
          (fun s h => hs s (List.mem_cons_of_mem r h)))

/- The cross-square expansion is proved by a structural induction.  These
   coefficient equalities deliberately use the normalizer rather than any
   independence/disjointness assumption on polynomial variables. -/
private theorem crossSquares_eq_formula (a b : RatPoly) :
    ∀ pairs : List PolyPair,
      RatPolyCoeffEqv (crossSquares a b pairs)
        (polyAdd
          (polyAdd (polyMul (polyMul a a) (squareSecond pairs))
            (polyMul (polyMul b b) (squareFirst pairs)))
          (polyNeg (polyMul (cap 2) (polyMul (polyMul a b) (mixedSum pairs)))))
  | [] => by
      have ha : RatPolyCoeffEqv (polyMul (polyMul a a) polyZero) polyZero :=
        RatPolyCoeffEqv.mul_zero_right _
      have hb : RatPolyCoeffEqv (polyMul (polyMul b b) polyZero) polyZero :=
        RatPolyCoeffEqv.mul_zero_right _
      have hab : RatPolyCoeffEqv (polyMul (polyMul a b) polyZero) polyZero :=
        RatPolyCoeffEqv.mul_zero_right _
      have hterm : RatPolyCoeffEqv
          (polyMul (cap 2) (polyMul (polyMul a b) polyZero)) polyZero :=
        (RatPolyCoeffEqv.refl (cap 2)).mul hab |>.trans
          (RatPolyCoeffEqv.mul_zero_right (cap 2))
      have hneg : RatPolyCoeffEqv
          (polyNeg (polyMul (cap 2) (polyMul (polyMul a b) polyZero))) polyZero := by
        simpa [polyNeg, polyZero] using RatPolyCoeffEqv.neg hterm
      have hzero : RatPolyCoeffEqv
          (polyAdd (polyAdd (polyMul (polyMul a a) polyZero)
            (polyMul (polyMul b b) polyZero))
            (polyNeg (polyMul (cap 2) (polyMul (polyMul a b) polyZero)))) polyZero := by
        have hassoc := RatPolyCoeffEqv.add_assoc
          (polyMul (polyMul a a) polyZero) (polyMul (polyMul b b) polyZero)
          (polyNeg (polyMul (cap 2) (polyMul (polyMul a b) polyZero)))
        exact hassoc.trans (ha.add (hb.add hneg)) |>.trans
          (RatPolyCoeffEqv.zero_add (polyAdd polyZero polyZero)) |>.trans
            (RatPolyCoeffEqv.zero_add polyZero)
      simpa [crossSquares, squareFirst, squareSecond, mixedSum] using hzero.symm
  | r :: rs => by
      have ih := crossSquares_eq_formula a b rs
      let d := polyAdd (polyMul a r.2) (polyNeg (polyMul b r.1))
      have hstep : RatPolyCoeffEqv (crossSquares a b (r :: rs))
          (polyAdd (polyMul d d) (polyAdd
            (polyAdd (polyMul (polyMul a a) (squareSecond rs))
              (polyMul (polyMul b b) (squareFirst rs)))
            (polyNeg (polyMul (cap 2) (polyMul (polyMul a b) (mixedSum rs)))))) :=
        (RatPolyCoeffEqv.refl _).add ih
      have halgebra : RatPolyCoeffEqv
          (polyAdd (polyMul d d) (polyAdd
            (polyAdd (polyMul (polyMul a a) (squareSecond rs))
              (polyMul (polyMul b b) (squareFirst rs)))
            (polyNeg (polyMul (cap 2) (polyMul (polyMul a b) (mixedSum rs))))))
          (polyAdd
            (polyAdd (polyMul (polyMul a a)
              (polyAdd (polyMul r.2 r.2) (squareSecond rs)))
              (polyMul (polyMul b b)
                (polyAdd (polyMul r.1 r.1) (squareFirst rs))))
            (polyNeg (polyMul (cap 2) (polyMul (polyMul a b)
              (polyAdd (polyMul r.1 r.2) (mixedSum rs)))))) := by
        exact coeffEvalExpr_eqv_of_normalize_eq
          (.add
            (.mul (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2))))
              (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))))
            (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 5))
              (.mul (.mul (.var 1) (.var 1)) (.var 4)))
              (.neg (.mul (.const 2) (.mul (.mul (.var 0) (.var 1)) (.var 6))))))
          (.add
            (.add (.mul (.mul (.var 0) (.var 0))
              (.add (.mul (.var 3) (.var 3)) (.var 5)))
              (.mul (.mul (.var 1) (.var 1))
                (.add (.mul (.var 2) (.var 2)) (.var 4))))
            (.neg (.mul (.const 2) (.mul (.mul (.var 0) (.var 1))
              (.add (.mul (.var 2) (.var 3)) (.var 6))))))
          (by decide) (fun
            | 0 => a
            | 1 => b
            | 2 => r.1
            | 3 => r.2
            | 4 => squareFirst rs
            | 5 => squareSecond rs
            | _ => mixedSum rs)
      exact hstep.trans halgebra

private theorem gram_cons_eqv (a b : RatPoly) (rs : List PolyPair) :
    RatPolyCoeffEqv
      (gramDeterminant ((a,b) :: rs))
      (polyAdd (gramDeterminant rs) (crossSquares a b rs)) := by
  have hc := crossSquares_eq_formula a b rs
  have halgebra : RatPolyCoeffEqv
      (polyAdd
        (polyMul (polyAdd (polyMul a a) (squareFirst rs))
          (polyAdd (polyMul b b) (squareSecond rs)))
        (polyNeg (polyMul (polyAdd (polyMul a b) (mixedSum rs))
          (polyAdd (polyMul a b) (mixedSum rs)))))
      (polyAdd (gramDeterminant rs)
        (polyAdd
          (polyAdd (polyMul (polyMul a a) (squareSecond rs))
            (polyMul (polyMul b b) (squareFirst rs)))
          (polyNeg (polyMul (cap 2) (polyMul (polyMul a b) (mixedSum rs)))))) := by
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.mul (.add (.mul (.var 0) (.var 0)) (.var 3))
          (.add (.mul (.var 1) (.var 1)) (.var 4)))
        (.neg (.mul (.add (.mul (.var 0) (.var 1)) (.var 5))
          (.add (.mul (.var 0) (.var 1)) (.var 5)))))
      (.add
        (.add (.mul (.var 3) (.var 4)) (.neg (.mul (.var 5) (.var 5))))
        (.add
          (.add (.mul (.mul (.var 0) (.var 0)) (.var 4))
            (.mul (.mul (.var 1) (.var 1)) (.var 3)))
          (.neg (.mul (.const 2) (.mul (.mul (.var 0) (.var 1)) (.var 5))))))
      (by decide) (fun
        | 0 => a
        | 1 => b
        | 2 => polyZero
        | 3 => squareFirst rs
        | 4 => squareSecond rs
        | _ => mixedSum rs)
  have hformula := hc
  exact halgebra.trans ((RatPolyCoeffEqv.refl _).add hformula.symm)

def gramDeterminantCertificate {blocks : Nat} :
    (pairs : List PolyPair) →
    (hsupport : ∀ r, r ∈ pairs → SupportedQuaternionBlocks blocks r.1 ∧
      SupportedQuaternionBlocks blocks r.2) →
    Certificate blocks (gramDeterminant pairs)
  | [], _ => by
      have hzero : RatPolyCoeffEqv (gramDeterminant []) polyZero := by
        have hp : RatPolyCoeffEqv (polyMul polyZero polyZero) polyZero :=
          RatPolyCoeffEqv.mul_zero_right _
        have hn : RatPolyCoeffEqv (polyNeg (polyMul polyZero polyZero)) polyZero := by
          simpa [polyNeg, polyZero] using RatPolyCoeffEqv.neg hp
        simpa [gramDeterminant, squareFirst, squareSecond, mixedSum] using
          (hp.add hn).trans (RatPolyCoeffEqv.zero_add polyZero)
      exact Certificate.ofCoeff (hzero.trans (RatPolyCoeffEqv.zero_smul polyOne).symm)
        (.smul 0 (by decide) (Certificate.one blocks))
  | (a,b) :: rs, hs => by
      let h := hs (a,b) List.mem_cons_self
      have htail := gramDeterminantCertificate rs
        (fun r hr => hs r (List.mem_cons_of_mem (a,b) hr))
      have hcross := crossSquaresCertificate a b h.1 h.2 rs
        (fun r hr => hs r (List.mem_cons_of_mem (a,b) hr))
      exact Certificate.ofCoeff (gram_cons_eqv a b rs) (.add htail hcross)

#print axioms gramDeterminantCertificate

end YMGap.Continuum.QuaternionHaarPolynomialGramDeterminant
