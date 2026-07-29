/-
# Completely-positive polynomial order for the compact BF4 complement

This file consumes three exact layers:

* arbitrary-degree positivity of normalized Haar on `SU(2)^10`;
* four-factor Fubini permutation under arbitrary-product Haar;
* the checked signed-edge SOS certificate for the cleared BF4 complement.

It proves that multiplication by the sphere-relative complement is positive
on every polynomial square.  Equivalently, for every supported polynomial
`P`,

  H_10(P^2 * [480 (133/4 - A)]) >= 0.

This is the finite, all-label CP-order theorem needed by the shifted
Feynman--Kac exponential.  There is no degree or spin cutoff.
-/

import YMGap.Continuum.BF4CompactActionDiagonalSOS
import YMGap.Continuum.SU2QuaternionArbitraryHaarFourSwap

namespace YMGap.Continuum.BF4CompactActionCPOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarFourSwap
open YMGap.Continuum.SU2QuaternionHaarRingNormalizer
open YMGap.Continuum.BF4CompactActionDiagonalSOS

local infix:50 " ≈ " => Q'.eqv

/-- Compile one nonnegatively weighted linear square. -/
def polynomialSOSEntry
    (entry : Int × PolyExpr) : RatPoly :=
  let linear := exprToRatPoly entry.2
  polySmul (Q'.ofInt entry.1)
    (polyMul linear linear)

/-- The exposed diagonal-dominance carrier as a literal polynomial sum of
squares. -/
def compactActionComplementSOSPolynomial : RatPoly :=
  compactActionComplementSOSEntries.foldr
    (fun entry total =>
      polyAdd (polynomialSOSEntry entry) total)
    (exprToRatPoly (.const 0))

/-- The direct polynomial SOS is exactly the compiler output of the checked
certificate expression. -/
theorem compactActionComplementSOSPolynomial_eq :
    compactActionComplementSOSPolynomial =
      exprToRatPoly compactActionComplementSOSExpr := by
  decide

theorem quaternionHaar_append
    (blocks : Nat) :
    ∀ left right : RatPoly,
      quaternionHaar blocks (left ++ right) ≈
        quaternionHaar blocks left +
          quaternionHaar blocks right
  | [], right =>
      Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | term :: rest, right => by
      change
        term.2 * quaternionHaarMono blocks term.1 +
            quaternionHaar blocks (rest ++ right) ≈
          (term.2 * quaternionHaarMono blocks term.1 +
              quaternionHaar blocks rest) +
            quaternionHaar blocks right
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (quaternionHaar_append
            blocks rest right))
        (Q'.eqv_symm
          (Q'.add_assoc_eqv _ _ _))

/-- Exact product Haar is linear under rational scalar multiplication. -/
theorem quaternionHaar_polySmul
    (blocks : Nat) (coefficient : Q') :
    ∀ polynomial : RatPoly,
      quaternionHaar blocks
          (polySmul coefficient polynomial) ≈
        coefficient *
          quaternionHaar blocks polynomial
  | [] =>
      Q'.eqv_symm (Q'.mul_zero_eqv coefficient)
  | term :: rest => by
      change
        (coefficient * term.2) *
              quaternionHaarMono blocks term.1 +
            quaternionHaar blocks
              (polySmul coefficient rest) ≈
          coefficient *
            (term.2 *
                quaternionHaarMono blocks term.1 +
              quaternionHaar blocks rest)
      refine Q'.eqv_trans _
        (coefficient *
              (term.2 *
                quaternionHaarMono blocks term.1) +
            coefficient *
              quaternionHaar blocks rest) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_assoc_eqv coefficient term.2
            (quaternionHaarMono blocks term.1))
          (quaternionHaar_polySmul
            blocks coefficient rest)
      · exact Q'.eqv_symm
          (Q'.mul_add_eqv coefficient _ _)

/-- Multiplication by the literal polynomial unit is invisible to exact
product Haar. -/
theorem quaternionHaar_polyMul_one_right
    (blocks : Nat) :
    ∀ polynomial : RatPoly,
      quaternionHaar blocks
          (polyMul polynomial polyOne) ≈
        quaternionHaar blocks polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        (term.2 * 1) *
              quaternionHaarMono blocks
                (monoMul term.1 []) +
            quaternionHaar blocks
              (polyMul rest polyOne) ≈
          term.2 *
              quaternionHaarMono blocks term.1 +
            quaternionHaar blocks rest
      have hmono :
          monoMul term.1 [] = term.1 := by
        cases term.1 <;> rfl
      rw [hmono]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_one_eqv term.2))
        (quaternionHaar_polyMul_one_right
          blocks rest)

private theorem quaternionHaar_polyMul_add_left
    (blocks : Nat) (left right third : RatPoly) :
    quaternionHaar blocks
        (polyMul (polyAdd left right) third) ≈
      quaternionHaar blocks (polyMul left third) +
        quaternionHaar blocks (polyMul right third) := by
  simp only [polyAdd, polyMul, List.flatMap_append]
  exact quaternionHaar_append blocks _ _

theorem quaternionHaar_polyMul_add_right
    (blocks : Nat) (first left right : RatPoly) :
    quaternionHaar blocks
        (polyMul first (polyAdd left right)) ≈
      quaternionHaar blocks (polyMul first left) +
        quaternionHaar blocks (polyMul first right) := by
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyAdd left right) first)) _
    (quaternionHaar_polyMul_comm
      blocks first (polyAdd left right)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul left first) +
      quaternionHaar blocks (polyMul right first)) _
    (quaternionHaar_polyMul_add_left
      blocks left right first) ?_
  exact QPoly.q_add_congr
    (quaternionHaar_polyMul_comm
      blocks left first)
    (quaternionHaar_polyMul_comm
      blocks right first)

private theorem quaternionHaarRow_smul_source
    (blocks : Nat) (coefficient : Q')
    (source : RatTerm) :
    ∀ right : RatPoly,
      quaternionHaarRow blocks
          (source.1, coefficient * source.2) right ≈
        coefficient *
          quaternionHaarRow blocks source right
  | [] =>
      Q'.eqv_symm
        (Q'.mul_zero_eqv coefficient)
  | target :: rest => by
      change
        ((coefficient * source.2) * target.2) *
              quaternionHaarMono blocks
                (monoMul source.1 target.1) +
            quaternionHaarRow blocks
              (source.1, coefficient * source.2)
              rest ≈
          coefficient *
            ((source.2 * target.2) *
                quaternionHaarMono blocks
                  (monoMul source.1 target.1) +
              quaternionHaarRow blocks source rest)
      refine Q'.eqv_trans _
        (coefficient *
              ((source.2 * target.2) *
                quaternionHaarMono blocks
                  (monoMul source.1 target.1)) +
            coefficient *
              quaternionHaarRow blocks source rest) _ ?_ ?_
      · exact QPoly.q_add_congr
          (Q'.eqv_trans _ _ _
            (Q'.mul_assoc_eqv _ _ _)
            (Q'.eqv_trans _ _ _
              (Q'.mul_assoc_eqv _ _ _)
              (Q'.mul_eqv_congr_left _ _ _
                (Q'.eqv_symm
                  (Q'.mul_assoc_eqv _ _ _)))))
          (quaternionHaarRow_smul_source
            blocks coefficient source rest)
      · exact Q'.eqv_symm
          (Q'.mul_add_eqv _ _ _)

private theorem quaternionHaarBilinear_smul_left
    (blocks : Nat) (coefficient : Q') :
    ∀ left right : RatPoly,
      quaternionHaarBilinear blocks
          (polySmul coefficient left) right ≈
        coefficient *
          quaternionHaarBilinear blocks left right
  | [], right =>
      Q'.eqv_symm
        (Q'.mul_zero_eqv coefficient)
  | source :: rest, right => by
      change
        quaternionHaarRow blocks
              (source.1, coefficient * source.2) right +
            quaternionHaarBilinear blocks
              (polySmul coefficient rest) right ≈
          coefficient *
            (quaternionHaarRow blocks source right +
              quaternionHaarBilinear blocks rest right)
      refine Q'.eqv_trans _
        (coefficient *
              quaternionHaarRow blocks source right +
            coefficient *
              quaternionHaarBilinear blocks rest right) _ ?_ ?_
      · exact QPoly.q_add_congr
          (quaternionHaarRow_smul_source
            blocks coefficient source right)
          (quaternionHaarBilinear_smul_left
            blocks coefficient rest right)
      · exact Q'.eqv_symm
          (Q'.mul_add_eqv _ _ _)

private theorem quaternionHaar_polyMul_smul_left
    (blocks : Nat) (coefficient : Q')
    (left right : RatPoly) :
    quaternionHaar blocks
        (polyMul (polySmul coefficient left) right) ≈
      coefficient *
        quaternionHaar blocks
          (polyMul left right) := by
  refine Q'.eqv_trans _
    (quaternionHaarBilinear blocks
      (polySmul coefficient left) right) _
    (quaternionHaar_polyMul
      blocks (polySmul coefficient left) right) ?_
  refine Q'.eqv_trans _
    (coefficient *
      quaternionHaarBilinear blocks left right) _
    (quaternionHaarBilinear_smul_left
      blocks coefficient left right) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm
      (quaternionHaar_polyMul
        blocks left right))

theorem quaternionHaar_polyMul_smul_right
    (blocks : Nat) (coefficient : Q')
    (left right : RatPoly) :
    quaternionHaar blocks
        (polyMul left
          (polySmul coefficient right)) ≈
      coefficient *
        quaternionHaar blocks
          (polyMul left right) := by
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polySmul coefficient right)
        left)) _
    (quaternionHaar_polyMul_comm
      blocks left
        (polySmul coefficient right)) ?_
  refine Q'.eqv_trans _
    (coefficient *
      quaternionHaar blocks
        (polyMul right left)) _
    (quaternionHaar_polyMul_smul_left
      blocks coefficient right left) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (quaternionHaar_polyMul_comm
      blocks right left)

theorem supported_polyMul
    {blocks : Nat} {left right : RatPoly}
    (hleft : SupportedQuaternionBlocks blocks left)
    (hright : SupportedQuaternionBlocks blocks right) :
    SupportedQuaternionBlocks blocks
      (polyMul left right) := by
  have monoMul_drop_of_length_le
      (first second : List Nat) (coordinates : Nat)
      (hsecond : second.length ≤ coordinates) :
      (monoMul first second).drop coordinates =
        first.drop coordinates := by
    induction coordinates generalizing first second with
    | zero =>
        cases second with
        | nil => cases first <;> rfl
        | cons _ rest => simp at hsecond
    | succ coordinates induction =>
        cases first with
        | nil =>
            simp only [monoMul]
            exact List.drop_eq_nil_of_le hsecond
        | cons x xs =>
            cases second with
            | nil => simp [monoMul]
            | cons y ys =>
                simp only [List.length_cons] at hsecond
                simp [monoMul,
                  induction xs ys (by omega)]
  have monoMul_length_le_local
      {first second : List Nat} {coordinates : Nat}
      (hfirst : first.length ≤ coordinates)
      (hsecond : second.length ≤ coordinates) :
      (monoMul first second).length ≤ coordinates := by
    apply List.drop_eq_nil_iff.mp
    rw [monoMul_drop_of_length_le
      first second coordinates hsecond]
    exact List.drop_eq_nil_of_le hfirst
  have mem_polyMul_local
      {first second : RatPoly} {term : RatTerm}
      (hterm : term ∈ polyMul first second) :
      ∃ firstTerm, firstTerm ∈ first ∧
        ∃ secondTerm, secondTerm ∈ second ∧
          term =
            (monoMul firstTerm.1 secondTerm.1,
              firstTerm.2 * secondTerm.2) := by
    unfold polyMul at hterm
    rw [List.mem_flatMap] at hterm
    obtain ⟨firstTerm, hfirst, hterm⟩ := hterm
    rw [List.mem_map] at hterm
    obtain ⟨secondTerm, hsecond, rfl⟩ := hterm
    exact ⟨firstTerm, hfirst,
      secondTerm, hsecond, rfl⟩
  intro term hterm
  obtain ⟨leftTerm, hleftTerm,
      rightTerm, hrightTerm, rfl⟩ :=
    mem_polyMul_local hterm
  exact monoMul_length_le_local
    (hleft leftTerm hleftTerm)
    (hright rightTerm hrightTerm)

def polynomialSupportedBool
    (blocks : Nat) (polynomial : RatPoly) : Bool :=
  polynomial.all fun term =>
    decide (term.1.length ≤ 4 * blocks)

theorem supported_of_bool
    (blocks : Nat) (polynomial : RatPoly)
    (hsupported :
      polynomialSupportedBool blocks polynomial = true) :
    SupportedQuaternionBlocks blocks polynomial := by
  intro term hterm
  have hdecision :=
    List.all_eq_true.mp hsupported term hterm
  exact of_decide_eq_true hdecision

/-- Every linear form in the fixed certificate uses only the retained forty
coordinates. -/
theorem compactActionComplementSOSEntries_supported :
    ∀ entry,
      entry ∈ compactActionComplementSOSEntries →
        SupportedQuaternionBlocks 10
          (exprToRatPoly entry.2) := by
  have hall :
      compactActionComplementSOSEntries.all
        (fun entry =>
          polynomialSupportedBool 10
            (exprToRatPoly entry.2)) = true := by
    decide
  intro entry hentry
  exact supported_of_bool 10
    (exprToRatPoly entry.2)
    (List.all_eq_true.mp hall entry hentry)

theorem one_sos_entry_nonnegative
    (blocks : Nat)
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks blocks polynomial)
    (entry : Int × PolyExpr)
    (hweight : (0 : Int) ≤ entry.1)
    (hlinear :
      SupportedQuaternionBlocks blocks
        (exprToRatPoly entry.2)) :
    (0 : Q') ≤
      quaternionHaar blocks
        (polyMul (polyMul polynomial polynomial)
          (polynomialSOSEntry entry)) := by
  let linear := exprToRatPoly entry.2
  have hsquare :
      (0 : Q') ≤
        quaternionHaar blocks
          (polyMul
            (polyMul polynomial linear)
            (polyMul polynomial linear)) :=
    quaternionHaar_square_nonnegative
      blocks
      (polyMul polynomial linear)
      (supported_polyMul hsupport hlinear)
  have hfour :
      quaternionHaar blocks
          (polyMul
            (polyMul polynomial polynomial)
            (polyMul linear linear)) ≈
        quaternionHaar blocks
          (polyMul
            (polyMul polynomial linear)
            (polyMul polynomial linear)) :=
    quaternionHaar_polyMul_four_swap
      blocks polynomial polynomial linear linear
  have hcoefficient :
      (0 : Q') ≤ Q'.ofInt entry.1 := by
    rw [Q'.zero_le_iff_num_nonneg]
    exact hweight
  have hscaled :
      (0 : Q') ≤
        Q'.ofInt entry.1 *
          quaternionHaar blocks
            (polyMul
              (polyMul polynomial polynomial)
              (polyMul linear linear)) :=
    Q'.mul_nonneg _ _ hcoefficient
      (Q'.le_trans' _ _ _ hsquare
        (Q'.le_of_eqv
          (Q'.eqv_symm hfour)))
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (quaternionHaar_polyMul_smul_right
          blocks (Q'.ofInt entry.1)
          (polyMul polynomial polynomial)
          (polyMul linear linear))))

theorem sos_entries_nonnegative
    (blocks : Nat)
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks blocks polynomial) :
    ∀ entries : List (Int × PolyExpr),
      (∀ entry, entry ∈ entries →
        (0 : Int) ≤ entry.1) →
      (∀ entry, entry ∈ entries →
        SupportedQuaternionBlocks blocks
          (exprToRatPoly entry.2)) →
      (0 : Q') ≤
        quaternionHaar blocks
          (polyMul
            (polyMul polynomial polynomial)
            (entries.foldr
              (fun entry total =>
                polyAdd
                  (polynomialSOSEntry entry)
                  total)
              (exprToRatPoly (.const 0))))
  | [], _, _ => by
      change
        (0 : Q') ≤
          quaternionHaar blocks
            (polyMul
              (polyMul polynomial polynomial)
              (exprToRatPoly (.const 0)))
      have hzero :
          exprToRatPoly (.const 0) =
            [([], (0 : Q'))] := rfl
      rw [hzero]
      change
        (0 : Q') ≤
          quaternionHaar blocks
            ((polyMul
              (polyMul polynomial polynomial)
              [([], (0 : Q'))]))
      -- Multiplication by the literal zero coefficient has zero Haar value.
      induction (polyMul polynomial polynomial) with
      | nil => exact Q'.le_refl' 0
      | cons term rest induction =>
          change
            (0 : Q') ≤
                (term.2 * 0) *
                    quaternionHaarMono blocks
                      (monoMul term.1 []) +
                quaternionHaar blocks
                  (polyMul rest [([], (0 : Q'))])
          have hterm :
              (term.2 * 0) *
                  quaternionHaarMono blocks
                    (monoMul term.1 []) ≈ 0 := by
            exact Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ _
                (Q'.mul_zero_eqv term.2))
              (Q'.zero_mul_eqv _)
          have hsum :
                  (term.2 * 0) *
                    quaternionHaarMono blocks
                      (monoMul term.1 []) +
                  quaternionHaar blocks
                    (polyMul rest [([], (0 : Q'))]) ≈
                quaternionHaar blocks
                  (polyMul rest [([], (0 : Q'))]) := by
            exact Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_right _ _ _ hterm)
              (QPoly.q_zero_add_eqv _)
          exact Q'.le_trans' _ _ _ induction
            (Q'.le_of_eqv
              (Q'.eqv_symm hsum))
  | entry :: rest, hweights, hlinear => by
      have hhead :=
        one_sos_entry_nonnegative
          blocks polynomial hsupport entry
          (hweights entry (by simp))
          (hlinear entry (by simp))
      have hrest :=
        sos_entries_nonnegative
          blocks polynomial hsupport rest
          (fun other hother =>
            hweights other (by simp [hother]))
          (fun other hother =>
            hlinear other (by simp [hother]))
      exact Q'.le_trans' _ _ _
        (Q'.zero_le_add _ _ hhead hrest)
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (quaternionHaar_polyMul_add_right
              blocks (polyMul polynomial polynomial)
              (polynomialSOSEntry entry)
              (rest.foldr
                (fun next total =>
                  polyAdd
                    (polynomialSOSEntry next)
                    total)
                (exprToRatPoly (.const 0))))))

/-- The literal diagonal-dominance SOS is positive after multiplication by
every supported polynomial square. -/
theorem compactActionComplementSOSPolynomial_cp
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    (0 : Q') ≤
      tenfoldHaar
        (polyMul (polyMul polynomial polynomial)
          compactActionComplementSOSPolynomial) := by
  exact sos_entries_nonnegative
    10 polynomial hsupport
    compactActionComplementSOSEntries
    compactActionComplementSOSEntries_nonnegative
    compactActionComplementSOSEntries_supported

/-- **All-label BF4 complement CP order.**  The checked sphere-relative
polynomial `480(133/4-A)` is nonnegative against every polynomial square
under exact normalized Haar on `SU(2)^10`. -/
theorem clearedSphereComplement_cp
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    (0 : Q') ≤
      tenfoldHaar
        (polyMul (polyMul polynomial polynomial)
          (exprToRatPoly
            clearedSphereComplementExpr)) := by
  have hnormal :
      tenfoldHaar
          (polyMul (polyMul polynomial polynomial)
            (exprToRatPoly
              clearedSphereComplementExpr)) ≈
        tenfoldHaar
          (polyMul (polyMul polynomial polynomial)
            (exprToRatPoly
              compactActionComplementSOSExpr)) :=
    quaternionHaar_mul_expr_congr_of_normal_eq
      10 clearedSphereComplementExpr
      compactActionComplementSOSExpr
      compactActionComplementSOS_normal
      (polyMul polynomial polynomial)
  have hsos :
      (0 : Q') ≤
        tenfoldHaar
          (polyMul (polyMul polynomial polynomial)
            (exprToRatPoly
              compactActionComplementSOSExpr)) := by
    rw [← compactActionComplementSOSPolynomial_eq]
    exact compactActionComplementSOSPolynomial_cp
      polynomial hsupport
  exact Q'.le_trans' _ _ _ hsos
    (Q'.le_of_eqv
      (Q'.eqv_symm hnormal))

/-- Exact reciprocal of the denominator-clearing factor. -/
def oneOver480 : Q' :=
  Q'.mkPos 1 480 (by decide)

/-- The unscaled sphere-relative BF4 action complement. -/
def compactActionComplementPolynomial : RatPoly :=
  polySmul oneOver480
    (exprToRatPoly clearedSphereComplementExpr)

/-- Normalized all-label CP order:
`H(P² * (133/4-A)) >= 0` in the ten-sphere quotient. -/
theorem compactActionComplement_cp
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    (0 : Q') ≤
      tenfoldHaar
        (polyMul (polyMul polynomial polynomial)
          compactActionComplementPolynomial) := by
  have hcleared :=
    clearedSphereComplement_cp polynomial hsupport
  have hscale :
      tenfoldHaar
          (polyMul (polyMul polynomial polynomial)
            compactActionComplementPolynomial) ≈
        oneOver480 *
          tenfoldHaar
            (polyMul (polyMul polynomial polynomial)
              (exprToRatPoly
                clearedSphereComplementExpr)) :=
    quaternionHaar_polyMul_smul_right
      10 oneOver480
      (polyMul polynomial polynomial)
      (exprToRatPoly
        clearedSphereComplementExpr)
  have hnonnegative :
      (0 : Q') ≤
        oneOver480 *
          tenfoldHaar
            (polyMul (polyMul polynomial polynomial)
              (exprToRatPoly
                clearedSphereComplementExpr)) :=
    Q'.mul_nonneg _ _
      (by decide) hcleared
  exact Q'.le_trans' _ _ _ hnonnegative
    (Q'.le_of_eqv
      (Q'.eqv_symm hscale))

end YMGap.Continuum.BF4CompactActionCPOrder

#print axioms YMGap.Continuum.BF4CompactActionCPOrder.compactActionComplementSOSPolynomial_eq
#print axioms YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_append
#print axioms YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polySmul
#print axioms YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polyMul_one_right
#print axioms YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polyMul_add_right
#print axioms YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polyMul_smul_right
#print axioms YMGap.Continuum.BF4CompactActionCPOrder.supported_polyMul
#print axioms YMGap.Continuum.BF4CompactActionCPOrder.supported_of_bool
#print axioms YMGap.Continuum.BF4CompactActionCPOrder.one_sos_entry_nonnegative
#print axioms YMGap.Continuum.BF4CompactActionCPOrder.sos_entries_nonnegative
#print axioms YMGap.Continuum.BF4CompactActionCPOrder.compactActionComplementSOSEntries_supported
#print axioms YMGap.Continuum.BF4CompactActionCPOrder.compactActionComplementSOSPolynomial_cp
#print axioms YMGap.Continuum.BF4CompactActionCPOrder.clearedSphereComplement_cp
#print axioms YMGap.Continuum.BF4CompactActionCPOrder.compactActionComplement_cp
