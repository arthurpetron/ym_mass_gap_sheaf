/-
# Spectator projections commute with a translated quaternion head

The translated head uses only blocks zero and one.  Integration in any
later block therefore commutes coefficientwise with the actual finite
polynomial substitution.  This is an algebraic statement about the raw
polynomial carrier, not a change-of-measure or small-coupling estimate.
-/

import YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra

namespace YMGap.Continuum.SU2QuaternionTranslationSpectatorProjection

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (exponentAt_drop)

local infix:50 " ≈ " => Q'.eqv

private structure QuaternionIndependent (block : Nat) (q : PolyQuaternion) : Prop where
  scalar : QuaternionBlockIndependent block q.scalar
  iPart : QuaternionBlockIndependent block q.iPart
  jPart : QuaternionBlockIndependent block q.jPart
  kPart : QuaternionBlockIndependent block q.kPart

private theorem coordinate_independent {block slot : Nat} (hne : slot ≠ block) :
    QuaternionIndependent block (PolyQuaternion.coordinateVariable slot) := by
  constructor
  · change QuaternionBlockIndependent block (polyVar (4*slot+0))
    exact quaternionBlockIndependent_polyVar_of_distinctBlock hne (by decide : 0 < 4)
  · exact quaternionBlockIndependent_polyVar_of_distinctBlock hne (by decide : 1 < 4)
  · exact quaternionBlockIndependent_polyVar_of_distinctBlock hne (by decide : 2 < 4)
  · exact quaternionBlockIndependent_polyVar_of_distinctBlock hne (by decide : 3 < 4)

private theorem mul_independent {block : Nat} {p q : PolyQuaternion}
    (hp : QuaternionIndependent block p) (hq : QuaternionIndependent block q) :
    QuaternionIndependent block (PolyQuaternion.mul p q) := by
  constructor
  · exact quaternionBlockIndependent_polyAdd
      (quaternionBlockIndependent_polyMul hp.scalar hq.scalar)
      (quaternionBlockIndependent_polyNeg
        (quaternionBlockIndependent_polyAdd
          (quaternionBlockIndependent_polyMul hp.iPart hq.iPart)
          (quaternionBlockIndependent_polyAdd
            (quaternionBlockIndependent_polyMul hp.jPart hq.jPart)
            (quaternionBlockIndependent_polyMul hp.kPart hq.kPart))))
  · exact quaternionBlockIndependent_polyAdd
      (quaternionBlockIndependent_polyMul hp.scalar hq.iPart)
      (quaternionBlockIndependent_polyAdd
        (quaternionBlockIndependent_polyMul hp.iPart hq.scalar)
        (quaternionBlockIndependent_polyAdd
          (quaternionBlockIndependent_polyMul hp.jPart hq.kPart)
          (quaternionBlockIndependent_polyNeg
            (quaternionBlockIndependent_polyMul hp.kPart hq.jPart))))
  · exact quaternionBlockIndependent_polyAdd
      (quaternionBlockIndependent_polyMul hp.scalar hq.jPart)
      (quaternionBlockIndependent_polyAdd
        (quaternionBlockIndependent_polyMul hp.jPart hq.scalar)
        (quaternionBlockIndependent_polyAdd
          (quaternionBlockIndependent_polyMul hp.kPart hq.iPart)
          (quaternionBlockIndependent_polyNeg
            (quaternionBlockIndependent_polyMul hp.iPart hq.kPart))))
  · exact quaternionBlockIndependent_polyAdd
      (quaternionBlockIndependent_polyMul hp.scalar hq.kPart)
      (quaternionBlockIndependent_polyAdd
        (quaternionBlockIndependent_polyMul hp.kPart hq.scalar)
        (quaternionBlockIndependent_polyAdd
          (quaternionBlockIndependent_polyMul hp.iPart hq.jPart)
          (quaternionBlockIndependent_polyNeg
            (quaternionBlockIndependent_polyMul hp.jPart hq.iPart))))

private theorem translated_independent (right : Bool) (block : Nat)
    (hblock : 2 ≤ block) :
    QuaternionIndependent block
      (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) := by
  cases right with
  | false =>
      exact mul_independent
        (coordinate_independent (by omega : 1 ≠ block))
        (coordinate_independent (by omega : 0 ≠ block))
  | true =>
      exact mul_independent
        (coordinate_independent (by omega : 0 ≠ block))
        (coordinate_independent (by omega : 1 ≠ block))

private theorem pow_independent {block : Nat} {p : RatPoly}
    (hp : QuaternionBlockIndependent block p) :
    ∀ degree, QuaternionBlockIndependent block (ratPolyPow p degree)
  | 0 => quaternionBlockIndependent_polyOne block
  | degree + 1 => quaternionBlockIndependent_polyMul
      (pow_independent hp degree) hp

private theorem translatedHeadMonomial_independent
    (right : Bool) (block : Nat) (hblock : 2 ≤ block)
    (e0 e1 e2 e3 : Nat) :
    QuaternionBlockIndependent block
      (translatedHeadMonomial
        (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion)
        e0 e1 e2 e3) := by
  have hq := translated_independent right block hblock
  unfold translatedHeadMonomial
  exact quaternionBlockIndependent_polyMul
    (pow_independent hq.scalar e0)
    (quaternionBlockIndependent_polyMul
      (pow_independent hq.iPart e1)
      (quaternionBlockIndependent_polyMul
        (pow_independent hq.jPart e2)
        (pow_independent hq.kPart e3)))

private theorem exponentAt_headTail (monomial : List Nat) (coordinate : Nat)
    (hcoordinate : 4 ≤ coordinate) :
    exponentAt ([0, 0, 0, 0] ++ monomial.drop 4) coordinate =
      exponentAt monomial coordinate := by
  have hsplit : coordinate = 4 + (coordinate - 4) := by omega
  rw [hsplit]
  simp only [List.cons_append, List.nil_append]
  have hprefix :
      exponentAt (0 :: 0 :: 0 :: 0 :: monomial.drop 4)
          (4 + (coordinate - 4)) =
        exponentAt (monomial.drop 4) (coordinate - 4) := by
    unfold exponentAt
    rw [Nat.add_comm 4 (coordinate - 4)]
    rfl
  rw [hprefix]
  exact exponentAt_drop monomial 4 (coordinate - 4)

private theorem moment_headTail (block : Nat) (hblock : 2 ≤ block)
    (monomial : List Nat) :
    quaternionBlockMoment block ([0, 0, 0, 0] ++ monomial.drop 4) =
      quaternionBlockMoment block monomial := by
  unfold quaternionBlockMoment
  rw [exponentAt_headTail monomial (4 * block) (by omega),
    exponentAt_headTail monomial (4 * block + 1) (by omega),
    exponentAt_headTail monomial (4 * block + 2) (by omega),
    exponentAt_headTail monomial (4 * block + 3) (by omega)]

private theorem clear_headTail (block : Nat) (hblock : 2 ≤ block)
    (monomial : List Nat) :
    clearQuaternionBlock block ([0, 0, 0, 0] ++ monomial.drop 4) =
      [0, 0, 0, 0] ++ (clearQuaternionBlock block monomial).drop 4 := by
  have h0 : ¬ coordinateInQuaternionBlock block 0 := by
    unfold coordinateInQuaternionBlock
    omega
  have h1 : ¬ coordinateInQuaternionBlock block 1 := by
    unfold coordinateInQuaternionBlock
    omega
  have h2 : ¬ coordinateInQuaternionBlock block 2 := by
    unfold coordinateInQuaternionBlock
    omega
  have h3 : ¬ coordinateInQuaternionBlock block 3 := by
    unfold coordinateInQuaternionBlock
    omega
  unfold clearQuaternionBlock
  rw [clearQuaternionBlockFrom_drop block 0 monomial 4]
  simp only [List.cons_append, List.nil_append, clearQuaternionBlockFrom,
    h0, h1, h2, h3, if_false]

private theorem project_headTail_term (block : Nat) (hblock : 2 ≤ block)
    (term : RatTerm) :
    RatPolyCoeffEqv (project block (headTailLiftTerm term))
      (headTailLiftTerm (integrateQuaternionBlockTerm block term)) := by
  have ht : RatPolyTermwiseEqv
      (project block (headTailLiftTerm term))
      (headTailLiftTerm (integrateQuaternionBlockTerm block term)) := by
    refine ⟨clear_headTail block hblock term.1, ?_, True.intro⟩
    change term.2 *
        quaternionBlockMoment block ([0, 0, 0, 0] ++ term.1.drop 4) ≈
      term.2 * quaternionBlockMoment block term.1
    rw [moment_headTail block hblock term.1]
    exact Q'.eqv_refl _
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

private theorem project_translatedHeadTerm (right : Bool) (block : Nat)
    (hblock : 2 ≤ block) (term : RatTerm) :
    RatPolyCoeffEqv
      (project block
        (translatedHeadTerm
          (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion)
          term))
      (translatedHeadTerm
        (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion)
        (integrateQuaternionBlockTerm block term)) := by
  let q := if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion
  let m := translatedHeadMonomial q
    (exponentAt term.1 0) (exponentAt term.1 1)
    (exponentAt term.1 2) (exponentAt term.1 3)
  have hm : QuaternionBlockIndependent block m :=
    translatedHeadMonomial_independent right block hblock _ _ _ _
  have he (component : Nat) (hc : component < 4) :
      exponentAt (clearQuaternionBlock block term.1) component =
        exponentAt term.1 component := by
    simpa only [Nat.mul_zero, Nat.zero_add] using
      (exponentAt_clearQuaternionBlock_of_ne term.1
        (source := 0) (target := block) (by omega : 0 ≠ block) hc)
  have htranslated : RatPolyCoeffEqv
      (translatedHeadTerm q (integrateQuaternionBlockTerm block term))
      (polyMul m (headTailLiftTerm (integrateQuaternionBlockTerm block term))) := by
    simp only [translatedHeadTerm, integrateQuaternionBlockTerm]
    rw [he 0 (by decide), he 1 (by decide),
      he 2 (by decide), he 3 (by decide)]
    exact RatPolyCoeffEqv.refl _
  exact ((project_mul_of_independent block m (headTailLiftTerm term) hm).trans
    ((project_headTail_term block hblock term).mul_left m)).trans htranslated.symm

/-- A spectator block at index at least two commutes coefficientwise with
either order of translated-head quaternion multiplication, for every raw
finite polynomial and every degree. -/
theorem project_translatedHeadPolynomial (right : Bool) (block : Nat)
    (hblock : 2 ≤ block) : ∀ polynomial : RatPoly,
    RatPolyCoeffEqv
      (project block
        (translatedHeadPolynomial
          (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion)
          polynomial))
      (translatedHeadPolynomial
        (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion)
        (project block polynomial))
  | [] => RatPolyCoeffEqv.refl _
  | term :: rest => by
      change RatPolyCoeffEqv
        (project block
          (polyAdd
            (translatedHeadTerm _ term)
            (translatedHeadPolynomial _ rest)))
        (polyAdd
          (translatedHeadTerm _ (integrateQuaternionBlockTerm block term))
          (translatedHeadPolynomial _ (project block rest)))
      rw [project_add]
      exact RatPolyCoeffEqv.add
        (project_translatedHeadTerm right block hblock term)
        (project_translatedHeadPolynomial right block hblock rest)

#print axioms project_translatedHeadPolynomial

end YMGap.Continuum.SU2QuaternionTranslationSpectatorProjection
