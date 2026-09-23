/-
# Block-reindex transport for formal angular derivatives

This module records the finite coordinate change needed to compare a
selected-block angular energy with the literal head angular energy.  It uses
only the explicit exponent-vector reindexing and coefficient-probe equality.
No heat estimate, OS statement, or continuum claim is made here.
-/

import YMGap.Continuum.SU2QuaternionAngularDerivative
import YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
import YMGap.Continuum.SU2QuaternionAngularSupport
import YMGap.Continuum.QuaternionHaarLinearAngularEnergy
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex

namespace YMGap.Continuum.SU2QuaternionAngularReindex

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.BF4CompactActionCPOrder

local infix:50 " ≈ " => Q'.eqv

private theorem exponentAt_lowerExponentAt
    (coordinate target : Nat) (monomial : List Nat) :
    exponentAt (lowerExponentAt coordinate monomial) target =
      if coordinate = target then
        exponentAt monomial target - 1
      else exponentAt monomial target := by
  induction coordinate generalizing target monomial with
  | zero =>
      cases monomial with
      | nil =>
          cases target <;> rfl
      | cons exponent rest =>
          cases target <;> rfl
  | succ coordinate ih =>
      cases monomial with
      | nil =>
          cases target with
          | zero =>
              have hzero : coordinate + 1 ≠ 0 := by omega
              rw [if_neg hzero]
              change 0 = 0
              rfl
          | succ target =>
              by_cases h : coordinate = target
              · subst target
                rw [if_pos rfl]
                change 0 = 0
                rfl
              · have hs : coordinate + 1 ≠ target + 1 := by omega
                rw [if_neg hs]
                change 0 = 0
                rfl
      | cons exponent rest =>
          cases target with
          | zero => rfl
          | succ target =>
              simpa only [lowerExponentAt, exponentAt, Nat.succ.injEq] using
                ih target rest

private theorem lowerExponentAt_length
    (coordinate : Nat) : ∀ monomial : List Nat,
      (lowerExponentAt coordinate monomial).length = monomial.length
  | [] => by simp [lowerExponentAt]
  | _ :: rest => by
      cases coordinate with
      | zero => rfl
      | succ coordinate =>
          simp only [lowerExponentAt, List.length_cons]
          exact congrArg Nat.succ (lowerExponentAt_length coordinate rest)

private theorem block_index_eq
    (a b remainder : Nat) (hremainder : remainder < 4)
    (hleft : 4 * a ≤ 4 * b + remainder)
    (hright : 4 * b + remainder < 4 * a + 4) :
    a = b := by
  omega

private theorem natList_eq_of_length_getD_constructive
    {left right : List Nat}
    (hlength : left.length = right.length)
    (hget : ∀ coordinate, coordinate < left.length →
      left.getD coordinate 0 = right.getD coordinate 0) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons other rest =>
          have hfalse : (0 : Nat) = Nat.succ rest.length := hlength
          exact False.elim (Nat.noConfusion hfalse)
  | cons head tail ih =>
      cases right with
      | nil =>
          have hfalse : Nat.succ tail.length = (0 : Nat) := hlength
          exact False.elim (Nat.noConfusion hfalse)
      | cons other rest =>
          have hhead : head = other := by
            have hzero := hget 0 (by
              change 0 < Nat.succ tail.length
              exact Nat.zero_lt_succ _)
            change head = other at hzero
            exact hzero
          have htailLength : tail.length = rest.length := by
            exact Nat.succ.inj hlength
          have htailGet : ∀ coordinate, coordinate < tail.length →
              tail.getD coordinate 0 = rest.getD coordinate 0 := by
            intro coordinate hcoordinate
            have hsucc := hget (coordinate + 1) (by
              change Nat.succ coordinate < Nat.succ tail.length
              exact Nat.succ_lt_succ hcoordinate)
            change tail.getD coordinate 0 = rest.getD coordinate 0 at hsucc
            exact hsucc
          have htail := ih htailLength htailGet
          cases hhead
          cases htail
          rfl

private theorem coordinate_reindex_injective
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    {left right : Nat}
    (hleft : left < 4 * blocks) (hright : right < 4 * blocks)
    (heq : 4 * s.map (left / 4) + left % 4 =
      4 * s.map (right / 4) + right % 4) :
    left = right := by
  have hleftBlock : left / 4 < blocks := by omega
  have hrightBlock : right / 4 < blocks := by omega
  have hleftComponent : left % 4 < 4 := Nat.mod_lt _ (by decide)
  have hrightComponent : right % 4 < 4 := Nat.mod_lt _ (by decide)
  have hblock : s.map (left / 4) = s.map (right / 4) := by
    apply block_index_eq (s.map (left / 4)) (s.map (right / 4))
      (right % 4) hrightComponent
    · calc
        4 * s.map (left / 4) ≤
            4 * s.map (left / 4) + left % 4 := Nat.le_add_right _ _
        _ = 4 * s.map (right / 4) + right % 4 := heq
    · calc
        4 * s.map (right / 4) + right % 4 =
            4 * s.map (left / 4) + left % 4 := heq.symm
        _ < 4 * s.map (left / 4) + 4 := by
          exact Nat.add_lt_add_left hleftComponent _
  have hsource : left / 4 = right / 4 :=
    s.injective_on hleftBlock hrightBlock hblock
  have hcomponent : left % 4 = right % 4 := by omega
  have hleftDecomp : 4 * (left / 4) + left % 4 = left :=
    Nat.div_add_mod left 4
  have hrightDecomp : 4 * (right / 4) + right % 4 = right :=
    Nat.div_add_mod right 4
  omega

private theorem reindex_lowerExponentAt
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (coordinate : Nat) (hcoordinate : coordinate < 4 * blocks)
    (monomial : List Nat) :
    reindexQuaternionExponents s
        (lowerExponentAt
          (4 * s.map (coordinate / 4) + coordinate % 4) monomial) =
      lowerExponentAt coordinate
        (reindexQuaternionExponents s monomial) := by
  apply natList_eq_of_length_getD_constructive
  · rw [reindexQuaternionExponents_length,
      lowerExponentAt_length,
      reindexQuaternionExponents_length]
  · intro target htarget
    have hsourceCoordinate :
        4 * s.map (coordinate / 4) + coordinate % 4 < 4 * blocks := by
      have hblock : coordinate / 4 < blocks := by omega
      have hmapblock := s.map_lt (coordinate / 4) hblock
      exact by omega
    have htarget' : target < 4 * blocks := by
      simpa only [reindexQuaternionExponents_length,
        lowerExponentAt_length] using htarget
    have heq : exponentAt
        (reindexQuaternionExponents s
          (lowerExponentAt
            (4 * s.map (coordinate / 4) + coordinate % 4) monomial)) target =
      exponentAt
        (lowerExponentAt coordinate
          (reindexQuaternionExponents s monomial)) target := by
      rw [exponentAt_reindexQuaternionExponents s _ htarget',
        exponentAt_lowerExponentAt]
      rw [exponentAt_lowerExponentAt]
      by_cases htargetCoordinate : coordinate = target
      · subst target
        rw [if_pos rfl, if_pos rfl]
        rw [exponentAt_reindexQuaternionExponents s monomial htarget']
      · rw [if_neg htargetCoordinate]
        have hnotMapped :
            4 * s.map (coordinate / 4) + coordinate % 4 ≠
              4 * s.map (target / 4) + target % 4 := by
          intro heq
          exact htargetCoordinate
            (coordinate_reindex_injective s hcoordinate htarget' heq)
        rw [if_neg hnotMapped]
        rw [exponentAt_reindexQuaternionExponents s monomial htarget']
    simpa only [exponentAt] using heq

private theorem reindex_ratDerivative_termwise
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (coordinate : Nat) (hcoordinate : coordinate < 4 * blocks) :
    ∀ polynomial : RatPoly,
      RatPolyTermwiseEqv
        (reindexQuaternionPolynomial s
          (ratDerivative
            (4 * s.map (coordinate / 4) + coordinate % 4) polynomial))
        (ratDerivative coordinate
          (reindexQuaternionPolynomial s polynomial))
  | [] => by
      exact RatPolyTermwiseEqv.refl []
  | term :: rest => by
      rcases term with ⟨monomial, coefficient⟩
      refine ⟨?_, ?_, ?_⟩
      · exact reindex_lowerExponentAt s coordinate hcoordinate monomial
      · have hexponent :=
          exponentAt_reindexQuaternionExponents s monomial hcoordinate
        exact Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_of_eq (congrArg Q'.ofNat hexponent.symm))
      · exact reindex_ratDerivative_termwise s coordinate hcoordinate rest

theorem reindex_ratDerivative
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (coordinate : Nat) (hcoordinate : coordinate < 4 * blocks)
    (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (reindexQuaternionPolynomial s
        (ratDerivative
          (4 * s.map (coordinate / 4) + coordinate % 4) polynomial))
      (ratDerivative coordinate
        (reindexQuaternionPolynomial s polynomial)) := by
  intro weight
  exact ratWeightedSum_termwise_eqv weight
    (reindex_ratDerivative_termwise s coordinate hcoordinate polynomial)

/-! ## Prefix-safe angular transport -/

private theorem termwise_prefix_eqv
    {blocks : Nat} : ∀ {left right : RatPoly},
      RatPolyTermwiseEqv left right →
        QuaternionPrefixPolynomialEqv blocks left right
  | [], [], _ => .nil
  | left :: leftRest, right :: rightRest, h =>
      .cons
        ⟨h.2.1, fun _ _ => by rw [h.1]⟩
        (termwise_prefix_eqv h.2.2)

private theorem reindex_ratDerivative_prefix
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (coordinate : Nat) (hcoordinate : coordinate < 4 * blocks)
    (polynomial : RatPoly) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s
        (ratDerivative
          (4 * s.map (coordinate / 4) + coordinate % 4) polynomial))
      (ratDerivative coordinate
        (reindexQuaternionPolynomial s polynomial)) :=
  termwise_prefix_eqv
    (reindex_ratDerivative_termwise s coordinate hcoordinate polynomial)

private theorem reindex_polyVar_prefix
    {blocks target source component : Nat}
    (permutation : QuaternionBlockInvolution blocks)
    (htarget : target < blocks) (hcomponent : component < 4)
    (hmap : permutation.map target = source) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial permutation
        (polyVar (4 * source + component)))
      (polyVar (4 * target + component)) := by
  change QuaternionPrefixPolynomialEqv blocks
    [(_, 1)] [(YMGap.Continuum.RingNormaliser.varMono
      (4 * target + component), 1)]
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.eqv_refl 1
    · intro coordinate hcoordinate
      rw [exponentAt_reindexQuaternionExponents permutation _ hcoordinate,
        exponentAt_varMono, exponentAt_varMono]
      have hblock : coordinate / 4 < blocks := by omega
      have hcomponentCoordinate : coordinate % 4 < 4 :=
        Nat.mod_lt coordinate (by omega)
      by_cases heq :
          4 * permutation.map (coordinate / 4) + coordinate % 4 =
            4 * source + component
      · rw [if_pos heq]
        have hmapped : permutation.map (coordinate / 4) = source := by
          omega
        have hsourceBlock : coordinate / 4 = target :=
          permutation.injective_on hblock htarget
            (hmapped.trans hmap.symm)
        have hcoordinateDecomp :
            4 * (coordinate / 4) + coordinate % 4 = coordinate := by
          omega
        have hcomponentEq : coordinate % 4 = component := by omega
        rw [if_pos]
        omega
      · rw [if_neg heq]
        rw [if_neg]
        intro hcoordinateEq
        subst coordinate
        have hdiv : (4 * target + component) / 4 = target := by omega
        have hmod : (4 * target + component) % 4 = component := by omega
        rw [hdiv, hmod, hmap] at heq
        exact heq rfl
  · exact .nil

private theorem six_prefix
    {blocks : Nat} {left right : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 →
      QuaternionPrefixPolynomialEqv blocks (left i j) (right i j)) :
    QuaternionPrefixPolynomialEqv blocks (six left) (six right) := by
  unfold six
  exact (h 0 1 (by decide) (by decide)).append
    ((h 0 2 (by decide) (by decide)).append
      ((h 0 3 (by decide) (by decide)).append
        ((h 1 2 (by decide) (by decide)).append
          ((h 1 3 (by decide) (by decide)).append
            (h 2 3 (by decide) (by decide))))))

private theorem six_supported
    {blocks : Nat} {f : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 →
      SupportedQuaternionBlocks blocks (f i j)) :
    SupportedQuaternionBlocks blocks (six f) := by
  unfold six
  exact polyAdd_supported (h 0 1 (by decide) (by decide))
    (polyAdd_supported (h 0 2 (by decide) (by decide))
      (polyAdd_supported (h 0 3 (by decide) (by decide))
        (polyAdd_supported (h 1 2 (by decide) (by decide))
          (polyAdd_supported (h 1 3 (by decide) (by decide))
            (h 2 3 (by decide) (by decide))))))

def blockAngularDerivative (block i j : Nat) (polynomial : RatPoly) : RatPoly :=
  angularDerivative (4 * block + i) (4 * block + j) polynomial

def blockAngularSquare (block : Nat) (polynomial : RatPoly) : RatPoly :=
  six (fun i j =>
    polyMul (blockAngularDerivative block i j polynomial)
      (blockAngularDerivative block i j polynomial))

private theorem blockAngularSquare_supported
    {blocks block : Nat} (hblock : block < blocks)
    {polynomial : RatPoly} (hpolynomial : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks (blockAngularSquare block polynomial) := by
  apply six_supported
  intro i j hi hj
  exact supported_polyMul
    (angularDerivative_supported_at (by omega) (by omega) hpolynomial)
    (angularDerivative_supported_at (by omega) (by omega) hpolynomial)

private theorem reindex_blockAngularDerivative_prefix
    {blocks block i j : Nat} (s : QuaternionBlockInvolution blocks)
    (hblock : block < blocks) (hi : i < 4) (hj : j < 4)
    (polynomial : RatPoly) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s
        (blockAngularDerivative (s.map block) i j polynomial))
      (blockAngularDerivative block i j
        (reindexQuaternionPolynomial s polynomial)) := by
  unfold blockAngularDerivative angularDerivative
  have hcoordinate_i : 4 * block + i < 4 * blocks := by omega
  have hcoordinate_j : 4 * block + j < 4 * blocks := by omega
  have hsource_i : (4 * block + i) / 4 = block := by omega
  have hsource_j : (4 * block + j) / 4 = block := by omega
  have hcomponent_i : (4 * block + i) % 4 = i := by omega
  have hcomponent_j : (4 * block + j) % 4 = j := by omega
  have hvar_i := reindex_polyVar_prefix s hblock hi rfl
  have hvar_j := reindex_polyVar_prefix s hblock hj rfl
  have hderiv_i := reindex_ratDerivative_prefix s
    (4 * block + i) hcoordinate_i polynomial
  have hderiv_j := reindex_ratDerivative_prefix s
    (4 * block + j) hcoordinate_j polynomial
  rw [hsource_i, hcomponent_i] at hderiv_i
  rw [hsource_j, hcomponent_j] at hderiv_j
  rw [reindexQuaternionPolynomial_add,
    reindexQuaternionPolynomial_mul,
    reindexQuaternionPolynomial_smul,
    reindexQuaternionPolynomial_mul]
  exact (hvar_i.mul hderiv_j).append
    ((hvar_j.mul hderiv_i).smul (-1))

/- The selected-block energy after recoding is the Haar image of the
   corresponding original block energy.  This is the padded-safe replacement
   for a false raw coefficient equality. -/
theorem reindex_blockAngularSquare_haar
    {blocks block : Nat} (s : QuaternionBlockInvolution blocks)
    (hblock : block < blocks) (polynomial : RatPoly) :
    quaternionHaar blocks
        (reindexQuaternionPolynomial s
          (blockAngularSquare (s.map block) polynomial)) ≈
      quaternionHaar blocks
        (blockAngularSquare block
          (reindexQuaternionPolynomial s polynomial)) := by
  have hprefix : QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s
        (blockAngularSquare (s.map block) polynomial))
      (blockAngularSquare block
        (reindexQuaternionPolynomial s polynomial)) := by
    simpa only [blockAngularSquare, blockAngularDerivative, six,
      reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_mul] using
      (six_prefix (fun i j hi hj =>
        (reindex_blockAngularDerivative_prefix s hblock hi hj polynomial).mul
          (reindex_blockAngularDerivative_prefix s hblock hi hj polynomial)))
  exact quaternionHaar_prefixPolynomialEqv blocks hprefix
    (reindex_supported s
      (blockAngularSquare (s.map block) polynomial))
    (blockAngularSquare_supported hblock
      (reindex_supported s polynomial))

end YMGap.Continuum.SU2QuaternionAngularReindex

#print axioms YMGap.Continuum.SU2QuaternionAngularReindex.reindex_ratDerivative
#print axioms YMGap.Continuum.SU2QuaternionAngularReindex.reindex_blockAngularSquare_haar
