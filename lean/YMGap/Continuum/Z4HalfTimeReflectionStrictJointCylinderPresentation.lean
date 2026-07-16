/-
# Presentation covariance of the strict reflected cylinder Gram limit

The strict local Gram functional is initially presented using an ordered list
of canonical roots, hence on a Boolean word space whose coordinates remember
that list.  This file proves that the resulting finite quadratic and its
constructive-real limit depend only on the represented cylinder observable,
not on accidental choices in the root-list presentation.

The common mechanism is an exact recoding of local fingerprints.  Both sides
then pull back to literally the same complete-support reflection quadratic.
We specialize this to root permutations, adjacent duplicate insertion and
elimination, and the append presentation which is a common refinement of any
two finite root lists.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderPresentation

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic exact fingerprint recoding -/

/-- A target root presentation is an exact coordinate recoding of a source
presentation when this equality holds for every radius and every complete
lower-half support. -/
def StrictJointFingerprintRecoding
    (base : Nat) (sourceRoots targetRoots : List (List Nat))
    (recode : List Bool → List Bool) : Prop :=
  ∀ radius support,
    centralStrictLocalQueryCode radius base targetRoots support =
      recode
        (centralStrictLocalQueryCode radius base sourceRoots support)

/-- Exact stage covariance under any fingerprint recoding.  The two finite
quadratics may be written on Boolean spaces of different dimensions; their
pullbacks to the complete-support reflection Gram are nevertheless equal. -/
theorem centralNormalizedStrictJointFixedQuadraticSequence_eqv_of_recoding
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (sourceRoots targetRoots : List (List Nat))
    (recode : List Bool → List Bool)
    (hrecoding : StrictJointFingerprintRecoding
      base sourceRoots targetRoots recode)
    (coefficient : List Bool → Q') (stage : Nat) :
    centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base targetRoots coefficient stage ≈
      centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base sourceRoots
          (fun bits => coefficient (recode bits)) stage := by
  have htarget :=
    centralNormalizedStrictJointFixedQuadraticSequence_eqv_supportGram
      coupling hcoupling base targetRoots coefficient stage
  have hsource :=
    centralNormalizedStrictJointFixedQuadraticSequence_eqv_supportGram
      coupling hcoupling base sourceRoots
        (fun bits => coefficient (recode bits)) stage
  have hcoefficient :
      centralLocalSupportCoefficient
          (centralStrictLocalQueryCode
            (strictQueryBase base + stage) base targetRoots)
          coefficient =
        centralLocalSupportCoefficient
          (centralStrictLocalQueryCode
            (strictQueryBase base + stage) base sourceRoots)
          (fun bits => coefficient (recode bits)) := by
    funext support
    unfold centralLocalSupportCoefficient
    rw [hrecoding (strictQueryBase base + stage) support]
  rw [hcoefficient] at htarget
  exact Q'.eqv_trans _ _ _ htarget (Q'.eqv_symm hsource)

/-- Limit covariance under exact fingerprint recoding. -/
theorem centralNormalizedStrictJointFixedQuadraticLimit_equiv_of_recoding
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {sourceRoots targetRoots : List (List Nat)}
    (hsourceRoots : ∀ root, root ∈ sourceRoots →
      root ∈ canonicalSurfacePolymers base)
    (htargetRoots : ∀ root, root ∈ targetRoots →
      root ∈ canonicalSurfacePolymers base)
    (recode : List Bool → List Bool)
    (hrecoding : StrictJointFingerprintRecoding
      base sourceRoots targetRoots recode)
    (coefficient : List Bool → Q') :
    CReal.Equiv
      (centralNormalizedStrictJointFixedQuadraticLimit
        coupling hcoupling hle htargetRoots coefficient)
      (centralNormalizedStrictJointFixedQuadraticLimit
        coupling hcoupling hle hsourceRoots
          (fun bits => coefficient (recode bits))) := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have heqv :=
    centralNormalizedStrictJointFixedQuadraticSequence_eqv_of_recoding
      coupling hcoupling base sourceRoots targetRoots recode hrecoding
        coefficient stage
  have hepsilonNonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  change
    centralNormalizedStrictJointFixedQuadraticSequence
          coupling hcoupling base targetRoots coefficient stage ≤
        centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling base sourceRoots
              (fun bits => coefficient (recode bits)) stage + epsilon ∧
      centralNormalizedStrictJointFixedQuadraticSequence
          coupling hcoupling base sourceRoots
            (fun bits => coefficient (recode bits)) stage ≤
        centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling base targetRoots coefficient stage + epsilon
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative)⟩

/-! ## 2. Permuting root coordinates -/

/-- Read the first Boolean coordinate carrying a specified root.  Its fallback
clauses concern malformed words only. -/
def strictJointRootBit (root : List Nat) :
    List (List Nat) → List Bool → Bool
  | source :: sources, bit :: bits =>
      if source = root then bit
      else strictJointRootBit root sources bits
  | _, _ => false

theorem strictJointRootBit_map_of_mem
    (root : List Nat) (value : List Nat → Bool) :
    ∀ sources : List (List Nat), root ∈ sources →
      strictJointRootBit root sources (sources.map value) = value root
  | [], hroot => by
      exact (List.not_mem_nil hroot).elim
  | source :: sources, hroot => by
      by_cases heq : source = root
      · simp only [strictJointRootBit, heq, ↓reduceIte, List.map_cons]
      · have htail : root ∈ sources := by
          rcases List.mem_cons.mp hroot with hhead | htail
          · exact (heq hhead.symm).elim
          · exact htail
        simp only [strictJointRootBit, heq, ↓reduceIte, List.map_cons]
        exact strictJointRootBit_map_of_mem root value sources htail

/-- A proof-independent Boolean-coordinate transport between two root lists.
For a genuine query word, each target root reads the corresponding source
coordinate.  Repeated roots are harmless because genuine query coordinates
for equal roots agree. -/
def permuteStrictJointFingerprint
    (sourceRoots targetRoots : List (List Nat))
    (bits : List Bool) : List Bool :=
  targetRoots.map (fun root =>
    strictJointRootBit root sourceRoots bits)

/-- Under a permutation hypothesis, coordinate transport sends a mapped
source list exactly to the corresponding mapped target list. -/
theorem permuteStrictJointFingerprint_map
    {sourceRoots targetRoots : List (List Nat)}
    (hperm : sourceRoots.Perm targetRoots)
    (value : List Nat → Bool) :
    permuteStrictJointFingerprint sourceRoots targetRoots
        (sourceRoots.map value) =
      targetRoots.map value := by
  unfold permuteStrictJointFingerprint
  apply List.map_congr_left
  intro root hroot
  exact strictJointRootBit_map_of_mem root value sourceRoots
    ((hperm.mem_iff).mpr hroot)

theorem centralStrictLocalQueryCode_perm
    {base : Nat} {sourceRoots targetRoots : List (List Nat)}
    (hperm : sourceRoots.Perm targetRoots)
    (radius : Nat) (support : List Nat) :
    centralStrictLocalQueryCode radius base targetRoots support =
      permuteStrictJointFingerprint sourceRoots targetRoots
        (centralStrictLocalQueryCode
          radius base sourceRoots support) := by
  unfold centralStrictLocalQueryCode
    centralLowerSupportQueryFingerprint
    canonicalRootsSupportQueryFingerprint
    centralStrictLowerCylinderRoots
  simp only [List.map_map]
  exact (permuteStrictJointFingerprint_map hperm
    (fun root => canonicalPolymerSupportQueryEventB
      (centralAmbient radius)
      (centralStrictLowerCanonicalRoot radius base root)
      (centralLowerSupportAmbientFaces radius support))).symm

theorem strictJointFingerprintRecoding_perm
    {base : Nat} {sourceRoots targetRoots : List (List Nat)}
    (hperm : sourceRoots.Perm targetRoots) :
    StrictJointFingerprintRecoding base sourceRoots targetRoots
      (permuteStrictJointFingerprint sourceRoots targetRoots) := by
  intro radius support
  exact centralStrictLocalQueryCode_perm hperm radius support

theorem canonicalRoots_of_perm
    {base : Nat} {sourceRoots targetRoots : List (List Nat)}
    (hperm : sourceRoots.Perm targetRoots)
    (hsourceRoots : ∀ root, root ∈ sourceRoots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ root, root ∈ targetRoots →
      root ∈ canonicalSurfacePolymers base := by
  intro root hroot
  exact hsourceRoots root ((hperm.mem_iff).mpr hroot)

/-- Constructive-real covariance under an arbitrary root-list permutation. -/
theorem centralNormalizedStrictJointFixedQuadraticLimit_equiv_perm
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {sourceRoots targetRoots : List (List Nat)}
    (hperm : sourceRoots.Perm targetRoots)
    (hsourceRoots : ∀ root, root ∈ sourceRoots →
      root ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool → Q') :
    CReal.Equiv
      (centralNormalizedStrictJointFixedQuadraticLimit
        coupling hcoupling hle
          (canonicalRoots_of_perm hperm hsourceRoots) coefficient)
      (centralNormalizedStrictJointFixedQuadraticLimit
        coupling hcoupling hle hsourceRoots
          (fun bits => coefficient
            (permuteStrictJointFingerprint
              sourceRoots targetRoots bits))) := by
  exact centralNormalizedStrictJointFixedQuadraticLimit_equiv_of_recoding
    hcoupling hle hsourceRoots
      (canonicalRoots_of_perm hperm hsourceRoots)
      (permuteStrictJointFingerprint sourceRoots targetRoots)
      (strictJointFingerprintRecoding_perm hperm) coefficient

/-! ## 3. Exact duplicate insertion and elimination -/

/-- Duplicate the first coordinate of a Boolean fingerprint. -/
def duplicateHeadStrictJointFingerprint : List Bool → List Bool
  | [] => []
  | bit :: bits => bit :: bit :: bits

/-- Erase the second coordinate of a Boolean fingerprint. -/
def eraseSecondStrictJointFingerprint : List Bool → List Bool
  | first :: _ :: bits => first :: bits
  | bits => bits

theorem centralStrictLocalQueryCode_duplicateHead
    (radius base : Nat) (root : List Nat)
    (roots : List (List Nat)) (support : List Nat) :
    centralStrictLocalQueryCode radius base
        (root :: root :: roots) support =
      duplicateHeadStrictJointFingerprint
        (centralStrictLocalQueryCode radius base
          (root :: roots) support) := by
  unfold centralStrictLocalQueryCode
    centralLowerSupportQueryFingerprint
    canonicalRootsSupportQueryFingerprint
    centralStrictLowerCylinderRoots
    duplicateHeadStrictJointFingerprint
  rfl

theorem centralStrictLocalQueryCode_eraseDuplicateHead
    (radius base : Nat) (root : List Nat)
    (roots : List (List Nat)) (support : List Nat) :
    centralStrictLocalQueryCode radius base
        (root :: roots) support =
      eraseSecondStrictJointFingerprint
        (centralStrictLocalQueryCode radius base
          (root :: root :: roots) support) := by
  unfold centralStrictLocalQueryCode
    centralLowerSupportQueryFingerprint
    canonicalRootsSupportQueryFingerprint
    centralStrictLowerCylinderRoots
    eraseSecondStrictJointFingerprint
  rfl

theorem strictJointFingerprintRecoding_duplicateHead
    (base : Nat) (root : List Nat) (roots : List (List Nat)) :
    StrictJointFingerprintRecoding base
      (root :: roots) (root :: root :: roots)
      duplicateHeadStrictJointFingerprint := by
  intro radius support
  exact centralStrictLocalQueryCode_duplicateHead
    radius base root roots support

theorem strictJointFingerprintRecoding_eraseDuplicateHead
    (base : Nat) (root : List Nat) (roots : List (List Nat)) :
    StrictJointFingerprintRecoding base
      (root :: root :: roots) (root :: roots)
      eraseSecondStrictJointFingerprint := by
  intro radius support
  exact centralStrictLocalQueryCode_eraseDuplicateHead
    radius base root roots support

theorem canonicalRoots_cons
    {base : Nat} {root : List Nat} {roots : List (List Nat)}
    (hroot : root ∈ canonicalSurfacePolymers base)
    (hroots : ∀ target, target ∈ roots →
      target ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ root :: roots →
      target ∈ canonicalSurfacePolymers base := by
  intro target htarget
  rcases List.mem_cons.mp htarget with htargetEq | htarget
  · rw [htargetEq]
    exact hroot
  · exact hroots target htarget

/-- Inserting an adjacent duplicate root is exact at every rational stage;
an arbitrary coefficient on the duplicated chart pulls back by duplicating
the corresponding Boolean coordinate. -/
theorem centralNormalizedStrictJointFixedQuadraticSequence_eqv_duplicateHead
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (root : List Nat) (roots : List (List Nat))
    (coefficient : List Bool → Q') (stage : Nat) :
    centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base (root :: root :: roots)
          coefficient stage ≈
      centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base (root :: roots)
          (fun bits => coefficient
            (duplicateHeadStrictJointFingerprint bits)) stage :=
  centralNormalizedStrictJointFixedQuadraticSequence_eqv_of_recoding
    coupling hcoupling base (root :: roots) (root :: root :: roots)
      duplicateHeadStrictJointFingerprint
      (strictJointFingerprintRecoding_duplicateHead base root roots)
      coefficient stage

/-- Duplicate elimination in the converse direction: a coefficient on the
short chart lifts to the duplicated chart while ignoring its redundant second
coordinate. -/
theorem centralNormalizedStrictJointFixedQuadraticSequence_eqv_eraseDuplicateHead
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (root : List Nat) (roots : List (List Nat))
    (coefficient : List Bool → Q') (stage : Nat) :
    centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base (root :: roots) coefficient stage ≈
      centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base (root :: root :: roots)
          (fun bits => coefficient
            (eraseSecondStrictJointFingerprint bits)) stage :=
  centralNormalizedStrictJointFixedQuadraticSequence_eqv_of_recoding
    coupling hcoupling base (root :: root :: roots) (root :: roots)
      eraseSecondStrictJointFingerprint
      (strictJointFingerprintRecoding_eraseDuplicateHead base root roots)
      coefficient stage

theorem centralNormalizedStrictJointFixedQuadraticLimit_equiv_duplicateHead
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {root : List Nat} {roots : List (List Nat)}
    (hroot : root ∈ canonicalSurfacePolymers base)
    (hroots : ∀ target, target ∈ roots →
      target ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool → Q') :
    CReal.Equiv
      (centralNormalizedStrictJointFixedQuadraticLimit
        coupling hcoupling hle
          (canonicalRoots_cons hroot
            (canonicalRoots_cons hroot hroots)) coefficient)
      (centralNormalizedStrictJointFixedQuadraticLimit
        coupling hcoupling hle (canonicalRoots_cons hroot hroots)
          (fun bits => coefficient
            (duplicateHeadStrictJointFingerprint bits))) := by
  exact centralNormalizedStrictJointFixedQuadraticLimit_equiv_of_recoding
    hcoupling hle (canonicalRoots_cons hroot hroots)
      (canonicalRoots_cons hroot (canonicalRoots_cons hroot hroots))
      duplicateHeadStrictJointFingerprint
      (strictJointFingerprintRecoding_duplicateHead base root roots)
      coefficient

theorem centralNormalizedStrictJointFixedQuadraticLimit_equiv_eraseDuplicateHead
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {root : List Nat} {roots : List (List Nat)}
    (hroot : root ∈ canonicalSurfacePolymers base)
    (hroots : ∀ target, target ∈ roots →
      target ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool → Q') :
    CReal.Equiv
      (centralNormalizedStrictJointFixedQuadraticLimit
        coupling hcoupling hle (canonicalRoots_cons hroot hroots)
          coefficient)
      (centralNormalizedStrictJointFixedQuadraticLimit
        coupling hcoupling hle
          (canonicalRoots_cons hroot
            (canonicalRoots_cons hroot hroots))
          (fun bits => coefficient
            (eraseSecondStrictJointFingerprint bits))) := by
  exact centralNormalizedStrictJointFixedQuadraticLimit_equiv_of_recoding
    hcoupling hle
      (canonicalRoots_cons hroot (canonicalRoots_cons hroot hroots))
      (canonicalRoots_cons hroot hroots)
      eraseSecondStrictJointFingerprint
      (strictJointFingerprintRecoding_eraseDuplicateHead base root roots)
      coefficient

/-! ## 4. Append as a common root-presentation refinement -/

theorem centralStrictLocalQueryCode_append
    (radius base : Nat) (leftRoots rightRoots : List (List Nat))
    (support : List Nat) :
    centralStrictLocalQueryCode radius base
        (leftRoots ++ rightRoots) support =
      centralStrictLocalQueryCode radius base leftRoots support ++
        centralStrictLocalQueryCode radius base rightRoots support := by
  unfold centralStrictLocalQueryCode
    centralLowerSupportQueryFingerprint
    canonicalRootsSupportQueryFingerprint
    centralStrictLowerCylinderRoots
  simp only [List.map_append, List.map_map]

def leftAppendStrictJointFingerprint
    (leftCount : Nat) (bits : List Bool) : List Bool :=
  bits.take leftCount

def rightAppendStrictJointFingerprint
    (leftCount : Nat) (bits : List Bool) : List Bool :=
  bits.drop leftCount

theorem strictJointFingerprintRecoding_append_left
    (base : Nat) (leftRoots rightRoots : List (List Nat)) :
    StrictJointFingerprintRecoding base
      (leftRoots ++ rightRoots) leftRoots
      (leftAppendStrictJointFingerprint leftRoots.length) := by
  intro radius support
  unfold leftAppendStrictJointFingerprint
  rw [centralStrictLocalQueryCode_append]
  have hlength := centralStrictLocalQueryCode_length
    radius base leftRoots support
  rw [← hlength, List.take_append_length]

theorem strictJointFingerprintRecoding_append_right
    (base : Nat) (leftRoots rightRoots : List (List Nat)) :
    StrictJointFingerprintRecoding base
      (leftRoots ++ rightRoots) rightRoots
      (rightAppendStrictJointFingerprint leftRoots.length) := by
  intro radius support
  unfold rightAppendStrictJointFingerprint
  rw [centralStrictLocalQueryCode_append]
  have hlength := centralStrictLocalQueryCode_length
    radius base leftRoots support
  rw [← hlength, List.drop_append_length]

theorem canonicalRoots_append
    {base : Nat} {leftRoots rightRoots : List (List Nat)}
    (hleftRoots : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers base)
    (hrightRoots : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ root, root ∈ leftRoots ++ rightRoots →
      root ∈ canonicalSurfacePolymers base := by
  intro root hroot
  rcases List.mem_append.mp hroot with hleft | hright
  · exact hleftRoots root hleft
  · exact hrightRoots root hright

/-- The append chart is a common refinement of any two canonical root
presentations.  Each limiting quadratic is recovered exactly by projecting
the common Boolean word to its left or right coordinate block. -/
theorem centralNormalizedStrictJointFixedQuadraticLimit_commonRefinement_append
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {leftRoots rightRoots : List (List Nat)}
    (hleftRoots : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers base)
    (hrightRoots : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    CReal.Equiv
        (centralNormalizedStrictJointFixedQuadraticLimit
          coupling hcoupling hle hleftRoots leftCoefficient)
        (centralNormalizedStrictJointFixedQuadraticLimit
          coupling hcoupling hle
            (canonicalRoots_append hleftRoots hrightRoots)
            (fun bits => leftCoefficient
              (leftAppendStrictJointFingerprint
                leftRoots.length bits))) ∧
      CReal.Equiv
        (centralNormalizedStrictJointFixedQuadraticLimit
          coupling hcoupling hle hrightRoots rightCoefficient)
        (centralNormalizedStrictJointFixedQuadraticLimit
          coupling hcoupling hle
            (canonicalRoots_append hleftRoots hrightRoots)
            (fun bits => rightCoefficient
              (rightAppendStrictJointFingerprint
                leftRoots.length bits))) := by
  constructor
  · exact centralNormalizedStrictJointFixedQuadraticLimit_equiv_of_recoding
      hcoupling hle (canonicalRoots_append hleftRoots hrightRoots)
        hleftRoots (leftAppendStrictJointFingerprint leftRoots.length)
        (strictJointFingerprintRecoding_append_left
          base leftRoots rightRoots) leftCoefficient
  · exact centralNormalizedStrictJointFixedQuadraticLimit_equiv_of_recoding
      hcoupling hle (canonicalRoots_append hleftRoots hrightRoots)
        hrightRoots (rightAppendStrictJointFingerprint leftRoots.length)
        (strictJointFingerprintRecoding_append_right
          base leftRoots rightRoots) rightCoefficient

#print axioms centralNormalizedStrictJointFixedQuadraticSequence_eqv_of_recoding
#print axioms centralNormalizedStrictJointFixedQuadraticLimit_equiv_of_recoding
#print axioms permuteStrictJointFingerprint_map
#print axioms centralStrictLocalQueryCode_perm
#print axioms centralNormalizedStrictJointFixedQuadraticLimit_equiv_perm
#print axioms centralNormalizedStrictJointFixedQuadraticSequence_eqv_duplicateHead
#print axioms centralNormalizedStrictJointFixedQuadraticLimit_equiv_duplicateHead
#print axioms centralNormalizedStrictJointFixedQuadraticLimit_equiv_eraseDuplicateHead
#print axioms centralStrictLocalQueryCode_append
#print axioms centralNormalizedStrictJointFixedQuadraticLimit_commonRefinement_append

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderPresentation
