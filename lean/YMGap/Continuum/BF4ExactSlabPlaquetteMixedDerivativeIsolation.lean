/-
# Two-edge isolation of a signed physical plaquette coefficient

Two distinct boundary links determine a plaquette. Differentiating a signed
face span once at each of two selected links therefore erases every other
face. This is a coefficient identity on the original polynomial carrier;
there is no action, positivity, or weighted estimate in this file.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity
import YMGap.Continuum.BF4ExactSlabPlaquetteGradient
import YMGap.Continuum.Z4PlaquetteBoundaryRigidity
import YMGap.Continuum.SU2QuaternionAngularLocality
import YMGap.Continuum.SU2QuaternionHaarAngularIBP

namespace YMGap.Continuum.BF4ExactSlabPlaquetteMixedDerivativeIsolation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork (correctedSlabPlaquettePolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabVacuumReflection (correctedSlabLinkAt)
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection (correctedSlabLinkAt_idxOf)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter)
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold (blockDegree_reindex)
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualPairing
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularLocality
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.SU2QuaternionHaarHeadFubini (headSwapBlockInvolution_map_zero)
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter (HasQuaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4PlaquetteBoundaryRigidity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

attribute [local irreducible] correctedSlabPlaquettePolynomial

/-- Angular differentiation at a literal physical link, transported through
the existing head transposition and back to the same polynomial carrier. -/
def linkDerivative (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (i j : Nat) (f : RatPoly) : RatPoly :=
  let swap := linkHeadSwap extent link hl
  reindexQuaternionPolynomial swap
    (angularDerivative i j (reindexQuaternionPolynomial swap f))

theorem linkDerivative_congr (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (i j : Nat) {f g : RatPoly}
    (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (linkDerivative extent link hl i j f)
      (linkDerivative extent link hl i j g) :=
  RatPolyCoeffEqv.reindex (linkHeadSwap extent link hl)
    (angularDerivative_congr i j
      (RatPolyCoeffEqv.reindex (linkHeadSwap extent link hl) h))

theorem linkDerivative_add (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (i j : Nat) (f g : RatPoly) :
    RatPolyCoeffEqv (linkDerivative extent link hl i j (polyAdd f g))
      (polyAdd (linkDerivative extent link hl i j f)
        (linkDerivative extent link hl i j g)) := by
  dsimp only [linkDerivative]
  rw [reindexQuaternionPolynomial_add]
  have h := RatPolyCoeffEqv.reindex (linkHeadSwap extent link hl)
    (angularDerivative_add i j
      (reindexQuaternionPolynomial (linkHeadSwap extent link hl) f)
      (reindexQuaternionPolynomial (linkHeadSwap extent link hl) g))
  simpa only [reindexQuaternionPolynomial_add] using h

theorem linkDerivative_smul (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (i j : Nat) (a : Q') (f : RatPoly) :
    RatPolyCoeffEqv (linkDerivative extent link hl i j (polySmul a f))
      (polySmul a (linkDerivative extent link hl i j f)) := by
  dsimp only [linkDerivative]
  rw [reindexQuaternionPolynomial_smul]
  have h := RatPolyCoeffEqv.reindex (linkHeadSwap extent link hl)
    (angularDerivative_smul i j a
      (reindexQuaternionPolynomial (linkHeadSwap extent link hl) f))
  simpa only [reindexQuaternionPolynomial_smul] using h

theorem linkDerivative_zero (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (i j : Nat) :
    RatPolyCoeffEqv (linkDerivative extent link hl i j polyZero) polyZero := by
  change RatPolyCoeffEqv
    (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
      (angularDerivative i j
        (reindexQuaternionPolynomial (linkHeadSwap extent link hl) polyZero))) polyZero
  exact RatPolyCoeffEqv.refl _

theorem linkDerivative_local (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    {links : List Z4Link} {f : RatPoly} (hf : LinkLocal extent links f)
    (hmem : link ∈ links) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    LinkLocal extent links (linkDerivative extent link hl i j f) := by
  unfold linkDerivative
  apply conjugatedHead_angularDerivative_local (linkHeadSwap extent link hl)
    hf (Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl))
  · rw [show (linkHeadSwap extent link hl).map 0 =
        (boundaryCompleteSlabLinks extent).idxOf link from
        headSwapBlockInvolution_map_zero _ _ (List.idxOf_lt_length_of_mem hl),
      correctedSlabLinkAt_idxOf hl]
    exact hmem
  · exact hi
  · exact hj

theorem linkDerivative_zero_of_missing (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    {links : List Z4Link} {f : RatPoly} (hf : LinkLocal extent links f)
    (hmiss : link ∉ links) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RatPolyCoeffEqv (linkDerivative extent link hl i j f) polyZero := by
  let swap := linkHeadSwap extent link hl
  have hd : HasQuaternionBlockDegree 0 0
      (reindexQuaternionPolynomial swap f) := by
    apply blockDegree_reindex swap
      (Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl))
      (headSwapBlockInvolution_map_zero _ _ (List.idxOf_lt_length_of_mem hl))
    exact linkLocal_degree_zero hf link hl hmiss
  have h := RatPolyCoeffEqv.reindex swap
    (angularDerivative_independent_zero hi hj _ hd)
  change RatPolyCoeffEqv (linkDerivative extent link hl i j f)
    (reindexQuaternionPolynomial swap polyZero) at h
  exact h

/-- Apply two distinct physical-link angular derivatives in the original
coordinate frame; the directions need not be equal at the two links. -/
def mixedDerivative (extent : Nat) (first second : Z4Link)
    (hfirst : first ∈ boundaryCompleteSlabLinks extent)
    (hsecond : second ∈ boundaryCompleteSlabLinks extent)
    (i j k l : Nat) (f : RatPoly) : RatPoly :=
  linkDerivative extent second hsecond k l
    (linkDerivative extent first hfirst i j f)

private theorem mixedDerivative_congr (extent : Nat) (first second : Z4Link)
    (hfirst : first ∈ boundaryCompleteSlabLinks extent)
    (hsecond : second ∈ boundaryCompleteSlabLinks extent)
    (i j k l : Nat) {f g : RatPoly} (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (mixedDerivative extent first second hfirst hsecond i j k l f)
      (mixedDerivative extent first second hfirst hsecond i j k l g) :=
  linkDerivative_congr extent second hsecond k l
    (linkDerivative_congr extent first hfirst i j h)

private theorem mixedDerivative_add (extent : Nat) (first second : Z4Link)
    (hfirst : first ∈ boundaryCompleteSlabLinks extent)
    (hsecond : second ∈ boundaryCompleteSlabLinks extent)
    (i j k l : Nat) (f g : RatPoly) :
    RatPolyCoeffEqv (mixedDerivative extent first second hfirst hsecond i j k l (polyAdd f g))
      (polyAdd (mixedDerivative extent first second hfirst hsecond i j k l f)
        (mixedDerivative extent first second hfirst hsecond i j k l g)) := by
  unfold mixedDerivative
  exact (linkDerivative_congr extent second hsecond k l
    (linkDerivative_add extent first hfirst i j f g)).trans
      (linkDerivative_add extent second hsecond k l _ _)

private theorem mixedDerivative_smul (extent : Nat) (first second : Z4Link)
    (hfirst : first ∈ boundaryCompleteSlabLinks extent)
    (hsecond : second ∈ boundaryCompleteSlabLinks extent)
    (i j k l : Nat) (a : Q') (f : RatPoly) :
    RatPolyCoeffEqv (mixedDerivative extent first second hfirst hsecond i j k l (polySmul a f))
      (polySmul a (mixedDerivative extent first second hfirst hsecond i j k l f)) := by
  unfold mixedDerivative
  exact (linkDerivative_congr extent second hsecond k l
    (linkDerivative_smul extent first hfirst i j a f)).trans
      (linkDerivative_smul extent second hsecond k l a _)

private theorem mixedDerivative_zero (extent : Nat) (first second : Z4Link)
    (hfirst : first ∈ boundaryCompleteSlabLinks extent)
    (hsecond : second ∈ boundaryCompleteSlabLinks extent)
    (i j k l : Nat) :
    RatPolyCoeffEqv (mixedDerivative extent first second hfirst hsecond i j k l polyZero)
      polyZero :=
  (linkDerivative_congr extent second hsecond k l
    (linkDerivative_zero extent first hfirst i j)).trans
    (linkDerivative_zero extent second hsecond k l)

/-- A different face cannot survive the two derivatives. The only geometric
input is that two distinct boundary links determine one plaquette. -/
theorem mixedDerivative_other_face_zero (extent : Nat)
    (p q : Z4Plaq) (hpq : q ≠ p) (first second : Z4Link)
    (hfirst : first ∈ boundaryCompleteSlabLinks extent)
    (hsecond : second ∈ boundaryCompleteSlabLinks extent)
    (hf : first ∈ edgesOf p) (hs : second ∈ edgesOf p)
    (hne : first ≠ second) {i j k l : Nat}
    (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4) :
    RatPolyCoeffEqv
      (mixedDerivative extent first second hfirst hsecond i j k l
        (faceCharacter extent q)) polyZero := by
  have hlocal : LinkLocal extent (edgesOf q) (faceCharacter extent q) := by
    unfold faceCharacter
    exact (face_scalar_local extent q).character 1
  by_cases hqf : first ∈ edgesOf q
  · have hqs : second ∉ edgesOf q := by
      intro h
      have he : p = q := two_boundary_links_determine_face p q first second
        hf hs hne hqf h
      exact hpq he.symm
    have hderiv := linkDerivative_local extent first hfirst hlocal hqf hi hj
    exact linkDerivative_zero_of_missing extent second hsecond hderiv hqs hk hl
  · have hz := linkDerivative_zero_of_missing extent first hfirst hlocal hqf hi hj
    exact (linkDerivative_congr extent second hsecond k l hz).trans
      (linkDerivative_zero extent second hsecond k l)

private theorem sourceSpan_absent_zero (extent : Nat) (c : Z4Plaq → Q')
    (p : Z4Plaq) (first second : Z4Link)
    (hfirst : first ∈ boundaryCompleteSlabLinks extent)
    (hsecond : second ∈ boundaryCompleteSlabLinks extent)
    (hf : first ∈ edgesOf p) (hs : second ∈ edgesOf p) (hne : first ≠ second)
    {i j k l : Nat} (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4) :
    ∀ qs : List Z4Plaq, p ∉ qs →
      RatPolyCoeffEqv
        (mixedDerivative extent first second hfirst hsecond i j k l
          (sourceSpan extent c qs)) polyZero
  | [], _ => mixedDerivative_zero extent first second hfirst hsecond i j k l
  | q::qs, habs => by
      have hnep : q ≠ p := by
        intro he
        apply habs
        exact List.mem_cons.mpr (Or.inl he.symm)
      have htail : p ∉ qs := fun hp => habs (List.mem_cons_of_mem q hp)
      change RatPolyCoeffEqv
        (mixedDerivative extent first second hfirst hsecond i j k l
          (polyAdd (polySmul (c q) (faceCharacter extent q))
            (sourceSpan extent c qs))) polyZero
      have hhead : RatPolyCoeffEqv
          (mixedDerivative extent first second hfirst hsecond i j k l
            (polySmul (c q) (faceCharacter extent q))) polyZero :=
        (mixedDerivative_smul extent first second hfirst hsecond i j k l (c q) _).trans
          (((mixedDerivative_other_face_zero extent p q hnep first second
            hfirst hsecond hf hs hne hi hj hk hl).smul (c q)).trans
            (RatPolyCoeffEqv.smul_zero (c q)))
      have hrest := sourceSpan_absent_zero extent c p first second
        hfirst hsecond hf hs hne hi hj hk hl qs htail
      exact (mixedDerivative_add extent first second hfirst hsecond i j k l _ _).trans
        ((hhead.add hrest).trans (RatPolyCoeffEqv.zero_add polyZero))

/-- The signed sourceSpan retains precisely the chosen face's coefficient.
Nodup removes multiple occurrences but no coefficient sign is changed. -/
theorem sourceSpan_mixedDerivative_isolates (extent : Nat) (c : Z4Plaq → Q')
    (p : Z4Plaq) (qs : List Z4Plaq) (hn : qs.Nodup) (hp : p ∈ qs)
    (first second : Z4Link)
    (hfirst : first ∈ boundaryCompleteSlabLinks extent)
    (hsecond : second ∈ boundaryCompleteSlabLinks extent)
    (hf : first ∈ edgesOf p) (hs : second ∈ edgesOf p) (hne : first ≠ second)
    {i j k l : Nat} (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4) :
    RatPolyCoeffEqv
      (mixedDerivative extent first second hfirst hsecond i j k l
        (sourceSpan extent c qs))
      (polySmul (c p)
        (mixedDerivative extent first second hfirst hsecond i j k l
          (faceCharacter extent p))) := by
  induction qs with
  | nil => exact False.elim (List.not_mem_nil hp)
  | cons q qs ih =>
      have hsplit := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hp with he | ht
      · subst q
        have htail := sourceSpan_absent_zero extent c p first second
          hfirst hsecond hf hs hne hi hj hk hl qs hsplit.1
        change RatPolyCoeffEqv
          (mixedDerivative extent first second hfirst hsecond i j k l
            (polyAdd (polySmul (c p) (faceCharacter extent p))
              (sourceSpan extent c qs))) _
        have hhead := mixedDerivative_smul extent first second hfirst hsecond
          i j k l (c p) (faceCharacter extent p)
        exact (mixedDerivative_add extent first second hfirst hsecond i j k l _ _).trans
          ((hhead.add htail).trans (RatPolyCoeffEqv.add_zero _))
      · have hnep : q ≠ p := by
          intro he
          apply hsplit.1
          exact he.symm ▸ ht
        have hterm := mixedDerivative_other_face_zero extent p q hnep first second
          hfirst hsecond hf hs hne hi hj hk hl
        change RatPolyCoeffEqv
          (mixedDerivative extent first second hfirst hsecond i j k l
            (polyAdd (polySmul (c q) (faceCharacter extent q))
              (sourceSpan extent c qs))) _
        have hhead : RatPolyCoeffEqv
            (mixedDerivative extent first second hfirst hsecond i j k l
              (polySmul (c q) (faceCharacter extent q))) polyZero :=
          (mixedDerivative_smul extent first second hfirst hsecond i j k l (c q) _).trans
            ((hterm.smul (c q)).trans (RatPolyCoeffEqv.smul_zero (c q)))
        exact (mixedDerivative_add extent first second hfirst hsecond i j k l _ _).trans
          ((hhead.add (ih hsplit.2 ht)).trans (RatPolyCoeffEqv.zero_add _))

/-- The same exact isolation holds after subtracting ANY rational center. -/
theorem affineSource_mixedDerivative_isolates (extent : Nat) (c : Z4Plaq → Q')
    (p : Z4Plaq) (qs : List Z4Plaq) (hn : qs.Nodup) (hp : p ∈ qs)
    (m : Q') (first second : Z4Link)
    (hfirst : first ∈ boundaryCompleteSlabLinks extent)
    (hsecond : second ∈ boundaryCompleteSlabLinks extent)
    (hf : first ∈ edgesOf p) (hs : second ∈ edgesOf p) (hne : first ≠ second)
    {i j k l : Nat} (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4) :
    RatPolyCoeffEqv
      (mixedDerivative extent first second hfirst hsecond i j k l
        (affineSource extent c qs m))
      (polySmul (c p)
        (mixedDerivative extent first second hfirst hsecond i j k l
          (faceCharacter extent p))) := by
  change RatPolyCoeffEqv
    (mixedDerivative extent first second hfirst hsecond i j k l
      (polyAdd (polySmul 1 (sourceSpan extent c qs)) (polySmul (-m) polyOne))) _
  have hone : LinkLocal extent ([] : List Z4Link) polyOne :=
    BlockLocal.one (List.length (boundaryCompleteSlabLinks extent))
      (fun block => correctedSlabLinkAt extent block ∈ ([] : List Z4Link))
  have hz := linkDerivative_zero_of_missing extent first hfirst hone
    (fun h => False.elim (List.not_mem_nil h)) hi hj
  have hm : RatPolyCoeffEqv
      (mixedDerivative extent first second hfirst hsecond i j k l polyOne)
      polyZero :=
    (linkDerivative_congr extent second hsecond k l hz).trans
      (linkDerivative_zero extent second hsecond k l)
  have hsource : RatPolyCoeffEqv
      (mixedDerivative extent first second hfirst hsecond i j k l
        (polySmul 1 (sourceSpan extent c qs)))
      (polySmul (c p)
        (mixedDerivative extent first second hfirst hsecond i j k l
          (faceCharacter extent p))) :=
    (mixedDerivative_smul extent first second hfirst hsecond i j k l 1 _).trans
      (((sourceSpan_mixedDerivative_isolates extent c p qs hn hp first second
        hfirst hsecond hf hs hne hi hj hk hl).smul 1).trans
        (RatPolyCoeffEqv.one_smul _))
  have hcenter : RatPolyCoeffEqv
      (mixedDerivative extent first second hfirst hsecond i j k l
        (polySmul (-m) polyOne)) polyZero :=
    (mixedDerivative_smul extent first second hfirst hsecond i j k l (-m) _).trans
      ((hm.smul (-m)).trans (RatPolyCoeffEqv.smul_zero (-m)))
  exact (mixedDerivative_add extent first second hfirst hsecond i j k l _ _).trans
    ((hsource.add hcenter).trans (RatPolyCoeffEqv.add_zero _))

#print axioms linkDerivative
#print axioms linkDerivative_congr
#print axioms linkDerivative_add
#print axioms linkDerivative_smul
#print axioms linkDerivative_zero
#print axioms linkDerivative_local
#print axioms linkDerivative_zero_of_missing
#print axioms mixedDerivative
#print axioms mixedDerivative_other_face_zero
#print axioms sourceSpan_mixedDerivative_isolates
#print axioms affineSource_mixedDerivative_isolates

end YMGap.Continuum.BF4ExactSlabPlaquetteMixedDerivativeIsolation
