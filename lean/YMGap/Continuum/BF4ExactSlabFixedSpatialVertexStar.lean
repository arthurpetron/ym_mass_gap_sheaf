/-
# Literal vertex-center signs on the original spatial action

The star contains ALL retained links incident to the vertex, including
inactive fringe links. Every closed spatial face has even star incidence,
so its complete finite heat prefix, and the complete original spatial
weight, are invariant coefficientwise. No terminal-message invariance,
operator estimate, gauge-invariant-sector gap or limit is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
import YMGap.Continuum.SU2QuaternionCoordinateConjugation
import YMGap.Continuum.Z4EvenLinkMinimum

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces temporalFaces temporalFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary (SliceLink)
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram (faceLinkA)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (face_link_mem_base plaquette_fourWord)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt activeBlocks_nodup)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionCoordinateConjugation (signSelectedPolynomial_var)
open YMGap.Continuum.SU2QuaternionOrientedWordSelection (word)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.Z4EvenLinkMinimum (base_ne_tip)
open YMGap.Continuum.CayleyPruferInjection (nodup_subset_length_le)

local notation:max "N" width:arg => List.length (baseLinks width)
local infixl:70 " ⋄ " => PolyQuaternion.mul
local prefix:80 "bar " => PolyQuaternion.conj
attribute [local irreducible] baseLinks spatialWeight

/-- Source OR target incidence, not a truncation to kinetic coordinates. -/
def incident (v : Z4Vertex) (l : Z4Link) : Bool :=
  decide (v = l.1 ∨ v = addE l.1 l.2)

private def fallback : Z4Link := ((0,0,0,0), Dir4.x0)

/-- The original numeric link slot; off-carrier slots are never selected. -/
def blockSelector (width : Nat) (v : Z4Vertex) (i : Nat) : Bool :=
  if i < N width then incident v ((baseLinks width).getD i fallback) else false

def coordinateSelector (width : Nat) (v : Z4Vertex) (c : Nat) : Bool :=
  blockSelector width v (c / 4)

def starSign (width : Nat) (v : Z4Vertex) (p : RatPoly) : RatPoly :=
  signSelectedPolynomial (4*N width) (coordinateSelector width v) p

theorem starSign_supported (width : Nat) (v : Z4Vertex) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    SupportedQuaternionBlocks (N width) (starSign width v p) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact hp source hs

theorem starSign_involutive (width : Nat) (v : Z4Vertex) : ∀ p : RatPoly,
    RatPolyCoeffEqv (starSign width v (starSign width v p)) p
  | [] => RatPolyCoeffEqv.refl []
  | term :: rest => by
      intro weight
      simp only [starSign, signSelectedPolynomial, List.map_cons]
      simp only [signSelectedTerm, ratWeightedSum]
      generalize hparity :
        selectedExponentParity (4*N width) (coordinateSelector width v) term.1 = parity
      cases parity
      · simp only [Bool.false_eq_true, if_false]
        exact Q'.add_eqv_congr' (Q'.eqv_refl _)
          (starSign_involutive width v rest weight)
      · simp only [if_true]
        exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ _ (Q'.neg_neg_eqv term.2))
          (starSign_involutive width v rest weight)

/-- Precisely the heat factors affected by a one-endpoint star sign. -/
def activeStar (width : Nat) (v : Z4Vertex) : List Nat :=
  (activeBlocks width).filter (blockSelector width v)

theorem coordinateSelector_block (width : Nat) (v : Z4Vertex) (i c : Nat) (hc : c < 4) :
    coordinateSelector width v (4*i+c) = blockSelector width v i := by
  unfold coordinateSelector
  congr 1
  omega

private theorem getD_idxOf {A : Type} [BEq A] [LawfulBEq A]
    (items : List A) (a default : A) (ha : a ∈ items) :
    items.getD (items.idxOf a) default = a := by
  have hi := List.idxOf_lt_length_of_mem ha
  rw [← List.getElem_eq_getD (l := items) (i := items.idxOf a) (h := hi) default]
  exact LawfulBEq.eq_of_beq (List.findIdx_getElem (w := hi))

theorem blockSelector_idxOf (width : Nat) (v : Z4Vertex) (l : Z4Link)
    (hl : l ∈ baseLinks width) :
    blockSelector width v ((baseLinks width).idxOf l) = incident v l := by
  rw [blockSelector, if_pos (List.idxOf_lt_length_of_mem hl), getD_idxOf _ _ _ hl]

theorem activeStar_mem (width : Nat) (v : Z4Vertex) (i : Nat) :
    i ∈ activeStar width v ↔ i ∈ activeBlocks width ∧ blockSelector width v i = true :=
  List.mem_filter

theorem activeStar_lt (width : Nat) (v : Z4Vertex) (i : Nat) (hi : i ∈ activeStar width v) :
    i < N width := activeBlocks_lt width i ((activeStar_mem width v i).mp hi).1

theorem activeStar_nodup (width : Nat) (v : Z4Vertex) : (activeStar width v).Nodup :=
  List.filter_sublist.nodup (activeBlocks_nodup width)

private theorem incident_xor (v : Z4Vertex) (l : Z4Link) :
    incident v l = xor (decide (v = l.1)) (decide (v = addE l.1 l.2)) := by
  by_cases hs : v = l.1 <;> by_cases ht : v = addE l.1 l.2
  · exact False.elim (base_ne_tip l (hs.symm.trans ht))
  all_goals simp [incident, hs, ht, base_ne_tip l, Ne.symm (base_ne_tip l)]

private theorem addE_comm (v : Z4Vertex) (d e : Dir4) :
    addE (addE v d) e = addE (addE v e) d := by
  rcases v with ⟨a,b,c,t⟩
  cases d <;> cases e <;> rfl

private def signedQuaternion (b : Bool) (p : PolyQuaternion) : PolyQuaternion :=
  if b then ⟨polyNeg p.scalar, polyNeg p.iPart, polyNeg p.jPart, polyNeg p.kPart⟩ else p

private def signExpr (b : Bool) (p : PolyQuaternionExpr) : PolyQuaternionExpr :=
  if b then ⟨.neg p.scalar, .neg p.iPart, .neg p.jPart, .neg p.kPart⟩ else p

private def environment (p q : PolyQuaternion) : Nat → RatPoly
  | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
  | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | _ => q.kPart

private theorem signed_mul (a b : Bool) (p q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (signedQuaternion a p ⋄ signedQuaternion b q)
      (signedQuaternion (xor a b) (p ⋄ q)) := by
  let l := PolyQuaternionExpr.mul (signExpr a (.coordinate 0)) (signExpr b (.coordinate 4))
  let r := signExpr (xor a b) (PolyQuaternionExpr.mul (.coordinate 0) (.coordinate 4))
  have hs := coeffEvalExpr_eqv_of_normalize_eq l.scalar r.scalar
    (by cases a <;> cases b <;> decide) (environment p q)
  have hi := coeffEvalExpr_eqv_of_normalize_eq l.iPart r.iPart
    (by cases a <;> cases b <;> decide) (environment p q)
  have hj := coeffEvalExpr_eqv_of_normalize_eq l.jPart r.jPart
    (by cases a <;> cases b <;> decide) (environment p q)
  have hk := coeffEvalExpr_eqv_of_normalize_eq l.kPart r.kPart
    (by cases a <;> cases b <;> decide) (environment p q)
  cases a <;> cases b <;> exact ⟨hs,hi,hj,hk⟩

private theorem signed_conj (b : Bool) (p : PolyQuaternion) :
    bar (signedQuaternion b p) = signedQuaternion b (bar p) := by cases b <;> rfl

private theorem closed_signs (a b c d : Bool) (p q r s : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (((signedQuaternion (xor a b) p ⋄ signedQuaternion (xor b c) q) ⋄
        bar (signedQuaternion (xor d c) r)) ⋄ bar (signedQuaternion (xor a d) s))
      (((p ⋄ q) ⋄ bar r) ⋄ bar s) := by
  rw [signed_conj, signed_conj]
  have h1 := ((signed_mul (xor a b) (xor b c) p q).mul
    (.refl (signedQuaternion (xor d c) (bar r)))).trans
      (signed_mul (xor (xor a b) (xor b c)) (xor d c) (p ⋄ q) (bar r))
  have h2 := (h1.mul (.refl (signedQuaternion (xor a d) (bar s)))).trans
    (signed_mul (xor (xor (xor a b) (xor b c)) (xor d c)) (xor a d)
      ((p ⋄ q) ⋄ bar r) (bar s))
  have hz : xor (xor (xor (xor a b) (xor b c)) (xor d c)) (xor a d) = false := by
    cases a <;> cases b <;> cases c <;> cases d <;> decide
  rw [hz] at h2
  exact h2

private def transformQuaternion (width : Nat) (v : Z4Vertex) (p : PolyQuaternion) : PolyQuaternion :=
  ⟨starSign width v p.scalar, starSign width v p.iPart,
    starSign width v p.jPart, starSign width v p.kPart⟩

private theorem transform_mul (width : Nat) (v : Z4Vertex) (p q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (transformQuaternion width v (p ⋄ q))
      (transformQuaternion width v p ⋄ transformQuaternion width v q) := by
  have hm (a b : RatPoly) := signSelectedPolynomial_mul_coeffEqv
    (4*N width) (coordinateSelector width v) a b
  constructor
  all_goals simp only [transformQuaternion, starSign, PolyQuaternion.mul,
    signSelectedPolynomial_add, signSelectedPolynomial_neg]
  · exact (hm p.scalar q.scalar).add (RatPolyCoeffEqv.neg
      ((hm p.iPart q.iPart).add ((hm p.jPart q.jPart).add (hm p.kPart q.kPart))))
  · exact (hm p.scalar q.iPart).add ((hm p.iPart q.scalar).add
      ((hm p.jPart q.kPart).add (RatPolyCoeffEqv.neg (hm p.kPart q.jPart))))
  · exact (hm p.scalar q.jPart).add ((hm p.jPart q.scalar).add
      ((hm p.kPart q.iPart).add (RatPolyCoeffEqv.neg (hm p.iPart q.kPart))))
  · exact (hm p.scalar q.kPart).add ((hm p.kPart q.scalar).add
      ((hm p.iPart q.jPart).add (RatPolyCoeffEqv.neg (hm p.jPart q.iPart))))

private theorem transform_conj (width : Nat) (v : Z4Vertex) (p : PolyQuaternion) :
    transformQuaternion width v (bar p) = bar (transformQuaternion width v p) := by
  simp only [transformQuaternion, starSign, PolyQuaternion.conj, signSelectedPolynomial_neg]

private theorem transform_coordinate (width : Nat) (v : Z4Vertex) (i : Nat) (hi : i < N width) :
    transformQuaternion width v (PolyQuaternion.coordinateVariable i) =
      signedQuaternion (blockSelector width v i) (PolyQuaternion.coordinateVariable i) := by
  unfold transformQuaternion starSign PolyQuaternion.coordinateVariable
  rw [signSelectedPolynomial_var _ _ (4*i) (by omega),
    signSelectedPolynomial_var _ _ (4*i+1) (by omega),
    signSelectedPolynomial_var _ _ (4*i+2) (by omega),
    signSelectedPolynomial_var _ _ (4*i+3) (by omega)]
  rw [show coordinateSelector width v (4*i) = blockSelector width v i from
    coordinateSelector_block width v i 0 (by decide),
    coordinateSelector_block width v i 1 (by decide),
    coordinateSelector_block width v i 2 (by decide),
    coordinateSelector_block width v i 3 (by decide)]
  cases blockSelector width v i <;> rfl

private theorem transform_word (width : Nat) (v : Z4Vertex) (a b c d : PolyQuaternion) :
    PolyQuaternionCoeffEqv (transformQuaternion width v (((a ⋄ b) ⋄ bar c) ⋄ bar d))
      (((transformQuaternion width v a ⋄ transformQuaternion width v b) ⋄
        bar (transformQuaternion width v c)) ⋄ bar (transformQuaternion width v d)) := by
  have h := (transform_mul width v ((a ⋄ b) ⋄ bar c) (bar d)).trans
    (((transform_mul width v (a ⋄ b) (bar c)).trans
      ((transform_mul width v a b).mul (.refl _))).mul (.refl _))
  simpa only [transform_conj] using h

/-- Every original spatial face is even under the full literal vertex star. -/
theorem plaquette_invariant (width : Nat) (v : Z4Vertex) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    RatPolyCoeffEqv (starSign width v (plaquette width face).scalar) (plaquette width face).scalar := by
  let d := (dirsOf face.2).1
  let e := (dirsOf face.2).2
  let a : Z4Link := (face.1,d)
  let b : Z4Link := (addE face.1 d,e)
  let c : Z4Link := (addE face.1 e,d)
  let f : Z4Link := (face.1,e)
  have ha : a ∈ baseLinks width := face_link_mem_base hf (by simp [a, d, edgesOf])
  have hb : b ∈ baseLinks width := face_link_mem_base hf (by simp [b, d, e, edgesOf])
  have hc : c ∈ baseLinks width := face_link_mem_base hf (by simp [c, d, e, edgesOf])
  have hd : f ∈ baseLinks width := face_link_mem_base hf (by simp [f, e, edgesOf])
  let q (l : Z4Link) := PolyQuaternion.coordinateVariable ((baseLinks width).idxOf l)
  have hpin : PolyQuaternionCoeffEqv (plaquette width face) (((q a ⋄ q b) ⋄ bar (q c)) ⋄ bar (q f)) :=
    plaquette_fourWord hf
  have ht := transform_word width v (q a) (q b) (q c) (q f)
  have hq (l : Z4Link) (hl : l ∈ baseLinks width) :
      transformQuaternion width v (q l) = signedQuaternion (incident v l) (q l) := by
    change transformQuaternion width v
        (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf l)) =
      signedQuaternion (incident v l)
        (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf l))
    rw [transform_coordinate width v _ (List.idxOf_lt_length_of_mem hl),
      blockSelector_idxOf width v l hl]
  rw [hq a ha, hq b hb, hq c hc, hq f hd] at ht
  have hsign := closed_signs (decide (v = face.1)) (decide (v = addE face.1 d))
    (decide (v = addE (addE face.1 d) e)) (decide (v = addE face.1 e)) (q a) (q b) (q c) (q f)
  have hinc : PolyQuaternionCoeffEqv
      (((signedQuaternion (incident v a) (q a) ⋄ signedQuaternion (incident v b) (q b)) ⋄
        bar (signedQuaternion (incident v c) (q c))) ⋄ bar (signedQuaternion (incident v f) (q f)))
      (((q a ⋄ q b) ⋄ bar (q c)) ⋄ bar (q f)) := by
    simp only [incident_xor, a, b, c, f]
    rw [addE_comm face.1 e d]
    exact hsign
  exact (signSelectedPolynomial_coeffEqv (4*N width) (coordinateSelector width v) hpin.scalar).trans
    ((ht.trans hinc).scalar.trans hpin.scalar.symm)

private theorem parity_nil (selected : Nat → Bool) : ∀ n,
    selectedExponentParity n selected [] = false
  | 0 => rfl
  | n+1 => by
      have h : selectedExponentParity (n+1) selected [] =
          if selected n then xor (selectedExponentParity n selected []) false
          else selectedExponentParity n selected [] := by
        simp only [selectedExponentParity, List.range_succ, List.foldl_append,
          List.foldl_cons, List.foldl_nil, exponentAt, List.getD_nil]
        rfl
      rw [h, parity_nil selected n]
      cases selected n <;> rfl

theorem starSign_one (width : Nat) (v : Z4Vertex) : starSign width v polyOne = polyOne := by
  simp only [starSign, signSelectedPolynomial, polyOne, List.map_cons, List.map_nil,
    signSelectedTerm, parity_nil, Bool.false_eq_true, ↓reduceIte]

theorem starSign_add (width : Nat) (v : Z4Vertex) (p q : RatPoly) :
    starSign width v (polyAdd p q) = polyAdd (starSign width v p) (starSign width v q) :=
  signSelectedPolynomial_add _ _ p q

theorem starSign_mul (width : Nat) (v : Z4Vertex) (p q : RatPoly) :
    RatPolyCoeffEqv (starSign width v (polyMul p q))
      (polyMul (starSign width v p) (starSign width v q)) :=
  signSelectedPolynomial_mul_coeffEqv _ _ p q

theorem starSign_smul (width : Nat) (v : Z4Vertex) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (starSign width v (polySmul c p)) (polySmul c (starSign width v p)) :=
  signSelectedPolynomial_smul_coeffEqv _ _ c p

private theorem character_invariant (width : Nat) (v : Z4Vertex) (p : RatPoly)
    (hp : RatPolyCoeffEqv (starSign width v p) p) : ∀ spin,
    RatPolyCoeffEqv (starSign width v (characterPolynomial p spin)) (characterPolynomial p spin)
  | 0 => by rw [characterPolynomial, starSign_one]; exact .refl _
  | 1 => (starSign_smul width v 2 p).trans (hp.smul 2)
  | n+2 => by
      rw [characterPolynomial, starSign_add]
      exact ((starSign_mul width v _ _).trans
        (((starSign_smul width v 2 p).trans (hp.smul 2)).mul
          (character_invariant width v p hp (n+1)))).add
        ((starSign_smul width v (-1) _).trans ((character_invariant width v p hp n).smul (-1)))

/-- No spin is omitted by the center sign identity. -/
theorem character_starSign (width : Nat) (v : Z4Vertex) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (spin : Nat) :
    RatPolyCoeffEqv (starSign width v (characterPolynomial (plaquette width face).scalar spin))
      (characterPolynomial (plaquette width face).scalar spin) :=
  character_invariant width v _ (plaquette_invariant width v face hf) spin

private theorem sum_invariant {A : Type} (width : Nat) (v : Z4Vertex) (f : A → RatPoly) :
    ∀ ids : List A, (∀ i, i ∈ ids → RatPolyCoeffEqv (starSign width v (f i)) (f i)) →
      RatPolyCoeffEqv (starSign width v (finitePolySum f ids)) (finitePolySum f ids)
  | [], _ => .refl _
  | i::ids, hi => by
      rw [finitePolySum, starSign_add]
      exact (hi i List.mem_cons_self).add
        (sum_invariant width v f ids (fun j hj => hi j (List.mem_cons_of_mem i hj)))

/-- The complete original finite heat prefix, at every nome and cutoff. -/
theorem heatFace_starSign (w : Q') (K width : Nat) (v : Z4Vertex) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    RatPolyCoeffEqv (starSign width v (heatPrefix w K (plaquette width face).scalar))
      (heatPrefix w K (plaquette width face).scalar) := by
  unfold heatPrefix
  apply sum_invariant
  intro spin _
  exact (starSign_smul width v _ _).trans ((character_starSign width v face hf spin).smul _)

private theorem product_invariant {A : Type} (width : Nat) (v : Z4Vertex) (f : A → RatPoly) :
    ∀ ids : List A, (∀ i, i ∈ ids → RatPolyCoeffEqv (starSign width v (f i)) (f i)) →
      RatPolyCoeffEqv (starSign width v (polynomialProduct f ids)) (polynomialProduct f ids)
  | [], _ => by change RatPolyCoeffEqv (starSign width v polyOne) polyOne; rw [starSign_one]; exact .refl _
  | i::ids, hi => (starSign_mul width v _ _).trans
      ((hi i List.mem_cons_self).mul
        (product_invariant width v f ids (fun j hj => hi j (List.mem_cons_of_mem i hj))))

/-- Full spatial action invariance: all faces and all cutoff terms retained. -/
theorem spatialWeight_starSign (w : Q') (K width : Nat) (v : Z4Vertex) :
    RatPolyCoeffEqv (starSign width v (spatialWeight w K width)) (spatialWeight w K width) := by
  unfold spatialWeight
  exact product_invariant width v _ (spatialFaces width) (heatFace_starSign w K width v)

private def sixLinks (v : Z4Vertex) : List Z4Link :=
  [(v,.x0),(v,.x1),(v,.x2),(subE v .x0,.x0),(subE v .x1,.x1),(subE v .x2,.x2)]

private theorem incident_in_six (v : Z4Vertex) (l : Z4Link)
    (hs : l.2 ≠ Dir4.x3) (hi : incident v l = true) : l ∈ sixLinks v := by
  have hp : v = l.1 ∨ v = addE l.1 l.2 := of_decide_eq_true hi
  rcases l with ⟨u,d⟩
  rcases hp with hp | hp
  · subst v
    cases d <;> first | exact False.elim (hs rfl) | simp [sixLinks]
  · have hu : u = subE v d :=
      (subE_addE u d).symm.trans (congrArg (fun w => subE w d) hp.symm)
    rw [hu]
    cases d <;> first | exact False.elim (hs rfl) | simp [sixLinks]

private theorem active_face_link_mem {width : Nat} {face : Z4Plaq}
    (hf : face ∈ temporalFaces width) : faceLinkA face ∈ baseLinks width := by
  obtain ⟨hx,hy,hz,ht,hd⟩ := (temporalFaces_mem_iff width face).mp hf
  apply (baseLinks_mem_iff width _).mpr
  rcases face with ⟨⟨x,y,z,t⟩,plane⟩
  cases plane <;> simp only [dirsOf] at hd <;> try cases hd
  all_goals dsimp only at hx hy hz ht
  all_goals simp only [SliceLink, faceLinkA, dirsOf]
  all_goals refine ⟨(by intro h; cases h), ?_, ?_, ?_, ?_⟩ <;> omega

/-- Boundary stars may contain fewer factors, never more than six.
The six-link comparison list may repeat at zero coordinates; its length
bound does not rely on interpreting those repeated candidates as links. -/
theorem activeStar_length_le_six (width : Nat) (v : Z4Vertex) : (activeStar width v).length ≤ 6 := by
  have hsub : ∀ i, i ∈ activeStar width v →
      i ∈ (sixLinks v).map ((baseLinks width).idxOf) := by
    intro i hi
    have hm := (activeStar_mem width v i).mp hi
    obtain ⟨face,hface,rfl⟩ := List.mem_map.mp hm.1
    have hl := active_face_link_mem hface
    have hs := ((baseLinks_mem_iff width _).mp hl).1
    have hin := hm.2
    rw [blockSelector_idxOf width v _ hl] at hin
    exact List.mem_map.mpr ⟨faceLinkA face, incident_in_six v _ hs hin, rfl⟩
  have h := nodup_subset_length_le (activeStar width v)
    ((sixLinks v).map ((baseLinks width).idxOf)) (activeStar_nodup width v) hsub
  simpa only [List.length_map, sixLinks, List.length_cons, List.length_nil] using h

end YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.incident
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.blockSelector
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.coordinateSelector
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.starSign
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.starSign_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.starSign_involutive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.activeStar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.coordinateSelector_block
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.blockSelector_idxOf
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.activeStar_mem
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.activeStar_lt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.activeStar_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.plaquette_invariant
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.starSign_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.starSign_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.starSign_mul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.starSign_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.character_starSign
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.heatFace_starSign
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.spatialWeight_starSign
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar.activeStar_length_le_six
