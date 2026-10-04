/-
# A literal signed spatial family has one coherent tail at each original link

Every incident face is rotated in its original four-link word. Negative
incidences are conjugated, not dropped. The aggregate is a literal list sum:
repeated faces and signed coefficients survive, as do all cross-plane terms
inside its quaternion norm. Every Haar insertion, including the full original
interacting action, is retained. No variance comparison or smallness is claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyLocalAngular
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
import YMGap.Continuum.SU2QuaternionIndependentTailAngularSquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (Supported)
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.Z4UnitCubeIncidenceParity (edgesOf_nodup)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct (blockGamma)
open YMGap.Continuum.SU2QuaternionIndependentTailAngularSquare
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_coordinate)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_add supported_one)

local notation:max "N" width:arg => List.length (baseLinks width)
local infixl:70 " ⋄ " => PolyQuaternion.mul
attribute [local irreducible] baseLinks

private def faceLink (face : Z4Plaq) : Nat → Z4Link
  | 0 => (face.1,(dirsOf face.2).1)
  | 1 => (addE face.1 (dirsOf face.2).1,(dirsOf face.2).2)
  | 2 => (addE face.1 (dirsOf face.2).2,(dirsOf face.2).1)
  | _+3 => (face.1,(dirsOf face.2).2)

private def faceVariable (width : Nat) (face : Z4Plaq) (i : Nat) : PolyQuaternion :=
  PolyQuaternion.coordinateVariable ((baseLinks width).idxOf (faceLink face i))

private def zeroQuaternion : PolyQuaternion := ⟨polyZero,polyZero,polyZero,polyZero⟩
private def addQuaternion (p q : PolyQuaternion) : PolyQuaternion :=
  ⟨polyAdd p.scalar q.scalar,polyAdd p.iPart q.iPart,
    polyAdd p.jPart q.jPart,polyAdd p.kPart q.kPart⟩
private def smulQuaternion (c : Q') (p : PolyQuaternion) : PolyQuaternion :=
  ⟨polyMul (cap c) p.scalar,polyMul (cap c) p.iPart,
    polyMul (cap c) p.jPart,polyMul (cap c) p.kPart⟩

/-- The selected original face is rebased at its actual link. Missing incidences
return zero; no truncated predecessor or fixture coordinate is substituted. -/
def faceCoherentTail (width : Nat) (l : Z4Link) (face : Z4Plaq) : PolyQuaternion :=
  let q := faceVariable width face
  if l = faceLink face 0 then (q 1 ⋄ PolyQuaternion.conj (q 2)) ⋄ PolyQuaternion.conj (q 3)
  else if l = faceLink face 1 then (PolyQuaternion.conj (q 2) ⋄ PolyQuaternion.conj (q 3)) ⋄ q 0
  else if l = faceLink face 2 then PolyQuaternion.conj ((PolyQuaternion.conj (q 3) ⋄ q 0) ⋄ q 1)
  else if l = faceLink face 3 then PolyQuaternion.conj ((q 0 ⋄ q 1) ⋄ PolyQuaternion.conj (q 2))
  else zeroQuaternion

def incidentSpan (width : Nat) (l : Z4Link) (c : Z4Plaq → Q') (qs : List Z4Plaq) : RatPoly :=
  spatialSpan width c (blockRowFaces width ((baseLinks width).idxOf l) qs)

private def sumTails (width : Nat) (l : Z4Link) (c : Z4Plaq → Q') : List Z4Plaq → PolyQuaternion
  | [] => zeroQuaternion
  | p::ps => addQuaternion (smulQuaternion (c p) (faceCoherentTail width l p))
      (sumTails width l c ps)

/-- Literal order and every occurrence of each signed face are retained. -/
def aggregateCoherentTail (width : Nat) (l : Z4Link) (c : Z4Plaq → Q') (qs : List Z4Plaq) : PolyQuaternion :=
  sumTails width l c (blockRowFaces width ((baseLinks width).idxOf l) qs)

private theorem faceLink_mem (face : Z4Plaq) (i : Nat) : faceLink face i ∈ edgesOf face := by
  match i with
  | 0 | 1 | 2 | _+3 => simp [faceLink,edgesOf]

private theorem faceLink_distinct (face : Z4Plaq) :
    (faceLink face 0 ≠ faceLink face 1 ∧ faceLink face 0 ≠ faceLink face 2 ∧ faceLink face 0 ≠ faceLink face 3) ∧
    (faceLink face 1 ≠ faceLink face 2 ∧ faceLink face 1 ≠ faceLink face 3) ∧
      faceLink face 2 ≠ faceLink face 3 := by
  have h := edgesOf_nodup face
  simp only [edgesOf,List.nodup_cons,List.mem_cons,or_false,
    List.nodup_nil,List.not_mem_nil,not_or,not_false_eq_true,and_true] at h
  exact ⟨⟨h.1.2.2,h.1.2.1,h.1.1⟩,
    ⟨(fun e => h.2.2 e.symm),(fun e => h.2.1.2 e.symm)⟩,
    (fun e => h.2.1.1 e.symm)⟩

private theorem faceVariable_supported (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (i : Nat) : Supported (N width) (faceVariable width face i) :=
  Supported.coordinate (List.idxOf_lt_length_of_mem (face_link_mem_base hf (faceLink_mem face i)))

private theorem faceVariable_degree (width : Nat) (l : Z4Link) (hl : l ∈ baseLinks width)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width) (i : Nat) (hne : l ≠ faceLink face i) :
    HasPolyQuaternionBlockDegree ((baseLinks width).idxOf l) 0 (faceVariable width face i) := by
  have hi := face_link_mem_base hf (faceLink_mem face i)
  have hd : (baseLinks width).idxOf l ≠ (baseLinks width).idxOf (faceLink face i) :=
    fun h => hne (idxOf_injective_on_members hl hi h)
  simpa only [faceVariable,if_neg hd] using
    hasPolyQuaternionBlockDegree_coordinateVariable
      ((baseLinks width).idxOf (faceLink face i)) ((baseLinks width).idxOf l)

theorem faceCoherentTail_supported (width : Nat) (l : Z4Link) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) : Supported (N width) (faceCoherentTail width l face) := by
  have h := faceVariable_supported width face hf
  unfold faceCoherentTail
  split
  · exact ((h 1).mul (h 2).conj).mul (h 3).conj
  · split
    · exact ((h 2).conj.mul (h 3).conj).mul (h 0)
    · split
      · exact (((h 3).conj.mul (h 0)).mul (h 1)).conj
      · split
        · exact (((h 0).mul (h 1)).mul (h 2).conj).conj
        · exact ⟨(by intro t ht; cases ht),(by intro t ht; cases ht),
            (by intro t ht; cases ht),(by intro t ht; cases ht)⟩

theorem faceCoherentTail_degree_zero (width : Nat) (l : Z4Link) (hl : l ∈ baseLinks width)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    HasPolyQuaternionBlockDegree ((baseLinks width).idxOf l) 0 (faceCoherentTail width l face) := by
  have hn := faceLink_distinct face
  have h := faceVariable_degree width l hl face hf
  unfold faceCoherentTail
  split
  · rename_i he
    subst l
    exact ((h 1 hn.1.1).mul (h 2 hn.1.2.1).conj).mul (h 3 hn.1.2.2).conj
  · rename_i h0
    split
    · rename_i he
      subst l
      exact (((h 2 hn.2.1.1).conj.mul (h 3 hn.2.1.2).conj).mul (h 0 hn.1.1.symm))
    · rename_i h1
      split
      · rename_i he
        subst l
        exact (((h 3 hn.2.2).conj.mul (h 0 hn.1.2.1.symm)).mul (h 1 hn.2.1.1.symm)).conj
      · rename_i h2
        split
        · rename_i he
          subst l
          exact (((h 0 hn.1.2.2.symm).mul (h 1 hn.2.1.2.symm)).mul (h 2 hn.2.2.symm).conj).conj
        · exact ⟨(by intro t ht; cases ht),(by intro t ht; cases ht),
            (by intro t ht; cases ht),(by intro t ht; cases ht)⟩

private theorem first_tail (a b c d : PolyQuaternion) :
    RatPolyCoeffEqv (((a ⋄ b) ⋄ c) ⋄ d).scalar (a ⋄ ((b ⋄ c) ⋄ d)).scalar :=
  (((PolyQuaternionCoeffEqv.mul_assoc a b c).mul (.refl d)).trans
    (PolyQuaternionCoeffEqv.mul_assoc a (b ⋄ c) d)).scalar

private theorem reverse_first (a b : PolyQuaternion) :
    RatPolyCoeffEqv (PolyQuaternion.conj a ⋄ b).scalar (a ⋄ PolyQuaternion.conj b).scalar := by
  let env : Nat → RatPoly := fun
    | 0 => a.scalar | 1 => a.iPart | 2 => a.jPart | 3 => a.kPart
    | 4 => b.scalar | 5 => b.iPart | 6 => b.jPart | _ => b.kPart
  exact coeffEvalExpr_eqv_of_normalize_eq
    (PolyQuaternionExpr.mul (PolyQuaternionExpr.conj (.coordinate 0)) (.coordinate 4)).scalar
    (PolyQuaternionExpr.mul (.coordinate 0) (PolyQuaternionExpr.conj (.coordinate 4))).scalar
    (by decide) env

/-- Coefficient-strength recoding of the actual face, not a fixture substitution. -/
theorem actual_face_tail_recode (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (l : Z4Link) (hl : l ∈ edgesOf face) :
    RatPolyCoeffEqv (characterPolynomial (plaquette width face).scalar 1)
      (characterPolynomial (PolyQuaternion.mul
        (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf l))
        (faceCoherentTail width l face)).scalar 1) := by
  let q := faceVariable width face
  have hp : RatPolyCoeffEqv (plaquette width face).scalar
      (((q 0 ⋄ q 1) ⋄ PolyQuaternion.conj (q 2)) ⋄ PolyQuaternion.conj (q 3)).scalar :=
    (plaquette_fourWord hf).scalar
  have h1 := hp.trans (scalar_cyclic (q 0) (q 1) (PolyQuaternion.conj (q 2)) (PolyQuaternion.conj (q 3)))
  have h2 := h1.trans (scalar_cyclic (q 1) (PolyQuaternion.conj (q 2)) (PolyQuaternion.conj (q 3)) (q 0))
  have h3 := h2.trans (scalar_cyclic (PolyQuaternion.conj (q 2)) (PolyQuaternion.conj (q 3)) (q 0) (q 1))
  have hn := faceLink_distinct face
  have hm : l = faceLink face 0 ∨ l = faceLink face 1 ∨ l = faceLink face 2 ∨ l = faceLink face 3 := by
    have h : l = faceLink face 0 ∨ l = faceLink face 3 ∨ l = faceLink face 2 ∨ l = faceLink face 1 := by
      simpa only [edgesOf,List.mem_cons,List.mem_nil_iff,or_false,faceLink] using hl
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  rcases hm with he | he | he | he
  · subst l
    simp only [faceCoherentTail]
    exact characterPolynomial_coeffEqv (hp.trans (first_tail _ _ _ _)) 1
  · subst l
    simp only [faceCoherentTail,if_neg hn.1.1.symm]
    exact characterPolynomial_coeffEqv (h1.trans (first_tail _ _ _ _)) 1
  · subst l
    simp only [faceCoherentTail,if_neg hn.1.2.1.symm,if_neg hn.2.1.1.symm]
    exact characterPolynomial_coeffEqv
      (h2.trans ((first_tail _ _ _ _).trans (reverse_first _ _))) 1
  · subst l
    simp only [faceCoherentTail,if_neg hn.1.2.2.symm,if_neg hn.2.1.2.symm,if_neg hn.2.2.symm]
    exact characterPolynomial_coeffEqv
      (h3.trans ((first_tail _ _ _ _).trans (reverse_first _ _))) 1

private def linearTrace (b : Nat) (p : PolyQuaternion) : RatPoly :=
  characterPolynomial (PolyQuaternion.coordinateVariable b ⋄ p).scalar 1

private theorem linearTrace_add (b : Nat) (p q : PolyQuaternion) :
    RatPolyCoeffEqv (linearTrace b (addQuaternion p q))
      (polyAdd (linearTrace b p) (linearTrace b q)) := by
  let u := PolyQuaternion.coordinateVariable b
  let env : Nat → RatPoly := fun
    | 0 => u.scalar | 1 => u.iPart | 2 => u.jPart | 3 => u.kPart
    | 4 => p.scalar | 5 => p.iPart | 6 => p.jPart | 7 => p.kPart
    | 8 => q.scalar | 9 => q.iPart | 10 => q.jPart | _ => q.kPart
  let sum : PolyQuaternionExpr :=
    ⟨.add (.var 4) (.var 8),.add (.var 5) (.var 9),
      .add (.var 6) (.var 10),.add (.var 7) (.var 11)⟩
  have h : RatPolyCoeffEqv (u ⋄ addQuaternion p q).scalar
      (polyAdd (u ⋄ p).scalar (u ⋄ q).scalar) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (PolyQuaternionExpr.mul (.coordinate 0) sum).scalar
      (.add (PolyQuaternionExpr.mul (.coordinate 0) (.coordinate 4)).scalar
        (PolyQuaternionExpr.mul (.coordinate 0) (.coordinate 8)).scalar) (by decide) env
  exact (h.smul 2).trans (RatPolyCoeffEqv.smul_add 2 _ _)

private theorem linearTrace_smul (b : Nat) (c : Q') (p : PolyQuaternion) :
    RatPolyCoeffEqv (linearTrace b (smulQuaternion c p)) (polySmul c (linearTrace b p)) := by
  let u := PolyQuaternion.coordinateVariable b
  let env : Nat → RatPoly := fun
    | 0 => u.scalar | 1 => u.iPart | 2 => u.jPart | 3 => u.kPart
    | 4 => p.scalar | 5 => p.iPart | 6 => p.jPart | 7 => p.kPart | _ => cap c
  let scaled : PolyQuaternionExpr :=
    ⟨.mul (.var 8) (.var 4),.mul (.var 8) (.var 5),
      .mul (.var 8) (.var 6),.mul (.var 8) (.var 7)⟩
  have h : RatPolyCoeffEqv (u ⋄ smulQuaternion c p).scalar
      (polyMul (cap c) (u ⋄ p).scalar) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (PolyQuaternionExpr.mul (.coordinate 0) scaled).scalar
      (.mul (.var 8) (PolyQuaternionExpr.mul (.coordinate 0) (.coordinate 4)).scalar)
      (by decide) env
  exact (h.smul 2).trans
    ((RatPolyCoeffEqv.polyMul_smul_right 2 (cap c) (u ⋄ p).scalar).symm.trans
      (cap_mul_left c (linearTrace b p)))

private theorem row_incident (width : Nat) (l : Z4Link) (hl : l ∈ baseLinks width)
    (face : Z4Plaq) (hrow : blockRow width ((baseLinks width).idxOf l) face = true) :
    l ∈ edgesOf face := by
  obtain ⟨r,hr,hb,hi⟩ := (blockRow_iff width _ face).mp hrow
  have he := idxOf_injective_on_members hb hl hi
  exact he ▸ hr

private theorem tail_sum_recode (width : Nat) (l : Z4Link) (hl : l ∈ baseLinks width)
    (c : Z4Plaq → Q') : ∀ qs : List Z4Plaq,
    (∀ p, p ∈ qs → p ∈ spatialFaces width) →
    (∀ p, p ∈ qs → blockRow width ((baseLinks width).idxOf l) p = true) →
    RatPolyCoeffEqv (spatialSpan width c qs)
      (linearTrace ((baseLinks width).idxOf l) (sumTails width l c qs))
  | [], _, _ => .refl _
  | p::ps, hf, hr => by
      have hface := (((actual_face_tail_recode width p (hf p List.mem_cons_self) l
        (row_incident width l hl p (hr p List.mem_cons_self))).smul (c p)).trans
          (linearTrace_smul _ _ _).symm)
      have hrest := tail_sum_recode width l hl c ps
        (fun q hq => hf q (List.mem_cons_of_mem p hq))
        (fun q hq => hr q (List.mem_cons_of_mem p hq))
      exact (hface.add hrest).trans (linearTrace_add _ _ _).symm

theorem incidentSpan_tail_pin (width : Nat) (l : Z4Link) (hl : l ∈ baseLinks width)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hf : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    RatPolyCoeffEqv (incidentSpan width l c qs)
      (characterPolynomial (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf l) ⋄
        aggregateCoherentTail width l c qs).scalar 1) :=
  tail_sum_recode width l hl c _
    (fun p hp => hf p ((blockRowFaces_mem_iff width _ qs p).mp hp).1)
    (fun p hp => ((blockRowFaces_mem_iff width _ qs p).mp hp).2)

private theorem cap_supported (blocks : Nat) (c : Q') : SupportedQuaternionBlocks blocks (cap c) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact supported_one blocks s hs

private theorem sumTails_supported (width : Nat) (l : Z4Link) (c : Z4Plaq → Q') :
    ∀ qs : List Z4Plaq, (∀ p, p ∈ qs → p ∈ spatialFaces width) →
      Supported (N width) (sumTails width l c qs)
  | [], _ => ⟨(by intro t ht; cases ht),(by intro t ht; cases ht),
      (by intro t ht; cases ht),(by intro t ht; cases ht)⟩
  | p::ps, hf => by
      have hp := faceCoherentTail_supported width l p (hf p List.mem_cons_self)
      have hs := sumTails_supported width l c ps (fun q hq => hf q (List.mem_cons_of_mem p hq))
      have hc := cap_supported (N width) (c p)
      exact ⟨supported_add (supported_polyMul hc hp.scalar) hs.scalar,
        supported_add (supported_polyMul hc hp.iPart) hs.iPart,
        supported_add (supported_polyMul hc hp.jPart) hs.jPart,
        supported_add (supported_polyMul hc hp.kPart) hs.kPart⟩

theorem aggregate_tail_supported (width : Nat) (l : Z4Link) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hf : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    Supported (N width) (aggregateCoherentTail width l c qs) :=
  sumTails_supported width l c _
    (fun p hp => hf p ((blockRowFaces_mem_iff width _ qs p).mp hp).1)

private theorem sumTails_degree (width : Nat) (l : Z4Link) (hl : l ∈ baseLinks width)
    (c : Z4Plaq → Q') : ∀ qs : List Z4Plaq,
    (∀ p, p ∈ qs → p ∈ spatialFaces width) →
    HasPolyQuaternionBlockDegree ((baseLinks width).idxOf l) 0 (sumTails width l c qs)
  | [], _ => ⟨(by intro t ht; cases ht),(by intro t ht; cases ht),
      (by intro t ht; cases ht),(by intro t ht; cases ht)⟩
  | p::ps, hf => by
      have hp := faceCoherentTail_degree_zero width l hl p (hf p List.mem_cons_self)
      have hs := sumTails_degree width l hl c ps (fun q hq => hf q (List.mem_cons_of_mem p hq))
      have hc : HasQuaternionBlockDegree ((baseLinks width).idxOf l) 0 (cap (c p)) :=
        (hasQuaternionBlockDegree_one _).smul (c p)
      exact ⟨(hc.mul hp.scalar).add hs.scalar,(hc.mul hp.iPart).add hs.iPart,
        (hc.mul hp.jPart).add hs.jPart,(hc.mul hp.kPart).add hs.kPart⟩

theorem aggregate_tail_degree_zero (width : Nat) (l : Z4Link) (hl : l ∈ baseLinks width)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hf : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    HasPolyQuaternionBlockDegree ((baseLinks width).idxOf l) 0 (aggregateCoherentTail width l c qs) :=
  sumTails_degree width l hl c _
    (fun p hp => hf p ((blockRowFaces_mem_iff width _ qs p).mp hp).1)

private theorem row_derivative (width b : Nat) (hb : b < N width) (c : Z4Plaq → Q')
    (i j : Nat) (hi : i < 4) (hj : j < 4) : ∀ qs : List Z4Plaq,
    RatPolyCoeffEqv (angularDerivative (4*b+i) (4*b+j) (spatialSpan width c qs))
      (angularDerivative (4*b+i) (4*b+j) (spatialSpan width c (blockRowFaces width b qs)))
  | [] => .refl _
  | p::ps => by
      have ih := row_derivative width b hb c i j hi hj ps
      cases hr : blockRow width b p with
      | true =>
          simp only [blockRowFaces,List.filter_cons,hr]
          exact (angularDerivative_add _ _ _ _).trans
            (((RatPolyCoeffEqv.refl _).add ih).trans (angularDerivative_add _ _ _ _).symm)
      | false =>
          simp only [blockRowFaces,List.filter_cons,hr]
          have hz := (angularDerivative_smul _ _ (c p) _).trans
            (((blockRow_derivative_zero width b p hb hr hi hj).smul (c p)).trans
              (RatPolyCoeffEqv.smul_zero (c p)))
          exact (angularDerivative_add _ _ _ _).trans
            ((hz.add ih).trans (RatPolyCoeffEqv.zero_add _))

private theorem row_square (width b : Nat) (hb : b < N width) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    RatPolyCoeffEqv (blockGamma b (spatialSpan width c qs) (spatialSpan width c qs))
      (blockAngularSquare b (spatialSpan width c (blockRowFaces width b qs))) := by
  have h (i j : Nat) (hi : i < 4) (hj : j < 4) := row_derivative width b hb c i j hi hj qs
  unfold blockGamma blockAngularSquare six
  exact ((h 0 1 (by decide) (by decide)).mul (h 0 1 (by decide) (by decide))).add
    (((h 0 2 (by decide) (by decide)).mul (h 0 2 (by decide) (by decide))).add
      (((h 0 3 (by decide) (by decide)).mul (h 0 3 (by decide) (by decide))).add
        (((h 1 2 (by decide) (by decide)).mul (h 1 2 (by decide) (by decide))).add
          (((h 1 3 (by decide) (by decide)).mul (h 1 3 (by decide) (by decide))).add
            ((h 2 3 (by decide) (by decide)).mul (h 2 3 (by decide) (by decide)))))))

private theorem square_congr (b : Nat) {p q : RatPoly} (hp : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (blockAngularSquare b p) (blockAngularSquare b q) := by
  have h (i j : Nat) := angularDerivative_congr (4*b+i) (4*b+j) hp
  unfold blockAngularSquare six
  exact ((h 0 1).mul (h 0 1)).add (((h 0 2).mul (h 0 2)).add
    (((h 0 3).mul (h 0 3)).add (((h 1 2).mul (h 1 2)).add
      (((h 1 3).mul (h 1 3)).add ((h 2 3).mul (h 2 3))))))

/-- The exact row norm retains every signed cross-group term and EVERY full
Haar insertion. The square subtracted is the incident span, not the full source. -/
theorem family_coherent_row (width : Nat) (l : Z4Link) (hl : l ∈ baseLinks width)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hf : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    HaarCarrierEqv (N width)
      (blockGamma ((baseLinks width).idxOf l) (spatialSpan width c qs) (spatialSpan width c qs))
      (polyAdd (polySmul 4 (polyQuaternionNorm (aggregateCoherentTail width l c qs)))
        (polyNeg (polyMul (incidentSpan width l c qs) (incidentSpan width l c qs)))) := by
  let b := (baseLinks width).idxOf l
  let tail := aggregateCoherentTail width l c qs
  have hb := List.idxOf_lt_length_of_mem hl
  have hp := incidentSpan_tail_pin width l hl c qs hf
  have hnorm : HaarCarrierEqv (N width)
      (polyMul (polyQuaternionNorm (PolyQuaternion.coordinateVariable b)) (polyQuaternionNorm tail))
      (polyQuaternionNorm tail) :=
    (HaarCarrierEqv.mul_right (polyQuaternionNorm tail) (haarNorm_coordinate hb)).trans
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_mul _))
  exact (RatPolyCoeffEqv.haarCarrier (row_square width b hb c qs)).trans
    ((RatPolyCoeffEqv.haarCarrier (square_congr b hp)).trans
      ((linear_angularSquare_norm hb tail (aggregate_tail_degree_zero width l hl c qs hf)).trans
        (HaarCarrierEqv.add (HaarCarrierEqv.smul 4 hnorm)
          (HaarCarrierEqv.neg (RatPolyCoeffEqv.haarCarrier (hp.symm.mul hp.symm))))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail.faceCoherentTail
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail.incidentSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail.aggregateCoherentTail
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail.faceCoherentTail_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail.faceCoherentTail_degree_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail.actual_face_tail_recode
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail.incidentSpan_tail_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail.aggregate_tail_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail.aggregate_tail_degree_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail.family_coherent_row
