/-
# A literal rational unit-quaternion field test for plaquette-only recoding

Two consecutive x0 links at the corner carry I,I or I,J. Every other link
is the unit. Each elementary plaquette meets at most one marked link, so its
class coordinate agrees in the two fields. The two-plaquette rectangle does
not. This is a pointwise observable-algebra obstruction, not an OS-norm
non-density or transfer-kernel theorem.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback
import YMGap.Continuum.SU2QuaternionWilsonWeightSOS
import YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing

namespace YMGap.Continuum.SU2PlaquetteCharacterNonseparation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS (evalRatPoly_var)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing (schurFactor)

local infix:50 " ≈ " => Q'.eqv

def unitI : UnitNorm := ⟨basisI, by unfold IsUnitNorm normSq basisI; decide⟩
def unitJ : UnitNorm := ⟨basisJ, by unfold IsUnitNorm normSq basisJ; decide⟩

def markA : Z4Link := ((0,0,0,0), .x0)
def markB : Z4Link := ((1,0,0,0), .x0)

/-- Both alternatives are genuine unit-norm fields on the same lattice. -/
def field (alternate : Bool) : RationalUnitQuaternionGaugeField := fun link =>
  if link = markA then unitI
  else if link = markB then (if alternate then unitJ else unitI)
  else unitOne

/-- All elementary faces, not merely the two selected faces or a finite list. -/
theorem plaquette_scalar_equal (face : Z4Plaq) :
    (latticePlaquetteHolonomy (field false) face).val.r =
      (latticePlaquetteHolonomy (field true) face).val.r := by
  obtain ⟨⟨x,y,z,t⟩,plane⟩ := face
  cases plane <;>
    cases (inferInstance : Decidable (x = 0 ∧ y = 0 ∧ z = 0 ∧ t = 0)) <;> rename_i h0 <;>
    cases (inferInstance : Decidable (x = 1 ∧ y = 0 ∧ z = 0 ∧ t = 0)) <;> rename_i h1 <;>
    simp only [latticePlaquetteHolonomy, standardPlaquetteHolonomy,
      plaquetteOrientedEdgeInput, field, markA, markB, dirsOf, addE,
      Prod.mk.injEq, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, false_and,
      and_true, reduceCtorEq, h0, h1, ↓reduceIte] <;> rfl

private def rectangleWord {A : Type} (mul : A → A → A) (inv : A → A) (f : Z4Link → A) : A :=
  mul (mul (mul
    (mul (mul (f markA) (f markB))
      (f ((2,0,0,0), .x1)))
    (inv (f ((1,1,0,0), .x0))))
    (inv (f ((0,1,0,0), .x0))))
    (inv (f ((0,0,0,0), .x1)))

/-- The six ordered outer edges, with the last three read inversely. -/
def rectangleHolonomy (f : RationalUnitQuaternionGaugeField) : UnitNorm :=
  rectangleWord UnitNorm.mul UnitNorm.inv f

theorem rectangle_false : (rectangleHolonomy (field false)).val.r ≈ -1 := by decide +kernel
theorem rectangle_true : (rectangleHolonomy (field true)).val.r ≈ 0 := by decide +kernel

theorem rectangle_distinguished :
    ¬ ((rectangleHolonomy (field false)).val.r ≈ (rectangleHolonomy (field true)).val.r) := by
  intro h
  have bad := Q'.eqv_trans _ _ _ (Q'.eqv_symm rectangle_false)
    (Q'.eqv_trans _ _ _ h rectangle_true)
  exact (by decide : ¬ ((-1 : Q') ≈ 0)) bad

private def value (q : UnitNorm) : QuaternionValue := ⟨q.val.r,q.val.i,q.val.j,q.val.k⟩

private def component (q : UnitNorm) : Nat → Q'
  | 0 => q.val.r | 1 => q.val.i | 2 => q.val.j | 3 => q.val.k | _ => 0

/-- Evaluation on the ORIGINAL slab's link-major coordinate carrier. -/
def fieldEnvironment (extent : Nat) (f : RationalUnitQuaternionGaugeField) (i : Nat) : Q' :=
  component (f (correctedSlabLinkAt extent (i/4))) (i%4)

private theorem environment_component (extent : Nat) (f : RationalUnitQuaternionGaugeField)
    (block c : Nat) (hc : c < 4) :
    fieldEnvironment extent f (4*block+c) = component (f (correctedSlabLinkAt extent block)) c := by
  unfold fieldEnvironment
  rw [show (4*block+c)/4 = block by omega, show (4*block+c)%4 = c by omega]

/-- Every coordinate block in either test environment is genuinely on S^3. -/
theorem fieldEnvironment_unit (extent : Nat) (f : RationalUnitQuaternionGaugeField) (block : Nat) :
    (fieldEnvironment extent f (4*block) * fieldEnvironment extent f (4*block) +
      fieldEnvironment extent f (4*block+1) * fieldEnvironment extent f (4*block+1)) +
    (fieldEnvironment extent f (4*block+2) * fieldEnvironment extent f (4*block+2) +
      fieldEnvironment extent f (4*block+3) * fieldEnvironment extent f (4*block+3)) ≈ 1 := by
  have h0 := environment_component extent f block 0 (by decide)
  have h1 := environment_component extent f block 1 (by decide)
  have h2 := environment_component extent f block 2 (by decide)
  have h3 := environment_component extent f block 3 (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0,h1,h2,h3]
  exact (f (correctedSlabLinkAt extent block)).unitNorm

private theorem qmul {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') : a*b ≈ a'*b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem value_trans {a b c : QuaternionValue} (h : QuaternionValue.Eqv a b)
    (k : QuaternionValue.Eqv b c) : QuaternionValue.Eqv a c :=
  ⟨Q'.eqv_trans _ _ _ h.scalar k.scalar, Q'.eqv_trans _ _ _ h.iPart k.iPart,
    Q'.eqv_trans _ _ _ h.jPart k.jPart, Q'.eqv_trans _ _ _ h.kPart k.kPart⟩

private theorem value_mul {a a' b b' : QuaternionValue} (ha : QuaternionValue.Eqv a a')
    (hb : QuaternionValue.Eqv b b') : QuaternionValue.Eqv (QuaternionValue.mul a b) (QuaternionValue.mul a' b') := by
  constructor <;> simp only [QuaternionValue.mul]
  all_goals repeat' first
    | exact ha.scalar | exact ha.iPart | exact ha.jPart | exact ha.kPart
    | exact hb.scalar | exact hb.iPart | exact hb.jPart | exact hb.kPart
    | apply Q'.add_eqv_congr' | apply qmul | apply Q'.neg_eqv_congr

private theorem realizes_mul {rho : Nat → Q'} {p q : PolyQuaternion} {a b : QuaternionValue}
    (hp : QuaternionValue.Eqv (evalPolyQuaternion rho p) a)
    (hq : QuaternionValue.Eqv (evalPolyQuaternion rho q) b) :
    QuaternionValue.Eqv (evalPolyQuaternion rho (PolyQuaternion.mul p q)) (QuaternionValue.mul a b) :=
  value_trans (evalPolyQuaternion_mul _ _ _) (value_mul hp hq)

private theorem realizes_conj {rho : Nat → Q'} {p : PolyQuaternion} {a : QuaternionValue}
    (hp : QuaternionValue.Eqv (evalPolyQuaternion rho p) a) :
    QuaternionValue.Eqv (evalPolyQuaternion rho (PolyQuaternion.conj p)) (QuaternionValue.conj a) :=
  value_trans (evalPolyQuaternion_conj _ _) ⟨hp.scalar,
    Q'.neg_eqv_congr _ _ hp.iPart, Q'.neg_eqv_congr _ _ hp.jPart, Q'.neg_eqv_congr _ _ hp.kPart⟩

private theorem eval_link (extent : Nat) (f : RationalUnitQuaternionGaugeField)
    (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent) :
    QuaternionValue.Eqv (evalPolyQuaternion (fieldEnvironment extent f)
      (correctedSlabLinkPolynomial extent link)) (value (f link)) := by
  have hc (c : Nat) (h : c < 4) : evalRatPoly (fieldEnvironment extent f)
      (polyVar (4*(boundaryCompleteSlabLinks extent).idxOf link+c)) ≈ component (f link) c := by
    refine Q'.eqv_trans _ _ _ (evalRatPoly_var _ _) ?_
    rw [environment_component _ _ _ _ h, correctedSlabLinkAt_idxOf hl]
    exact Q'.eqv_refl _
  rw [correctedSlabLinkPolynomial_of_mem hl]
  exact ⟨hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)⟩

private def faceValue (f : RationalUnitQuaternionGaugeField) (face : Z4Plaq) : QuaternionValue :=
  QuaternionValue.mul (QuaternionValue.mul (QuaternionValue.mul
    (QuaternionValue.mul QuaternionValue.one (value (f (faceLinkA face))))
      (value (f (faceLinkB face)))) (QuaternionValue.conj (value (f (faceLinkC face)))))
        (QuaternionValue.conj (value (f (faceLinkD face))))

private theorem eval_face (extent : Nat) (f : RationalUnitQuaternionGaugeField)
    (face : Z4Plaq) (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    QuaternionValue.Eqv (evalPolyQuaternion (fieldEnvironment extent f)
      (correctedSlabPlaquettePolynomial extent face)) (faceValue f face) := by
  have hp (link : Z4Link) (h : link ∈ edgesOf face) : link ∈ boundaryCompleteSlabLinks extent :=
    (mem_boundaryCompleteSlabLinks_iff extent link).mpr ⟨face,hf,h⟩
  exact realizes_mul (realizes_mul (realizes_mul
    (realizes_mul (evalPolyQuaternion_one _) (eval_link _ _ _ (hp _ (by simp [edgesOf]))))
      (eval_link _ _ _ (hp _ (by simp [edgesOf]))))
        (realizes_conj (eval_link _ _ _ (hp _ (by simp [edgesOf])))))
          (realizes_conj (eval_link _ _ _ (hp _ (by simp [edgesOf]))))

private theorem faceValue_equal (face : Z4Plaq) :
    (faceValue (field false) face).scalar = (faceValue (field true) face).scalar := by
  obtain ⟨⟨x,y,z,t⟩,plane⟩ := face
  cases plane <;>
    cases (inferInstance : Decidable (x = 0 ∧ y = 0 ∧ z = 0 ∧ t = 0)) <;> rename_i h0 <;>
    cases (inferInstance : Decidable (x = 1 ∧ y = 0 ∧ z = 0 ∧ t = 0)) <;> rename_i h1 <;>
    simp only [faceValue, faceLinkA, faceLinkB, faceLinkC, faceLinkD,
      field, markA, markB, dirsOf, addE,
      Prod.mk.injEq, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, false_and,
      and_true, reduceCtorEq, h0, h1, ↓reduceIte] <;> rfl

private theorem eval_add_pair {rho sigma : Nat → Q'} {p p' q q' : RatPoly}
    (hp : evalRatPoly rho p ≈ evalRatPoly sigma p') (hq : evalRatPoly rho q ≈ evalRatPoly sigma q') :
    evalRatPoly rho (polyAdd p q) ≈ evalRatPoly sigma (polyAdd p' q') :=
  Q'.eqv_trans _ _ _ (evalRatPoly_add _ _ _) (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hp hq) (Q'.eqv_symm (evalRatPoly_add _ _ _)))

private theorem eval_mul_pair {rho sigma : Nat → Q'} {p p' q q' : RatPoly}
    (hp : evalRatPoly rho p ≈ evalRatPoly sigma p') (hq : evalRatPoly rho q ≈ evalRatPoly sigma q') :
    evalRatPoly rho (polyMul p q) ≈ evalRatPoly sigma (polyMul p' q') :=
  Q'.eqv_trans _ _ _ (evalRatPoly_mul _ _ _) (Q'.eqv_trans _ _ _
    (qmul hp hq) (Q'.eqv_symm (evalRatPoly_mul _ _ _)))

private theorem eval_smul_pair {rho sigma : Nat → Q'} {p q : RatPoly}
    (h : evalRatPoly rho p ≈ evalRatPoly sigma q) (c : Q') :
    evalRatPoly rho (polySmul c p) ≈ evalRatPoly sigma (polySmul c q) :=
  Q'.eqv_trans _ _ _ (SU2QuaternionWilsonWeightSOS.evalRatPoly_smul _ _ _) (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ h) (Q'.eqv_symm (SU2QuaternionWilsonWeightSOS.evalRatPoly_smul _ _ _)))

private theorem eval_character_pair {rho sigma : Nat → Q'} {p q : RatPoly}
    (h : evalRatPoly rho p ≈ evalRatPoly sigma q) : ∀ spin,
    evalRatPoly rho (characterPolynomial p spin) ≈ evalRatPoly sigma (characterPolynomial q spin)
  | 0 => Q'.eqv_refl _
  | 1 => eval_smul_pair h 2
  | n+2 => eval_add_pair (eval_mul_pair (eval_smul_pair h 2) (eval_character_pair h (n+1)))
      (eval_smul_pair (eval_character_pair h n) (-1))

private theorem evaluate_same {half : Nat} (f : Nat → Nat → RatPoly) (rho sigma : Nat → Q')
    (h : ∀ id, id ∈ centralLowerFaceIds half → ∀ spin, evalRatPoly rho (f id spin) ≈ evalRatPoly sigma (f id spin)) :
    ∀ e : PlaquetteExpression half, evalRatPoly rho (evaluate f e) ≈ evalRatPoly sigma (evaluate f e)
  | .unit => Q'.eqv_refl _
  | .character id hi spin => h id hi spin
  | .add e g => eval_add_pair (evaluate_same f rho sigma h e) (evaluate_same f rho sigma h g)
  | .mul e g => eval_mul_pair (evaluate_same f rho sigma h e) (evaluate_same f rho sigma h g)
  | .smul c e => eval_smul_pair (evaluate_same f rho sigma h e) c

private theorem same_scalar (rho sigma : Nat → Q') (p q : PolyQuaternion) (a b : QuaternionValue)
    (hp : QuaternionValue.Eqv (evalPolyQuaternion rho p) a)
    (hq : QuaternionValue.Eqv (evalPolyQuaternion sigma q) b) (h : a.scalar = b.scalar) :
    evalRatPoly rho p.scalar ≈ evalRatPoly sigma q.scalar := by
  have hl : evalRatPoly rho p.scalar ≈ a.scalar := hp.scalar
  have hr : evalRatPoly sigma q.scalar ≈ b.scalar := hq.scalar
  rw [h] at hl
  exact Q'.eqv_trans _ _ _ hl (Q'.eqv_symm hr)

private theorem face_evaluation_equal (extent : Nat) (face : Z4Plaq)
    (hp : face ∈ boundaryCompleteSlabPlaquettes extent) (spin : Nat) :
    evalRatPoly (fieldEnvironment extent (field false))
      (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) ≈
    evalRatPoly (fieldEnvironment extent (field true))
      (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) := by
  have hs : evalRatPoly (fieldEnvironment extent (field false))
      (correctedSlabPlaquettePolynomial extent face).scalar ≈
    evalRatPoly (fieldEnvironment extent (field true))
      (correctedSlabPlaquettePolynomial extent face).scalar :=
    same_scalar (fieldEnvironment extent (field false)) (fieldEnvironment extent (field true))
      (correctedSlabPlaquettePolynomial extent face) (correctedSlabPlaquettePolynomial extent face)
      (faceValue (field false) face) (faceValue (field true) face)
      (eval_face extent (field false) face hp) (eval_face extent (field true) face hp) (faceValue_equal face)
  exact eval_character_pair hs spin

/-- Every expression in the EXISTING original algebra agrees on the two
literal unit fields, at every half-size and every character spin. -/
theorem original_lower_equal {half : Nat} (e : PlaquetteExpression half) :
    evalRatPoly (fieldEnvironment (centralExtent half) (field false)) (lower e) ≈
      evalRatPoly (fieldEnvironment (centralExtent half) (field true)) (lower e) := by
  let f : Nat → Nat → RatPoly := fun id spin => characterPolynomial
    (correctedSlabPlaquettePolynomial (centralExtent half) (slabPlaquetteAt (centralExtent half) id)).scalar spin
  change evalRatPoly (fieldEnvironment (centralExtent half) (field false)) (evaluate f e) ≈
    evalRatPoly (fieldEnvironment (centralExtent half) (field true)) (evaluate f e)
  refine evaluate_same f (fieldEnvironment (centralExtent half) (field false))
    (fieldEnvironment (centralExtent half) (field true)) ?_ e
  intro id hi spin
  have hp : slabPlaquetteAt (centralExtent half) id ∈ boundaryCompleteSlabPlaquettes (centralExtent half) :=
    slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp hi).1
  exact face_evaluation_equal (centralExtent half) (slabPlaquetteAt (centralExtent half) id) hp spin

private def rectangleQuaternion : PolyQuaternion :=
  rectangleWord PolyQuaternion.mul PolyQuaternion.conj (correctedSlabLinkPolynomial 1)

/-- The six-link rectangle character on the ORIGINAL extent-one slab, not
an independent six-link surrogate. -/
def rectanglePolynomial : RatPoly := characterPolynomial rectangleQuaternion.scalar 1

private def rectangleValue (f : RationalUnitQuaternionGaugeField) : QuaternionValue :=
  rectangleWord QuaternionValue.mul QuaternionValue.conj (fun link => value (f link))

private theorem eval_rectangle (f : RationalUnitQuaternionGaugeField) :
    QuaternionValue.Eqv (evalPolyQuaternion (fieldEnvironment 1 f) rectangleQuaternion) (rectangleValue f) := by
  have ha := eval_link 1 f markA (by decide +kernel)
  have hb := eval_link 1 f markB (by decide +kernel)
  have he := eval_link 1 f ((2,0,0,0), .x1) (by decide +kernel)
  have hf := eval_link 1 f ((1,1,0,0), .x0) (by decide +kernel)
  have hc := eval_link 1 f ((0,1,0,0), .x0) (by decide +kernel)
  have hd := eval_link 1 f ((0,0,0,0), .x1) (by decide +kernel)
  exact realizes_mul (realizes_mul (realizes_mul (realizes_mul (realizes_mul ha hb) he)
    (realizes_conj hf)) (realizes_conj hc)) (realizes_conj hd)

private theorem fundamental_evaluation (rho : Nat → Q') (p : PolyQuaternion) (v : QuaternionValue)
    (h : QuaternionValue.Eqv (evalPolyQuaternion rho p) v) :
    evalRatPoly rho (characterPolynomial p.scalar 1) ≈ 2*v.scalar :=
  Q'.eqv_trans _ _ _ (SU2QuaternionWilsonWeightSOS.evalRatPoly_smul _ _ _)
    (Q'.mul_eqv_congr_left _ _ _ h.scalar)

/-- The SAME original rectangle has values -2 and 0 on the two unit fields. -/
theorem rectangle_evaluation (alternate : Bool) :
    evalRatPoly (fieldEnvironment 1 (field alternate)) rectanglePolynomial ≈
      (if alternate then 0 else -2) := by
  have h := fundamental_evaluation (fieldEnvironment 1 (field alternate)) rectangleQuaternion
    (rectangleValue (field alternate)) (eval_rectangle (field alternate))
  refine Q'.eqv_trans
    (evalRatPoly (fieldEnvironment 1 (field alternate)) rectanglePolynomial)
    (2*(rectangleValue (field alternate)).scalar) (if alternate then 0 else -2) h ?_
  cases alternate <;> decide +kernel

private theorem separation_contradiction (p q r s : Q') (hp : p ≈ q)
    (hr : r ≈ -2) (hs : s ≈ 0) (hpr : p ≈ r) (hqs : q ≈ s) : False := by
  have bad := Q'.eqv_trans _ _ _ (Q'.eqv_symm hr) (Q'.eqv_trans _ _ _ (Q'.eqv_symm hpr)
    (Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _ hqs hs)))
  exact (by decide : ¬ ((-2 : Q') ≈ 0)) bad

/-- No original plaquette expression equals this rectangle even just on all
rational unit fields. No claim about almost-everywhere or OS-norm equality. -/
theorem no_pointwise_plaquette_recoding (e : PlaquetteExpression 0) :
    ¬ (∀ f : RationalUnitQuaternionGaugeField,
      evalRatPoly (fieldEnvironment 1 f) (lower e) ≈
        evalRatPoly (fieldEnvironment 1 f) rectanglePolynomial) := by
  intro h
  exact separation_contradiction
    (evalRatPoly (fieldEnvironment 1 (field false)) (lower e))
    (evalRatPoly (fieldEnvironment 1 (field true)) (lower e))
    (evalRatPoly (fieldEnvironment 1 (field false)) rectanglePolynomial)
    (evalRatPoly (fieldEnvironment 1 (field true)) rectanglePolynomial)
    (original_lower_equal e) (rectangle_evaluation false) (rectangle_evaluation true)
    (h (field false)) (h (field true))

theorem no_polynomial_plaquette_recoding (e : PlaquetteExpression 0) :
    ¬ RatPolyEqv (lower e) rectanglePolynomial :=
  fun h => no_pointwise_plaquette_recoding e (fun f => h (fieldEnvironment 1 f))

private theorem coeff_eval {p q : RatPoly} (h : RatPolyCoeffEqv p q) (rho : Nat → Q') :
    evalRatPoly rho p ≈ evalRatPoly rho q := by
  have pin : ∀ r : RatPoly, evalRatPoly rho r = ratWeightedSum (evalMono rho) r := by
    intro r
    induction r with
    | nil => rfl
    | cons t ts ih => simp only [evalRatPoly, ratWeightedSum, ih]
  rw [pin,pin]
  exact h _

theorem no_coefficient_plaquette_recoding (e : PlaquetteExpression 0) :
    ¬ RatPolyCoeffEqv (lower e) rectanglePolynomial :=
  fun h => no_polynomial_plaquette_recoding e (coeff_eval h)

/-- The exact half-rectangle normalization of shared-link Schur gluing does
not repair the missing pointwise plaquette-only recoding. -/
theorem no_coefficient_half_rectangle_recoding (e : PlaquetteExpression 0) :
    ¬ RatPolyCoeffEqv (lower e) (polySmul schurFactor rectanglePolynomial) := by
  intro h
  apply no_coefficient_plaquette_recoding (.smul 2 e)
  exact (h.smul 2).trans ((RatPolyCoeffEqv.smul_assoc _ _ _).trans
    ((RatPolyCoeffEqv.smul_coefficient (by decide : 2*schurFactor ≈ (1 : Q')) _).trans
      (RatPolyCoeffEqv.one_smul _)))

end YMGap.Continuum.SU2PlaquetteCharacterNonseparation

#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.unitI
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.unitJ
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.markA
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.markB
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.field
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.plaquette_scalar_equal
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.rectangleHolonomy
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.rectangle_false
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.rectangle_true
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.rectangle_distinguished
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.fieldEnvironment
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.fieldEnvironment_unit
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.original_lower_equal
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.rectanglePolynomial
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.rectangle_evaluation
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.no_pointwise_plaquette_recoding
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.no_polynomial_plaquette_recoding
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.no_coefficient_plaquette_recoding
#print axioms YMGap.Continuum.SU2PlaquetteCharacterNonseparation.no_coefficient_half_rectangle_recoding
