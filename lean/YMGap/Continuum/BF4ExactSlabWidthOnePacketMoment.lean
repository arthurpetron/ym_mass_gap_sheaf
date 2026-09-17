/-
# The complete original width-one heat packet against a fixed hexagon test

All three spatial heat prefixes remain in the original width-one action.
Their private links select exactly spin one against the displayed hexagon
and scalar-square insertion. The arbitrary heat cutoff is not expanded into
a large polynomial, and no other heat factor is treated as a constant.
The carrier keeps all 24 original quaternion coordinates.
-/

import YMGap.Continuum.BF4ExactSlabWidthOneGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
import YMGap.Continuum.SU2QuaternionOrientedWordSelection
import YMGap.Continuum.SU2QuaternionCornerFundamentalMoment

namespace YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq qpow)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (plaquette_fourWord)
open YMGap.Continuum.BF4ExactSlabWidthOneGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier (quaternionBlockMoment)
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra (degree_zero_independent)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported character_independent)
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarHeatCertificate
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.SU2QuaternionCornerFundamentalMoment
  (face01 face02 face12 hexQuaternion hex probe insertion bareProduct)

local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem hex_supported : SupportedQuaternionBlocks 24 hex :=
  character_supported ((((((Supported.coordinate (by decide : 3 < 24)).mul
    (Supported.coordinate (by decide : 2 < 24)).conj).mul
    (Supported.coordinate (by decide : 8 < 24))).mul
    (Supported.coordinate (by decide : 7 < 24)).conj).mul
    (Supported.coordinate (by decide : 5 < 24))).mul
    (Supported.coordinate (by decide : 6 < 24)).conj).scalar 1

theorem probe_supported : SupportedQuaternionBlocks 24 probe :=
  (Supported.coordinate (by decide : 4 < 24)).scalar

theorem insertion_supported : SupportedQuaternionBlocks 24 insertion :=
  supported_polyMul hex_supported (supported_polyMul probe_supported probe_supported)

private theorem hex_degree (slot : Nat) : HasQuaternionBlockDegree slot
    (((((if slot = 3 then 1 else 0) + (if slot = 2 then 1 else 0)) +
      (if slot = 8 then 1 else 0)) + (if slot = 7 then 1 else 0)) +
      (if slot = 5 then 1 else 0) + (if slot = 6 then 1 else 0)) hex :=
  ((((((hasPolyQuaternionBlockDegree_coordinateVariable 3 slot).mul
    (hasPolyQuaternionBlockDegree_coordinateVariable 2 slot).conj).mul
    (hasPolyQuaternionBlockDegree_coordinateVariable 8 slot)).mul
    (hasPolyQuaternionBlockDegree_coordinateVariable 7 slot).conj).mul
    (hasPolyQuaternionBlockDegree_coordinateVariable 5 slot)).mul
    (hasPolyQuaternionBlockDegree_coordinateVariable 6 slot).conj).scalar.smul 2

theorem insertion_private_degree (slot : Nat) (hs : slot = 3 ∨ slot = 6 ∨ slot = 8) :
    HasQuaternionBlockDegree slot 1 insertion := by
  have hh : HasQuaternionBlockDegree slot 1 hex := by
    rcases hs with rfl | rfl | rfl <;> simpa only [Nat.reduceEqDiff, ↓reduceIte, Nat.reduceAdd] using hex_degree _
  have hp : HasQuaternionBlockDegree slot 0 probe := by
    have hn : slot ≠ 4 := by rcases hs with rfl | rfl | rfl <;> decide
    simpa only [if_neg hn] using hasQuaternionBlockDegree_coordinate 4 0 slot (by decide)
  exact hh.mul (hp.mul hp)

/-- The source-piece test has one scalar probe, while insertion has its square. -/
def tester : RatPoly := polyMul hex probe

theorem tester_supported : SupportedQuaternionBlocks 24 tester :=
  supported_polyMul hex_supported probe_supported

theorem tester_first_independent (slot : Nat) (hs : slot = 0 ∨ slot = 1) :
    QuaternionBlockIndependent slot tester := by
  apply degree_zero_independent
  have hh : HasQuaternionBlockDegree slot 0 hex := by
    rcases hs with rfl | rfl <;>
      simpa only [Nat.reduceEqDiff, ↓reduceIte, Nat.reduceAdd] using hex_degree _
  have hp : HasQuaternionBlockDegree slot 0 probe := by
    have hn : slot ≠ 4 := by rcases hs with rfl | rfl <;> decide
    simpa only [if_neg hn] using hasQuaternionBlockDegree_coordinate 4 0 slot (by decide)
  exact hh.mul hp

private theorem degree_one_moment_zero (slot : Nat) (m : List Nat)
    (hd : quaternionBlockDegree m slot = 1) : quaternionBlockMoment slot m = 0 := by
  unfold quaternionBlockMoment sphereMoment4
  split
  · unfold quaternionBlockDegree at hd
    omega
  · rfl

private theorem project_degree_one_zero (slot : Nat) : ∀ p : RatPoly,
    HasQuaternionBlockDegree slot 1 p → RatPolyCoeffEqv (project slot p) polyZero
  | [], _ => .refl _
  | t::rest, hd => by
    intro weight
    change (t.2*quaternionBlockMoment slot t.1)*weight _ +
      ratWeightedSum weight (project slot rest) ≈ 0
    rw [degree_one_moment_zero slot t.1 (hd t List.mem_cons_self)]
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _)) (Q'.zero_mul_eqv _))
        (project_degree_one_zero slot rest (fun s hs => hd s (List.mem_cons_of_mem t hs)) weight))
      (Q'.eqv_of_eq (Q'.add_zero' 0))

private theorem degree_one_haar_zero {blocks slot : Nat} (hi : slot < blocks)
    {p : RatPoly} (hd : HasQuaternionBlockDegree slot 1 p) : quaternionHaar blocks p ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (project_mean blocks slot hi p))
    (haar_of_coeff (project_degree_one_zero slot p hd))

/-- The chosen early fringe projection vanishes coefficientwise, not only in mean. -/
theorem tester_project_two_zero : RatPolyCoeffEqv (project 2 tester) polyZero := by
  apply project_degree_one_zero
  have hh : HasQuaternionBlockDegree 2 1 hex := by
    simpa only [Nat.reduceEqDiff, ↓reduceIte, Nat.reduceAdd] using hex_degree 2
  have hp : HasQuaternionBlockDegree 2 0 probe :=
    hasQuaternionBlockDegree_coordinate 4 0 2 (by decide)
  exact hh.mul hp

private theorem word_degree_zero (slot a b c d : Nat)
    (ha : slot ≠ a) (hb : slot ≠ b) (hc : slot ≠ c) (hd : slot ≠ d) :
    HasQuaternionBlockDegree slot 0 (word a b c d false false true true).scalar := by
  have h := ((((hasPolyQuaternionBlockDegree_coordinateVariable a slot).mul
    (hasPolyQuaternionBlockDegree_coordinateVariable b slot)).mul
    (hasPolyQuaternionBlockDegree_coordinateVariable c slot).conj).mul
    (hasPolyQuaternionBlockDegree_coordinateVariable d slot).conj).scalar
  simpa only [if_neg ha, if_neg hb, if_neg hc, if_neg hd, Nat.zero_add] using h

private def sumValue {A : Type} (f : A → Q') : List A → Q'
  | [] => 0
  | a::xs => f a + sumValue f xs

private theorem sumValue_append {A : Type} (f : A → Q') : ∀ xs ys,
    sumValue f (xs++ys) ≈ sumValue f xs + sumValue f ys
  | [], _ => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | _a::xs, ys => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sumValue_append f xs ys))
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem sumValue_selected (f : Nat → Q') (hz : ∀ s, s ≠ 1 → f s ≈ 0) :
    ∀ k, sumValue f (List.range (k+2)) ≈ f 1
  | 0 => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (hz 0 (by decide)) (Q'.eqv_of_eq (Q'.add_zero' _)))
      (Q'.eqv_of_eq (Q'.zero_add' _))
  | k+1 => by
    rw [show k+1+2 = (k+2)+1 by omega, List.range_succ]
    exact Q'.eqv_trans _ _ _ (sumValue_append f _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (sumValue_selected f hz k)
          (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) (hz (k+2) (by omega))))
        (Q'.eqv_of_eq (Q'.add_zero' _)))

private theorem sum_insert (blocks : Nat) (f : Nat → RatPoly) (p : RatPoly) : ∀ xs,
    quaternionHaar blocks (polyMul (finitePolySum f xs) p) ≈
      sumValue (fun s => quaternionHaar blocks (polyMul (f s) p)) xs
  | [] => Q'.eqv_refl _
  | s::xs => by
    change quaternionHaar blocks (polyMul (polyAdd (f s) (finitePolySum f xs)) p) ≈ _
    rw [polyMul_add_left_exact]
    exact Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_insert blocks f p xs))

private theorem heat_selected (blocks : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (scalar p : RatPoly)
    (hz : ∀ spin, spin ≠ 1 →
      quaternionHaar blocks (polyMul (characterPolynomial scalar spin) p) ≈ 0) :
    quaternionHaar blocks (polyMul (heatPrefix w K scalar) p) ≈
      coeffW w 1 * quaternionHaar blocks (polyMul (characterPolynomial scalar 1) p) := by
  let f := fun spin => quaternionHaar blocks
    (polyMul (polySmul (coeffW w spin) (characterPolynomial scalar spin)) p)
  have hzero (s : Nat) (hs : s ≠ 1) : f s ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks _ _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (hz s hs)) (Q'.mul_zero_eqv _)))
  have hs := sumValue_selected f hzero (K-1)
  rw [show K-1+2 = K+1 by omega] at hs
  exact Q'.eqv_trans _ _ _ (sum_insert blocks _ p (List.range (K+1)))
    (Q'.eqv_trans _ _ _ hs
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
        (quaternionHaar_polySmul blocks _ _)))

private theorem face_select (w : Q') (K : Nat) (hK : 1 ≤ K)
    (a b c d : Fin 24) (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val)
    (hprivate : b.val = 3 ∨ b.val = 6 ∨ b.val = 8) (p : RatPoly)
    (hp : SupportedQuaternionBlocks 24 p) (hd : HasQuaternionBlockDegree b.val 0 p) :
    quaternionHaar 24 (polyMul (heatPrefix w K (word a.val b.val c.val d.val false false true true).scalar)
      (polyMul insertion p)) ≈
      coeffW w 1 * quaternionHaar 24 (polyMul
        (characterPolynomial (word a.val b.val c.val d.val false false true true).scalar 1)
        (polyMul insertion p)) := by
  apply heat_selected 24 w K hK
  intro spin hspin
  cases spin with
  | zero =>
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul _))
      (degree_one_haar_zero b.isLt ((insertion_private_degree b.val hprivate).mul hd))
  | succ spin =>
    exact any_slot_product_zero (by decide) a b c d hab hac had hbc hbd hcd
      false false true true (spin+1) insertion p insertion_supported hp b.val 1
      (Or.inr (Or.inl rfl)) (insertion_private_degree b.val hprivate) hd (by omega)

private theorem finite_sum_coeff {A : Type} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ s, s ∈ xs → RatPolyCoeffEqv (f s) (g s)) →
    RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => .refl _
  | s::xs, h => (h s List.mem_cons_self).add
      (finite_sum_coeff f g xs (fun t ht => h t (List.mem_cons_of_mem s ht)))

private theorem heat_coeff {p q : RatPoly} (h : RatPolyCoeffEqv p q) (w : Q') (K : Nat) :
    RatPolyCoeffEqv (heatPrefix w K p) (heatPrefix w K q) :=
  finite_sum_coeff _ _ _ (fun s _ => (characterPolynomial_coeffEqv h s).smul _)

theorem face01_pin : PolyQuaternionCoeffEqv (plaquette 1 ((0,0,0,0), Z4Plane.p01)) face01 := by
  have hf : ((0,0,0,0), Z4Plane.p01) ∈ spatialFaces 1 := by rw [spatialFaces_one]; simp
  have h := plaquette_fourWord hf
  change PolyQuaternionCoeffEqv _ (word
    ((baseLinks 1).idxOf ((0,0,0,0), Dir4.x0)) ((baseLinks 1).idxOf ((1,0,0,0), Dir4.x1))
    ((baseLinks 1).idxOf ((0,1,0,0), Dir4.x0)) ((baseLinks 1).idxOf ((0,0,0,0), Dir4.x1))
    false false true true) at h
  rw [origin_x0_index, far01_x1_index, far01_x0_index, origin_x1_index] at h
  exact h

theorem face02_pin : PolyQuaternionCoeffEqv (plaquette 1 ((0,0,0,0), Z4Plane.p02)) face02 := by
  have hf : ((0,0,0,0), Z4Plane.p02) ∈ spatialFaces 1 := by rw [spatialFaces_one]; simp
  have h := plaquette_fourWord hf
  change PolyQuaternionCoeffEqv _ (word
    ((baseLinks 1).idxOf ((0,0,0,0), Dir4.x0)) ((baseLinks 1).idxOf ((1,0,0,0), Dir4.x2))
    ((baseLinks 1).idxOf ((0,0,1,0), Dir4.x0)) ((baseLinks 1).idxOf ((0,0,0,0), Dir4.x2))
    false false true true) at h
  rw [origin_x0_index, far02_x2_index, far02_x0_index, origin_x2_index] at h
  exact h

theorem face12_pin : PolyQuaternionCoeffEqv (plaquette 1 ((0,0,0,0), Z4Plane.p12)) face12 := by
  have hf : ((0,0,0,0), Z4Plane.p12) ∈ spatialFaces 1 := by rw [spatialFaces_one]; simp
  have h := plaquette_fourWord hf
  change PolyQuaternionCoeffEqv _ (word
    ((baseLinks 1).idxOf ((0,0,0,0), Dir4.x1)) ((baseLinks 1).idxOf ((0,1,0,0), Dir4.x2))
    ((baseLinks 1).idxOf ((0,0,1,0), Dir4.x1)) ((baseLinks 1).idxOf ((0,0,0,0), Dir4.x2))
    false false true true) at h
  rw [origin_x1_index, far12_x2_index, far12_x1_index, origin_x2_index] at h
  exact h

/-- All three factors of the original action, with no spin selection yet. -/
theorem spatialWeight_pin (w : Q') (K : Nat) :
    RatPolyCoeffEqv (spatialWeight w K 1)
      (polyMul (heatPrefix w K face01.scalar)
        (polyMul (heatPrefix w K face02.scalar) (heatPrefix w K face12.scalar))) := by
  rw [spatialWeight, spatialFaces_one]
  have h12 := ((heat_coeff face12_pin.scalar w K).mul (.refl polyOne)).trans
    (RatPolyCoeffEqv.mul_one _)
  exact (heat_coeff face01_pin.scalar w K).mul ((heat_coeff face02_pin.scalar w K).mul h12)

private theorem word_scalar_supported {a b c d : Nat}
    (ha : a < 24) (hb : b < 24) (hc : c < 24) (hd : d < 24) :
    SupportedQuaternionBlocks 24 (word a b c d false false true true).scalar :=
  ((((Supported.coordinate ha).mul (Supported.coordinate hb)).mul
    (Supported.coordinate hc).conj).mul (Supported.coordinate hd).conj).scalar

private theorem heat_supported {p : RatPoly} (hp : SupportedQuaternionBlocks 24 p)
    (w : Q') (K : Nat) : SupportedQuaternionBlocks 24 (heatPrefix w K p) := by
  unfold heatPrefix
  induction List.range (K+1) with
  | nil => intro t ht; exact False.elim (List.not_mem_nil ht)
  | cons s ss ih => exact supported_add (support_smul (character_supported hp s) _) ih

private theorem heat_degree_zero {slot : Nat} {p : RatPoly} (hp : HasQuaternionBlockDegree slot 0 p)
    (w : Q') (K : Nat) : HasQuaternionBlockDegree slot 0 (heatPrefix w K p) := by
  unfold heatPrefix
  induction List.range (K+1) with
  | nil => exact hasQuaternionBlockDegree_zero slot 0
  | cons s ss ih => exact ((character_independent hp s).smul _).add ih

private theorem arrange_first (a b c x : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul a (polyMul b c)) x)
      (polyMul a (polyMul x (polyMul b c))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
    (.mul (.var 0) (.mul (.var 3) (.mul (.var 1) (.var 2))))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => x)

private theorem swap_selected (a b c x : RatPoly) :
    RatPolyCoeffEqv (polyMul a (polyMul x (polyMul b c)))
      (polyMul b (polyMul x (polyMul a c))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 3) (.mul (.var 1) (.var 2))))
    (.mul (.var 1) (.mul (.var 3) (.mul (.var 0) (.var 2))))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => x)

private theorem select_third (a b c x : RatPoly) :
    RatPolyCoeffEqv (polyMul b (polyMul x (polyMul a c)))
      (polyMul c (polyMul x (polyMul a b))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 1) (.mul (.var 3) (.mul (.var 0) (.var 2))))
    (.mul (.var 2) (.mul (.var 3) (.mul (.var 0) (.var 1))))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => x)

private theorem finish_order (a b c x : RatPoly) :
    RatPolyCoeffEqv (polyMul c (polyMul x (polyMul a b)))
      (polyMul a (polyMul b (polyMul c x))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 2) (.mul (.var 3) (.mul (.var 0) (.var 1))))
    (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => x)

private theorem triple_scale (c v : Q') : c*(c*(c*v)) ≈ qpow c 3*v :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.var 1))))
    (.mul (.pow (.var 0) 3) (.var 1)) (by decide) (fun | 0 => c | _ => v)

/-- Exact three-face spin selection inside the COMPLETE original action.
The other two heat prefixes are retained at each private-link elimination. -/
theorem packet_fundamental_pin (w : Q') (K : Nat) (hK : 1 ≤ K) :
    quaternionHaar 24 (polyMul (spatialWeight w K 1) insertion) ≈
      qpow (coeffW w 1) 3 * quaternionHaar 24 bareProduct := by
  let A := heatPrefix w K face01.scalar
  let B := heatPrefix w K face02.scalar
  let C := heatPrefix w K face12.scalar
  let a := characterPolynomial face01.scalar 1
  let b := characterPolynomial face02.scalar 1
  let c := characterPolynomial face12.scalar 1
  have sa : SupportedQuaternionBlocks 24 face01.scalar :=
    word_scalar_supported (by decide) (by decide) (by decide) (by decide)
  have sb : SupportedQuaternionBlocks 24 face02.scalar :=
    word_scalar_supported (by decide) (by decide) (by decide) (by decide)
  have sc : SupportedQuaternionBlocks 24 face12.scalar :=
    word_scalar_supported (by decide) (by decide) (by decide) (by decide)
  have a6 := word_degree_zero 6 0 3 2 1 (by decide) (by decide) (by decide) (by decide)
  have a8 := word_degree_zero 8 0 3 2 1 (by decide) (by decide) (by decide) (by decide)
  have b3 := word_degree_zero 3 0 6 5 4 (by decide) (by decide) (by decide) (by decide)
  have b8 := word_degree_zero 8 0 6 5 4 (by decide) (by decide) (by decide) (by decide)
  have c3 := word_degree_zero 3 1 8 7 4 (by decide) (by decide) (by decide) (by decide)
  have c6 := word_degree_zero 6 1 8 7 4 (by decide) (by decide) (by decide) (by decide)
  have h1 : quaternionHaar 24 (polyMul A (polyMul insertion (polyMul B C))) ≈
      coeffW w 1 * quaternionHaar 24 (polyMul a (polyMul insertion (polyMul B C))) :=
    face_select w K hK ⟨0,by decide⟩ ⟨3,by decide⟩ ⟨2,by decide⟩ ⟨1,by decide⟩
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl rfl)
      (polyMul B C) (supported_polyMul (heat_supported sb w K) (heat_supported sc w K))
      ((heat_degree_zero b3 w K).mul (heat_degree_zero c3 w K))
  have h2 : quaternionHaar 24 (polyMul a (polyMul insertion (polyMul B C))) ≈
      coeffW w 1 * quaternionHaar 24 (polyMul b (polyMul insertion (polyMul a C))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (swap_selected a B C insertion))
      (face_select w K hK ⟨0,by decide⟩ ⟨6,by decide⟩ ⟨5,by decide⟩ ⟨4,by decide⟩
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inr (Or.inl rfl))
        (polyMul a C) (supported_polyMul (character_supported sa 1) (heat_supported sc w K))
        ((character_independent a6 1).mul (heat_degree_zero c6 w K)))
  have h3 : quaternionHaar 24 (polyMul b (polyMul insertion (polyMul a C))) ≈
      coeffW w 1 * quaternionHaar 24 (polyMul c (polyMul insertion (polyMul a b))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (select_third a b C insertion))
      (face_select w K hK ⟨1,by decide⟩ ⟨8,by decide⟩ ⟨7,by decide⟩ ⟨4,by decide⟩
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inr (Or.inr rfl))
        (polyMul a b) (supported_polyMul (character_supported sa 1) (character_supported sb 1))
        ((character_independent a8 1).mul (character_independent b8 1)))
  have h4 : quaternionHaar 24 (polyMul c (polyMul insertion (polyMul a b))) ≈
      quaternionHaar 24 bareProduct := haar_of_coeff (finish_order a b c insertion)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (((spatialWeight_pin w K).mul_right insertion).trans (arrange_first A B C insertion)))
    (Q'.eqv_trans _ _ _ h1
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ h2
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ h3
            (Q'.mul_eqv_congr_left _ _ _ h4)))))
        (triple_scale _ _)))

private theorem coefficient_pin (w : Q') :
    qpow (coeffW w 1) 3 * Q'.mkPos 1 16 (by decide) ≈
      Q'.mkPos 1 2 (by decide) * qpow w 9 := by
  have h : qpow (coeffW w 1) 3 * Q'.mkPos 1 16 (by decide) ≈
      (8 * Q'.mkPos 1 16 (by decide)) * qpow w 9 :=
    poly_identity_of_normal_eq
      (.mul (.pow (.mul (.const 2) (.pow (.var 0) 3)) 3) (.var 1))
      (.mul (.mul (.const 8) (.var 1)) (.pow (.var 0) 9))
      (by decide) (fun | 0 => w | _ => Q'.mkPos 1 16 (by decide))
  exact Q'.eqv_trans _ _ _ h
    (Q'.mul_eqv_congr_right _ _ _
      (by decide : (8 : Q') * Q'.mkPos 1 16 (by decide) ≈ Q'.mkPos 1 2 (by decide)))

/-- The COMPLETE original width-one heat packet, every K containing spin one.
The nine occurring coordinates are still integrated inside H24. -/
theorem packet_moment (w : Q') (K : Nat) (hK : 1 ≤ K) :
    quaternionHaar 24 (polyMul (spatialWeight w K 1) insertion) ≈
      Q'.mkPos 1 2 (by decide) * qpow w 9 :=
  Q'.eqv_trans _ _ _ (packet_fundamental_pin w K hK)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (SU2QuaternionCornerFundamentalMoment.bare_moment_extended 24 (by decide)))
      (coefficient_pin w))

end YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment

#print axioms YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment.hex_supported
#print axioms YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment.probe_supported
#print axioms YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment.insertion_supported
#print axioms YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment.insertion_private_degree
#print axioms YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment.tester_supported
#print axioms YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment.tester_first_independent
#print axioms YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment.tester_project_two_zero
#print axioms YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment.face01_pin
#print axioms YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment.face02_pin
#print axioms YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment.face12_pin
#print axioms YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment.spatialWeight_pin
#print axioms YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment.packet_fundamental_pin
#print axioms YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment.packet_moment
