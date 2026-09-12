/-
# The original signed slab form uses the literal reflected observable

At every spin cutoff and rational heat parameter, the upper observable is
the actual link-variable time reflection of the lower observable in every
Haar row with a spectator on the same 116 physical links. Combining this
identity with the local interface heat product gives the original signed
quadratic as Haar(F * (H * theta F)). No comparison measure is substituted.

This is the geometric observable pin, NOT positivity of that form. A positive
reflected-channel resolution of H, its link-local composition, physical time,
the exact-law completed gap and continuum/Clay construction remain open.
-/

import YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct
import YMGap.Continuum.BF4ExactSlabVacuumReflection
import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor

namespace YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct
open YMGap.Continuum.BF4ExactSlabObservableHaarForm
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private abbrev Supported := SupportedQuaternionBlocks 116
private abbrev theta := reflectCorrectedSlabPolynomial 1

private theorem slab_blocks : (boundaryCompleteSlabLinks 1).length = 116 :=
  correctedSlabLinks_extent_one_length

private theorem reflect_support (p : RatPoly) : Supported (theta p) := by
  have h := reflectCorrectedSlabPolynomial_support 1 p
  rw [slab_blocks] at h
  exact h

private theorem character_support (face : Z4Plaq) (spin : Nat) :
    Supported (characterPolynomial (correctedSlabPlaquettePolynomial 1 face).scalar spin) := by
  have h := correctedSlabPlaquetteSpinFactor_support 1 (fun _ => spin) face
  rw [slab_blocks] at h
  exact h

private theorem support_zero (blocks : Nat) : SupportedQuaternionBlocks blocks polyZero := by
  intro term hterm
  simp only [polyZero, List.not_mem_nil] at hterm

private theorem support_one (blocks : Nat) : SupportedQuaternionBlocks blocks polyOne := by
  intro term hterm
  simp only [polyOne, List.mem_singleton] at hterm
  subst term
  simp

private theorem support_add {p q : RatPoly} (hp : Supported p) (hq : Supported q) :
    Supported (polyAdd p q) := by
  intro term hterm
  rcases List.mem_append.mp hterm with hterm | hterm
  · exact hp term hterm
  · exact hq term hterm

private theorem support_smul {a : Q'} {p : RatPoly} (hp : Supported p) : Supported (polySmul a p) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact hp source hsource

private def RowEqv (left right : RatPoly) : Prop :=
  ∀ insertion, Supported insertion →
    quaternionHaar 116 (polyMul insertion left) ≈ quaternionHaar 116 (polyMul insertion right)

private theorem RowEqv.refl (p : RatPoly) : RowEqv p p := fun _ _ => Q'.eqv_refl _
private theorem RowEqv.symm {p q : RatPoly} (h : RowEqv p q) : RowEqv q p :=
  fun s hs => Q'.eqv_symm (h s hs)
private theorem RowEqv.trans {p q r : RatPoly} (h : RowEqv p q) (k : RowEqv q r) : RowEqv p r :=
  fun s hs => Q'.eqv_trans _ _ _ (h s hs) (k s hs)

private theorem prefix_row {p q : RatPoly} (h : QuaternionPrefixPolynomialEqv 116 p q)
    (hp : Supported p) (hq : Supported q) : RowEqv p q := by
  intro s hs
  exact quaternionHaar_prefixPolynomialEqv 116
    (QuaternionPrefixPolynomialEqv.mul (QuaternionPrefixPolynomialEqv.refl 116 s) h)
    (supported_polyMul hs hp) (supported_polyMul hs hq)

private theorem RowEqv.add {p p' q q' : RatPoly} (hp : RowEqv p p') (hq : RowEqv q q') :
    RowEqv (polyAdd p q) (polyAdd p' q') := by
  intro s hs
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right 116 s p q)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (hp s hs) (hq s hs))
      (Q'.eqv_symm (quaternionHaar_polyMul_add_right 116 s p' q')))

private theorem RowEqv.smul (a : Q') {p q : RatPoly} (h : RowEqv p q) :
    RowEqv (polySmul a p) (polySmul a q) := by
  intro s hs
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right 116 a s p)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (h s hs))
      (Q'.eqv_symm (quaternionHaar_polyMul_smul_right 116 a s q)))

private theorem RowEqv.mul_left {p q : RatPoly} (f : RatPoly) (hf : Supported f)
    (h : RowEqv p q) : RowEqv (polyMul f p) (polyMul f q) := by
  intro s hs
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc 116 s f p))
    (Q'.eqv_trans _ _ _ (h (polyMul s f) (supported_polyMul hs hf))
      (quaternionHaar_polyMul_assoc 116 s f q))

private theorem row_comm (p q : RatPoly) : RowEqv (polyMul p q) (polyMul q p) :=
  fun s _ => quaternionHaar_polyMul_middle_comm 116 s p q

private theorem RowEqv.mul {p p' q q' : RatPoly} (hp : RowEqv p p') (hq : RowEqv q q')
    (hp' : Supported p') (hsq : Supported q) : RowEqv (polyMul p q) (polyMul p' q') :=
  (row_comm p q).trans ((hp.mul_left q hsq).trans
    ((row_comm q p').trans (hq.mul_left p' hp')))

private theorem reflect_smul_row (a : Q') (p : RatPoly) :
    RowEqv (theta (polySmul a p)) (polySmul a (theta p)) := by
  have h := reflectCorrectedSlabPolynomial_smul_prefix 1 a p
  rw [slab_blocks] at h
  exact prefix_row h (reflect_support _) (support_smul (reflect_support p))

private theorem reflect_mul_row (p q : RatPoly) :
    RowEqv (theta (polyMul p q)) (polyMul (theta p) (theta q)) := by
  have h := reflectCorrectedSlabPolynomial_mul_prefix 1 p q
  rw [slab_blocks] at h
  exact prefix_row h (reflect_support _) (supported_polyMul (reflect_support p) (reflect_support q))

private theorem weighted_support (w : Q') (K : Nat) (state : EdgeLabelling) (id : Nat) :
    Supported (weightedFacePolynomial w K state id) :=
  support_smul
    (character_support (slabPlaquetteAt 1 id) (state id))

/-- Every heat-weighted face is transported with its actual quaternion word,
spin and original heat coefficient, with any supported spectator retained. -/
theorem weightedFacePolynomial_reflection_insert (w : Q') (K : Nat) (state : EdgeLabelling)
    {id : Nat} (hid : id ∈ slabPhysicalFaceEdges 1) (insertion : RatPoly)
    (hsupport : SupportedQuaternionBlocks 116 insertion) :
    quaternionHaar 116 (polyMul insertion (reflectCorrectedSlabPolynomial 1
      (weightedFacePolynomial w K state id))) ≈
    quaternionHaar 116 (polyMul insertion
      (weightedFacePolynomial w K (fun j => state (slabFaceReflectId 1 j)) (slabFaceReflectId 1 id))) := by
  have hface : RowEqv
      (theta (characterPolynomial (correctedSlabPlaquettePolynomial 1 (slabPlaquetteAt 1 id)).scalar (state id)))
      (characterPolynomial (correctedSlabPlaquettePolynomial 1
        (timeReflectPlaquette 1 (slabPlaquetteAt 1 id))).scalar (state id)) := by
    intro s hs
    have h := correctedSlabPlaquetteSpinFactor_reflection_insert (fun _ => state id)
      (slabPlaquetteAt_mem hid) s
    rw [slab_blocks] at h
    exact h hs
  unfold weightedFacePolynomial
  simp only [slabFaceReflectId_involutive hid, slabPlaquetteAt_slabFaceReflectId hid]
  exact ((reflect_smul_row _ _).trans (hface.smul _)) insertion hsupport

private theorem fold_supported {A : Type} (f : A → RatPoly) (hf : ∀ a, Supported (f a)) :
    ∀ ids : List A, Supported (ids.foldr (fun a p => polyMul (f a) p) polyOne)
  | [] => support_one _
  | a :: rest => supported_polyMul (hf a) (fold_supported f hf rest)

private theorem reflected_fold (f g : Nat → RatPoly) (hg : ∀ id, Supported (g id)) :
    ∀ ids : List Nat, (∀ id, id ∈ ids → RowEqv (theta (f id)) (g id)) →
      RowEqv (theta (ids.foldr (fun id p => polyMul (f id) p) polyOne))
        (ids.foldr (fun id p => polyMul (g id) p) polyOne)
  | [], _ => by
    have h := reflectCorrectedSlabPolynomial_character_prefix 1 polyZero 0
    rw [slab_blocks] at h
    exact prefix_row h (reflect_support polyOne) (support_one _)
  | id :: rest, h =>
    (reflect_mul_row _ _).trans ((h id List.mem_cons_self).mul
      (reflected_fold f g hg rest (fun j hj => h j (List.mem_cons_of_mem id hj)))
      (hg id) (reflect_support _))

private theorem reflected_lower_ids :
    ((centralLowerFaceIds 0).map (slabFaceReflectId 1)).Perm (centralUpperFaceIds 0) := by
  have h := (centralUpperFaceIds_reflection_perm 0).map (slabFaceReflectId 1)
  have hi : ((centralUpperFaceIds 0).map (slabFaceReflectId 1)).map (slabFaceReflectId 1) =
      centralUpperFaceIds 0 := by
    rw [List.map_map]
    have hm : (centralUpperFaceIds 0).map (fun id => slabFaceReflectId 1 (slabFaceReflectId 1 id)) =
        (centralUpperFaceIds 0).map (fun id => id) := by
      apply List.map_congr_left
      intro id hid
      exact slabFaceReflectId_involutive (mem_centralUpperFaceIds.mp hid).1
    exact hm.trans (List.map_id _)
  change (((centralUpperFaceIds 0).map (slabFaceReflectId 1)).map (slabFaceReflectId 1)).Perm _ at h
  rw [hi] at h
  exact h.symm

/-- The entire heat-dressed upper half is the literal link reflection of the
lower half, not just a matching face-label presentation. -/
theorem lowerPolynomial_reflection_insert (w : Q') (K : Nat) (state : EdgeLabelling)
    (insertion : RatPoly) (hsupport : SupportedQuaternionBlocks 116 insertion) :
    quaternionHaar 116 (polyMul insertion (reflectCorrectedSlabPolynomial 1 (lowerPolynomial w K state))) ≈
      quaternionHaar 116 (polyMul insertion (upperPolynomial w K state)) := by
  rw [lowerPolynomial_eq_fold, upperPolynomial_eq_fold]
  let upper := weightedFacePolynomial w K (fun j => state (slabFaceReflectId 1 j))
  have href := reflected_fold (weightedFacePolynomial w K state)
    (fun id => upper (slabFaceReflectId 1 id)) (fun id => weighted_support w K _ _)
    (centralLowerFaceIds 0) (fun id hid s hs =>
      weightedFacePolynomial_reflection_insert w K state (mem_centralLowerFaceIds.mp hid).1 s hs)
  refine Q'.eqv_trans _ _ _ (href insertion hsupport) ?_
  have hperm := quaternionHaar_factorFold_perm 116 upper reflected_lower_ids insertion
  simpa only [List.foldr_map] using hperm

private theorem sum_supported {A : Type} (f : A → RatPoly) (hf : ∀ a, Supported (f a)) :
    ∀ ids : List A, Supported (finitePolySum f ids)
  | [] => support_zero _
  | a :: rest => support_add (hf a) (sum_supported f hf rest)

/-- The original observable is supported on the actual 116-link carrier. -/
theorem lowerObservable_support (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    SupportedQuaternionBlocks 116 (lowerObservable w K c) := by
  apply sum_supported
  intro state
  apply support_smul
  rw [lowerPolynomial_eq_fold]
  exact fold_supported _ (weighted_support w K state) _

/-- Every local interface heat factor remains on the same physical carrier. -/
theorem interfaceHeatProduct_support (w : Q') (K : Nat) :
    SupportedQuaternionBlocks 116 (interfaceHeatProduct w K) := by
  apply fold_supported
  intro id
  apply sum_supported
  intro spin
  exact support_smul
    (character_support (slabPlaquetteAt 1 id) spin)

private theorem reflected_sum {A : Type} (f g : A → RatPoly)
    (h : ∀ a, RowEqv (theta (f a)) (g a)) : ∀ ids : List A,
      RowEqv (theta (finitePolySum f ids)) (finitePolySum g ids)
  | [] => RowEqv.refl _
  | a :: rest => by
    change RowEqv (theta (polyAdd (f a) (finitePolySum f rest))) _
    rw [theta, reflectCorrectedSlabPolynomial_add]
    exact (h a).add (reflected_sum f g h rest)

/-- Arbitrary SIGNED observable coefficients commute with the literal time
reflection under every spectator on the actual slab-link carrier. -/
theorem lowerObservable_reflection_insert (w : Q') (K : Nat) (c : EdgeLabelling → Q')
    (insertion : RatPoly) (hsupport : SupportedQuaternionBlocks 116 insertion) :
    quaternionHaar 116 (polyMul insertion (reflectCorrectedSlabPolynomial 1 (lowerObservable w K c))) ≈
      quaternionHaar 116 (polyMul insertion (upperObservable w K c)) := by
  have h := reflected_sum (fun state => polySmul (c state) (lowerPolynomial w K state))
    (fun state => polySmul (c state) (upperPolynomial w K state))
    (fun state => (reflect_smul_row _ _).trans
      (RowEqv.smul _ (lowerPolynomial_reflection_insert w K state))) (centralHalfStates K 0)
  exact h insertion hsupport

/-- ORIGINAL signed bilinear form = Haar(F_left * (H * theta F_right)).
H is the product of the 24 actual face heat kernels, not a comparison law. -/
theorem exact_bilinear_eq_reflectedHaar (w : Q') (K : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K 0) left right (exactCorrectedSlabReflectedKernel w K 0) ≈
      quaternionHaar 116 (polyMul (lowerObservable w K left)
        (polyMul (interfaceHeatProduct w K) (reflectCorrectedSlabPolynomial 1 (lowerObservable w K right)))) := by
  refine Q'.eqv_trans _ _ _ (exact_bilinear_eq_productHaar w K left right) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc 116 _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm
    (lowerObservable_reflection_insert w K right _
      (supported_polyMul (lowerObservable_support w K left) (interfaceHeatProduct_support w K)))) ?_
  exact quaternionHaar_polyMul_assoc 116 _ _ _

/-- The exact quadratic uses the SAME lower observable and its literal
reflection. This equality alone asserts neither positivity nor a gap. -/
theorem exact_quadratic_eq_reflectedHaar (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    exactSlabAllCutoffQuadratic w K c ≈
      quaternionHaar 116 (polyMul (lowerObservable w K c)
        (polyMul (interfaceHeatProduct w K) (reflectCorrectedSlabPolynomial 1 (lowerObservable w K c)))) :=
  exact_bilinear_eq_reflectedHaar w K c c

end YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm

#print axioms YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm.weightedFacePolynomial_reflection_insert
#print axioms YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm.lowerPolynomial_reflection_insert
#print axioms YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm.lowerObservable_support
#print axioms YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm.interfaceHeatProduct_support
#print axioms YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm.lowerObservable_reflection_insert
#print axioms YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm.exact_bilinear_eq_reflectedHaar
#print axioms YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm.exact_quadratic_eq_reflectedHaar
