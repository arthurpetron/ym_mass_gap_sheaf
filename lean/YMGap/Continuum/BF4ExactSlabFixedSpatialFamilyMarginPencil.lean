/-
# The ORIGINAL signed margin as a coefficient-independent quadratic pencil

Fix the original nome, cutoff, width, terminal depth and positional face list.
The joint density does not depend on the signed observable coefficients.
Its basis means, product moments and COMPLETE jump-product moments therefore
define one pencil. Its ordered quadratic form is exactly Z^2 times the
existing normalized margin. All repeated faces and signed cross terms remain.

This is exact original-source algebra, not positivity of the pencil, an
accepted useful margin, a feasible-runtime bound or a justified scaling family.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCollectedFamilyMargin
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyKineticUpper

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginPencil

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionSparseCoefficientCollector (collect_coeff)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.BF4CompactActionCPOrder
  (quaternionHaar_append quaternionHaar_polySmul)
open YMGap.Continuum.QuaternionHaarFamilySquare
  (qListSum_congr qListSum_add qListSum_scale)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (jump)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyKineticUpper (family_jump_sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointDensity
  (observableCopies footprintEmbedding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCollectedFamilyMargin
  (pairing mass_positive compress_coeff)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyExpression family_within)
open YMGap.Continuum.BF4WilsonAllNomeFiniteReferenceMargin (referenceCutoff)

local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] pairing plaquette
  BF4ExactSlabFixedSpatialCollectedFamilyMargin.density

private theorem compress_add {s t : Nat} (E : BlockEmbedding s t) (p q : RatPoly) :
    E.compress (polyAdd p q) = polyAdd (E.compress p) (E.compress q) := by
  exact List.map_append

private theorem compress_smul {s t : Nat} (E : BlockEmbedding s t) (a : Q') (p : RatPoly) :
    E.compress (polySmul a p) = polySmul a (E.compress p) := by
  simp only [BlockEmbedding.compress, polySmul, List.map_map, Function.comp_def]

section Pairing

variable (w : Q') (K width depth : Nat) (qs : List Z4Plaq)

private theorem pairing_raw (p : RatPoly) :
    pairing w K width depth qs p ≈
      quaternionHaar (observableCopies width qs).length
        ((footprintEmbedding width qs).compress
          (polyMul (BF4ExactSlabFixedSpatialCollectedFamilyMargin.density w K width depth qs) p)) := by
  unfold pairing BF4ExactSlabFixedSpatialCollectedFamilyMargin.numerator
  exact haar_of_coeff (collect_coeff _)

theorem pairing_congr {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    pairing w K width depth qs p ≈ pairing w K width depth qs q :=
  Q'.eqv_trans _ _ _ (pairing_raw w K width depth qs p)
    (Q'.eqv_trans _ _ _
      (haar_of_coeff (compress_coeff (footprintEmbedding width qs)
        ((RatPolyCoeffEqv.refl _).mul h)))
      (Q'.eqv_symm (pairing_raw w K width depth qs q)))

private theorem pairing_zero : pairing w K width depth qs polyZero ≈ 0 :=
  Q'.eqv_trans _ _ _ (pairing_raw w K width depth qs polyZero)
    (haar_of_coeff (compress_coeff (footprintEmbedding width qs)
      (RatPolyCoeffEqv.mul_zero_right
        (BF4ExactSlabFixedSpatialCollectedFamilyMargin.density w K width depth qs))))

theorem pairing_add (p q : RatPoly) :
    pairing w K width depth qs (polyAdd p q) ≈
      pairing w K width depth qs p + pairing w K width depth qs q := by
  refine Q'.eqv_trans _ _ _ (pairing_raw w K width depth qs _) ?_
  refine Q'.eqv_trans _ _ _
    (haar_of_coeff (compress_coeff (footprintEmbedding width qs)
      (RatPolyCoeffEqv.mul_add_right _ p q))) ?_
  rw [compress_add]
  exact Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
    (Q'.add_eqv_congr'
      (Q'.eqv_symm (pairing_raw w K width depth qs p))
      (Q'.eqv_symm (pairing_raw w K width depth qs q)))

theorem pairing_smul (a : Q') (p : RatPoly) :
    pairing w K width depth qs (polySmul a p) ≈ a * pairing w K width depth qs p := by
  refine Q'.eqv_trans _ _ _ (pairing_raw w K width depth qs _) ?_
  refine Q'.eqv_trans _ _ _
    (haar_of_coeff (compress_coeff (footprintEmbedding width qs)
      (RatPolyCoeffEqv.polyMul_smul_right a _ p))) ?_
  rw [compress_smul]
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ a _)
    (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_symm (pairing_raw w K width depth qs p)))

private theorem pairing_sum {A : Type} (ids : List A) (f : A → RatPoly) :
    pairing w K width depth qs (polySum (ids.map f)) ≈
      qListSum (ids.map fun i => pairing w K width depth qs (f i)) := by
  induction ids with
  | nil => exact pairing_zero w K width depth qs
  | cons i ids ih =>
      exact Q'.eqv_trans _ _ _ (pairing_add w K width depth qs _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)

private theorem pairing_scaled_product (a b : Q') (f g : RatPoly) :
    pairing w K width depth qs (polyMul (polySmul a f) (polySmul b g)) ≈
      (a*b)*pairing w K width depth qs (polyMul f g) :=
  Q'.eqv_trans _ _ _
    (pairing_congr w K width depth qs
      ((RatPolyCoeffEqv.polyMul_smul_left a f (polySmul b g)).trans
        (((RatPolyCoeffEqv.polyMul_smul_right b f g).smul a).trans
          (RatPolyCoeffEqv.smul_assoc a b (polyMul f g)))))
    (pairing_smul w K width depth qs (a*b) (polyMul f g))

end Pairing

/-- Ordered quadratic form. Repeated faces are repeated positions, not erased. -/
def quadratic {A : Type} (ids : List A) (b : A → Q') (M : A → A → Q') : Q' :=
  qListSum (ids.map fun p => qListSum (ids.map fun q => (b p*b q)*M p q))

private theorem quadratic_congr {A : Type} (ids : List A) (b : A → Q')
    {M N : A → A → Q'} (h : ∀ p q, M p q ≈ N p q) :
    quadratic ids b M ≈ quadratic ids b N :=
  qListSum_congr ids _ _ (fun p _ => qListSum_congr ids _ _
    (fun q _ => Q'.mul_eqv_congr_left _ _ _ (h p q)))

private theorem quadratic_add {A : Type} (ids : List A) (b : A → Q')
    (M N : A → A → Q') :
    quadratic ids b (fun p q => M p q+N p q) ≈ quadratic ids b M+quadratic ids b N := by
  refine Q'.eqv_trans _
    (qListSum (ids.map fun p =>
      qListSum (ids.map fun q => (b p*b q)*M p q) +
      qListSum (ids.map fun q => (b p*b q)*N p q))) _
    (qListSum_congr ids _ _ (fun p _ => ?_)) ?_
  · exact Q'.eqv_trans _
      (qListSum (ids.map fun q => (b p*b q)*M p q+(b p*b q)*N p q)) _
      (qListSum_congr ids _ _ (fun q _ => Q'.mul_add_eqv _ _ _))
      (qListSum_add ids _ _)
  · exact qListSum_add ids _ _

private theorem quadratic_scale {A : Type} (ids : List A) (b : A → Q')
    (a : Q') (M : A → A → Q') :
    quadratic ids b (fun p q => a*M p q) ≈ a*quadratic ids b M := by
  refine Q'.eqv_trans _
    (qListSum (ids.map fun p => a*qListSum (ids.map fun q => (b p*b q)*M p q))) _
    (qListSum_congr ids _ _ (fun p _ => ?_)) ?_
  · exact Q'.eqv_trans _ _ _
      (qListSum_congr ids _ _ (fun q _ =>
        poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.mul (.var 2) (.mul (.mul (.var 0) (.var 1)) (.var 3)))
          (by decide) (fun | 0 => b p | 1 => b q | 2 => a | _ => M p q)))
      (qListSum_scale ids _ a)
  · exact qListSum_scale ids _ a

private theorem sum_product {A B : Type} (xs : List A) (ys : List B)
    (f : A → Q') (g : B → Q') :
    qListSum (xs.map fun p => qListSum (ys.map fun q => f p*g q)) ≈
      qListSum (xs.map f)*qListSum (ys.map g) := by
  refine Q'.eqv_trans _ _ _
    (qListSum_congr xs _ _ (fun p _ => qListSum_scale ys g (f p))) ?_
  refine Q'.eqv_trans _ _ _
    (qListSum_congr xs _ _ (fun p _ => Q'.mul_comm_eqv _ _)) ?_
  exact Q'.eqv_trans _ _ _ (qListSum_scale xs f _)
    (Q'.mul_comm_eqv _ _)

private theorem quadratic_mean {A : Type} (ids : List A) (b Amean : A → Q') :
    quadratic ids b (fun p q => Amean p*Amean q) ≈
      qListSum (ids.map fun p => b p*Amean p)*qListSum (ids.map fun p => b p*Amean p) := by
  refine Q'.eqv_trans _
    (qListSum (ids.map fun p => qListSum (ids.map fun q => (b p*Amean p)*(b q*Amean q)))) _
    (qListSum_congr ids _ _ (fun p _ => ?_)) ?_
  · exact qListSum_congr ids _ _ (fun q _ =>
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide) (fun | 0 => b p | 1 => b q | 2 => Amean p | _ => Amean q))
  · exact sum_product ids ids _ _

private theorem quadratic_affine {A : Type} (ids : List A) (b : A → Q')
    (c z h : Q') (C D : A → A → Q') (Amean : A → Q') :
    quadratic ids b (fun p q => c*(z*C p q + -(Amean p*Amean q)) + -((z*h)*D p q)) ≈
      c*(z*quadratic ids b C + -(quadratic ids b (fun p q => Amean p*Amean q))) +
        -((z*h)*quadratic ids b D) := by
  have he := quadratic_congr ids b (fun p q =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.var 3))))
        (.neg (.mul (.mul (.var 1) (.var 4)) (.var 5))))
      (.add (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.neg (.var 0)) (.var 3)))
        (.mul (.neg (.mul (.var 1) (.var 4))) (.var 5)))
      (by decide) (fun
        | 0 => c | 1 => z | 2 => C p q | 3 => Amean p*Amean q | 4 => h | _ => D p q))
  refine Q'.eqv_trans _ _ _ he ?_
  refine Q'.eqv_trans _ _ _ (quadratic_add ids b _ _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (quadratic_add ids b _ _)
        (Q'.add_eqv_congr' (quadratic_scale ids b (c*z) C)
          (quadratic_scale ids b (-c) (fun p q => Amean p*Amean q))))
      (quadratic_scale ids b (-(z*h)) D)) ?_
  exact poly_identity_of_normal_eq
    (.add (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.neg (.var 0)) (.var 3)))
      (.mul (.neg (.mul (.var 1) (.var 4))) (.var 5)))
    (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.var 3))))
      (.neg (.mul (.mul (.var 1) (.var 4)) (.var 5))))
    (by decide) (fun
      | 0 => c | 1 => z | 2 => quadratic ids b C
      | 3 => quadratic ids b (fun p q => Amean p*Amean q)
      | 4 => h | _ => quadratic ids b D)

private theorem pairing_weighted_sum (w : Q') (K width depth : Nat) (qs : List Z4Plaq)
    {A : Type} (ids : List A) (b : A → Q') (f : A → RatPoly) :
    pairing w K width depth qs (polySum (ids.map fun p => polySmul (b p) (f p))) ≈
      qListSum (ids.map fun p => b p*pairing w K width depth qs (f p)) :=
  Q'.eqv_trans _ _ _ (pairing_sum w K width depth qs ids _)
    (qListSum_congr ids _ _ (fun p _ => pairing_smul w K width depth qs (b p) (f p)))

private theorem pairing_weighted_square (w : Q') (K width depth : Nat) (qs : List Z4Plaq)
    {A : Type} (ids : List A) (b : A → Q') (f : A → RatPoly) :
    let span := polySum (ids.map fun p => polySmul (b p) (f p))
    pairing w K width depth qs (polyMul span span) ≈
      quadratic ids b (fun p q => pairing w K width depth qs (polyMul (f p) (f q))) := by
  dsimp only
  refine Q'.eqv_trans _ _ _
    (pairing_congr w K width depth qs (RatPolyCoeffEqv.polySum_mul_right _ _)) ?_
  refine Q'.eqv_trans _ _ _ (pairing_sum w K width depth qs _ _) ?_
  simp only [List.map_map, Function.comp_def]
  apply qListSum_congr ids _ _
  intro p _
  refine Q'.eqv_trans _ _ _
    (pairing_congr w K width depth qs (RatPolyCoeffEqv.mul_polySum_right _ _)) ?_
  refine Q'.eqv_trans _ _ _ (pairing_sum w K width depth qs _ _) ?_
  simp only [List.map_map, Function.comp_def]
  exact qListSum_congr ids _ _ (fun q _ => pairing_scaled_product w K width depth qs _ _ _ _)

/-- The exact original fundamental face character. -/
def basis (width : Nat) (p : Z4Plaq) : RatPoly :=
  characterPolynomial (plaquette width p).scalar 1

private theorem span_eq (width : Nat) (b : Z4Plaq → Q') (qs : List Z4Plaq) :
    spatialSpan width b qs = polySum (qs.map fun p => polySmul (b p) (basis width p)) := by
  induction qs with
  | nil => rfl
  | cons p qs ih => exact congrArg (polyAdd (polySmul (b p) (basis width p))) ih

/-- All entries depend on the original density and list, never on b. -/
def pencilEntry (w : Q') (K width depth : Nat) (qs : List Z4Plaq) (c : Q')
    (p q : Z4Plaq) : Q' :=
  let J := pairing w K width depth qs
  let Z := J polyOne
  c*(Z*J (polyMul (basis width p) (basis width q)) + -(J (basis width p)*J (basis width q))) +
    -((Z*HalfPow.half)*J (polyMul (jump width (basis width p)) (jump width (basis width q))))

/-- Exact rational direction evaluation, retaining the complete ordered matrix. -/
def pencil (w : Q') (K width depth : Nat) (qs : List Z4Plaq)
    (b : Z4Plaq → Q') (c : Q') : Q' :=
  quadratic qs b (pencilEntry w K width depth qs c)

/-- Contraction to the actual original moments; no sign estimate is used. -/
theorem pencil_contract (w : Q') (K width depth : Nat) (qs : List Z4Plaq)
    (b : Z4Plaq → Q') (c : Q') :
    let J := pairing w K width depth qs
    let Z := J polyOne
    let f := spatialSpan width b qs
    pencil w K width depth qs b c ≈
      c*(Z*J (polyMul f f) + -(J f*J f)) +
        -((Z*HalfPow.half)*J (polyMul (jump width f) (jump width f))) := by
  dsimp only
  let J := pairing w K width depth qs
  let f := spatialSpan width b qs
  have hmean : qListSum (qs.map fun p => b p*J (basis width p)) ≈ J f := by
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (congrArg J (span_eq width b qs)))
      (pairing_weighted_sum w K width depth qs qs b (basis width)))
  have hprod : quadratic qs b (fun p q => J (polyMul (basis width p) (basis width q))) ≈
      J (polyMul f f) := by
    rw [show f = polySum (qs.map fun p => polySmul (b p) (basis width p)) from span_eq width b qs]
    exact Q'.eqv_symm (pairing_weighted_square w K width depth qs qs b (basis width))
  have hown : quadratic qs b (fun p q => J (basis width p)*J (basis width q)) ≈ J f*J f :=
    Q'.eqv_trans _ _ _ (quadratic_mean qs b (fun p => J (basis width p)))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hmean)
        (Q'.mul_eqv_congr_left _ _ _ hmean))
  have hjump := family_jump_sum width b qs
  have hjprod : quadratic qs b (fun p q =>
      J (polyMul (jump width (basis width p)) (jump width (basis width q)))) ≈
      J (polyMul (jump width f) (jump width f)) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (pairing_weighted_square w K width depth qs qs b
        (fun p => jump width (basis width p))))
      (pairing_congr w K width depth qs (hjump.mul hjump).symm)
  exact Q'.eqv_trans _ _ _
    (quadratic_affine qs b c (J polyOne) HalfPow.half
      (fun p q => J (polyMul (basis width p) (basis width q)))
      (fun p q => J (polyMul (jump width (basis width p)) (jump width (basis width q))))
      (fun p => J (basis width p)))
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left c _ _ (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left (J polyOne) _ _ hprod) (Q'.neg_eqv_congr _ _ hown)))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hjprod)))

private theorem clear_margin (z r c A C D : Q') (hr : z*r ≈ 1) :
    z*z*(c*(C*r + -((A*r)*(A*r))) + -(HalfPow.half*(D*r))) ≈
      c*(z*C + -(A*A)) + -((z*HalfPow.half)*D) := by
  have h1 : (z*C)*(z*r) ≈ z*C :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr) (Q'.mul_one_eqv _)
  have h2 : (A*A)*((z*r)*(z*r)) ≈ A*A :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (A*A) _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hr)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr) (Q'.mul_one_eqv 1))))
      (Q'.mul_one_eqv _)
  have h3 : ((z*HalfPow.half)*D)*(z*r) ≈ (z*HalfPow.half)*D :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr) (Q'.mul_one_eqv _)
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left c _ _
      (Q'.add_eqv_congr' h1 (Q'.neg_eqv_congr _ _ h2))) (Q'.neg_eqv_congr _ _ h3))
  exact poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 0))
      (.add (.mul (.var 2) (.add (.mul (.var 4) (.var 1))
        (.neg (.mul (.mul (.var 3) (.var 1)) (.mul (.var 3) (.var 1))))))
        (.neg (.mul (.var 6) (.mul (.var 5) (.var 1))))))
    (.add (.mul (.var 2) (.add
      (.mul (.mul (.var 0) (.var 4)) (.mul (.var 0) (.var 1)))
      (.neg (.mul (.mul (.var 3) (.var 3))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))))))
      (.neg (.mul (.mul (.mul (.var 0) (.var 6)) (.var 5)) (.mul (.var 0) (.var 1)))))
    (by decide) (fun | 0 => z | 1 => r | 2 => c | 3 => A | 4 => C | 5 => D | _ => HalfPow.half)

/-- Exact pin to the EXISTING original margin. Positive original mass justifies
clearing both OWN-mean denominators; no matrix positivity is assumed. -/
theorem pencil_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (qs : List Z4Plaq)
    (b : Z4Plaq → Q') (c : Q') :
    let Z := pairing w K width depth qs polyOne
    Z*Z*BF4ExactSlabFixedSpatialCollectedFamilyMargin.margin hw0 hw1 K width hK depth qs b c ≈
      pencil w K width depth qs b c := by
  dsimp only
  let J := pairing w K width depth qs
  let Z := J polyOne
  let f := spatialSpan width b qs
  let r := Q'.recipPos Z (mass_positive hw0 hw1 K width hK depth qs)
  exact Q'.eqv_trans _ _ _
    (clear_margin Z r c (J f) (J (polyMul f f))
      (J (polyMul (jump width f) (jump width f)))
      (Q'.mul_recipPos_eqv Z (mass_positive hw0 hw1 K width hK depth qs)))
    (Q'.eqv_symm (pencil_contract w K width depth qs b c))

/-- Signed slack is equivalent after clearing Z^2, not merely implied. -/
theorem pencil_slack_iff {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (qs : List Z4Plaq)
    (b : Z4Plaq → Q') (c slack : Q') :
    let Z := pairing w K width depth qs polyOne
    Z*Z*slack ≤ pencil w K width depth qs b c ↔
      slack ≤ BF4ExactSlabFixedSpatialCollectedFamilyMargin.margin hw0 hw1 K width hK depth qs b c := by
  dsimp only
  have hz := mass_positive hw0 hw1 K width hK depth qs
  have hzz := Q'.mul_pos hz hz
  have pin := pencil_pin hw0 hw1 K width hK depth qs b c
  constructor
  · intro h
    exact Q'.le_of_mul_le_mul_left
      (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv pin)) hzz
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ h (Q'.le_of_lt hzz)) (Q'.le_of_eqv pin)

/-- A kernel-computed positional regression: removing the repeated index or
discarding signed cross terms changes this value. This is NOT a YM instance. -/
theorem quadratic_repeated_signed :
    quadratic ([0, 1, 0] : List Nat) (fun p => if p = 0 then (1 : Q') else -1)
      (fun _ _ => (1 : Q')) = (1 : Q') := by decide

theorem pencil_empty (w : Q') (K width depth : Nat) (b : Z4Plaq → Q') (c : Q') :
    pencil w K width depth [] b c = 0 := rfl

section Checker

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {base width : Nat} (hwidth : base < width) (qs : List Z4Plaq)
  (b : Z4Plaq → Q') (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)

local notation "wideFaces" =>
  (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
local notation "e" => familyExpression width qs b wideFaces
local notation "he" => family_within width qs b wideFaces

/-- Same original cutoff modulus, padding and strict slack, evaluated through
the coefficient-independent pencil. This assumes no successful direction. -/
def pencilCheck (s : Nat) (c epsilon : Q') (pivot : Nat) : Bool :=
  let Z := pairing w (headCutoff w+pivot) width (s+1) qs polyOne
  decide ((0 : Q') ≤ c ∧ (0 : Q') < epsilon ∧
    referenceCutoff hw0 hw1 e he c (s+1) epsilon ≤ pivot ∧
    Z*Z*(epsilon+epsilon) ≤ pencil w (headCutoff w+pivot) width (s+1) qs b c)

/-- No acceptance is lost or gained: the original finite checker is the actual
consumer, with every normalization and tail/slack condition unchanged. -/
theorem pencilCheck_correct (s : Nat) (c epsilon : Q') (pivot : Nat) :
    pencilCheck hw0 hw1 hwidth qs b hqs s c epsilon pivot = true ↔
      BF4WilsonAllNomeFiniteReferenceMargin.check hw0 hw1 e he s c epsilon pivot = true := by
  have hs := pencil_slack_iff hw0 hw1 (headCutoff w+pivot) width
    (Nat.le_add_right _ _) (s+1) qs b c (epsilon+epsilon)
  have old := BF4ExactSlabFixedSpatialCollectedFamilyMargin.check_correct
    hw0 hw1 hwidth qs b hqs s c epsilon pivot
  constructor
  · intro h
    have H := of_decide_eq_true h
    apply old.mp
    apply decide_eq_true
    exact ⟨H.1, H.2.1, H.2.2.1, hs.mp H.2.2.2⟩
  · intro h
    have H := of_decide_eq_true (old.mpr h)
    apply decide_eq_true
    exact ⟨H.1, H.2.1, H.2.2.1, hs.mpr H.2.2.2⟩

/-- Returns the EXISTING original certificate, never a replacement witness. -/
def pencilCertify (s : Nat) (c epsilon : Q') (pivot : Nat) :
    Option (BF4WilsonAllNomeFiniteReferenceMargin.Certificate hw0 hw1 e he s c) :=
  if h : pencilCheck hw0 hw1 hwidth qs b hqs s c epsilon pivot = true then
    some {
      tolerance := epsilon
      pivot := pivot
      accepted := (pencilCheck_correct hw0 hw1 hwidth qs b hqs s c epsilon pivot).mp h
    }
  else none

end Checker

#print axioms pairing_congr
#print axioms pairing_add
#print axioms pairing_smul
#print axioms quadratic
#print axioms basis
#print axioms pencilEntry
#print axioms pencil
#print axioms pencil_contract
#print axioms pencil_pin
#print axioms pencil_slack_iff
#print axioms quadratic_repeated_signed
#print axioms pencil_empty
#print axioms pencilCheck
#print axioms pencilCheck_correct
#print axioms pencilCertify

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginPencil
