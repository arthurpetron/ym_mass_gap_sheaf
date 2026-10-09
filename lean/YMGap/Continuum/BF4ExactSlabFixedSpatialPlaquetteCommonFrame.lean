/-
# Actual fixed-spatial plaquette first jets in one common prefix frame

The original LEFT link derivatives have signs +,+,-,- and prefixes
1,q0,q0*q1*q2,P. All unit cancellations are arbitrary-insertion Haar
relations on the original width-only carrier. Only raw coefficient
identities are differentiated. No weighted Hessian or survival bound is
asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
import YMGap.Continuum.SU2QuaternionLeftRightAngularAction
import YMGap.Continuum.QuaternionHaarUnitScalarSquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCommonFrame

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionPairedFrameAt
open YMGap.Continuum.SU2QuaternionLeftRightAngularAction
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (Supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local instance : Mul PolyQuaternion := ⟨PolyQuaternion.mul⟩

private theorem cases4 (s : Fin 4) : s=0 ∨ s=1 ∨ s=2 ∨ s=3 := by
  simp only [Fin.ext_iff]
  omega

/-- Literal physical boundary order, not a freely selected four-word. -/
def slotLink (p : Z4Plaq) (s : Fin 4) : Z4Link :=
  match s.val with
  | 0 => (p.1, (dirsOf p.2).1)
  | 1 => (addE p.1 (dirsOf p.2).1, (dirsOf p.2).2)
  | 2 => (addE p.1 (dirsOf p.2).2, (dirsOf p.2).1)
  | _ => (p.1, (dirsOf p.2).2)

def slotIndex (width : Nat) (p : Z4Plaq) (s : Fin 4) : Nat :=
  (baseLinks width).idxOf (slotLink p s)

theorem slot_physical {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) (s : Fin 4) :
    slotLink p s ∈ baseLinks width := by
  apply face_link_mem_base hp
  rcases cases4 s with rfl | rfl | rfl | rfl <;> simp [slotLink, edgesOf]

theorem slotIndex_lt {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) (s : Fin 4) :
    slotIndex width p s < (baseLinks width).length :=
  List.idxOf_lt_length_of_mem (slot_physical hp s)

theorem slotIndex_ne {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) {s t : Fin 4} (hst : s ≠ t) :
    slotIndex width p s ≠ slotIndex width p t := by
  have hn :
      ((p.1, (dirsOf p.2).1) ≠ (p.1, (dirsOf p.2).2) ∧
        ((p.1, (dirsOf p.2).1) ≠ (addE p.1 (dirsOf p.2).2, (dirsOf p.2).1) ∧
         (p.1, (dirsOf p.2).1) ≠ (addE p.1 (dirsOf p.2).1, (dirsOf p.2).2))) ∧
      (((p.1, (dirsOf p.2).2) ≠ (addE p.1 (dirsOf p.2).2, (dirsOf p.2).1) ∧
         (p.1, (dirsOf p.2).2) ≠ (addE p.1 (dirsOf p.2).1, (dirsOf p.2).2)) ∧
       (addE p.1 (dirsOf p.2).2, (dirsOf p.2).1) ≠
         (addE p.1 (dirsOf p.2).1, (dirsOf p.2).2)) := by
    simpa only [edgesOf, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, or_false, not_or, not_false_eq_true, and_true]
      using edgesOf_nodup p
  intro he
  have he' := idxOf_injective_on_members (slot_physical hp s) (slot_physical hp t) he
  rcases cases4 s with rfl | rfl | rfl | rfl <;>
    rcases cases4 t with rfl | rfl | rfl | rfl <;>
    simp only [slotLink] at he' <;>
    first | exact hst rfl | exact hn.1.1 he' | exact hn.1.2.1 he' |
      exact hn.1.2.2 he' | exact hn.2.1.1 he' | exact hn.2.1.2 he' |
      exact hn.2.2 he' | exact hn.1.1 he'.symm | exact hn.1.2.1 he'.symm |
      exact hn.1.2.2 he'.symm | exact hn.2.1.1 he'.symm |
      exact hn.2.1.2 he'.symm | exact hn.2.2 he'.symm

def factor (width : Nat) (p : Z4Plaq) (s : Fin 4) : PolyQuaternion :=
  orientedCoordinateQuaternion (slotIndex width p s) (decide (2 ≤ s.val))

def fourProduct (q0 q1 q2 q3 : PolyQuaternion) : PolyQuaternion :=
  ((q0 * q1) * q2) * q3

def faceProduct (width : Nat) (p : Z4Plaq) : PolyQuaternion :=
  fourProduct (factor width p 0) (factor width p 1)
    (factor width p 2) (factor width p 3)

def commonPrefix (width : Nat) (p : Z4Plaq) (s : Fin 4) : PolyQuaternion :=
  match s.val with
  | 0 => PolyQuaternion.one
  | 1 => factor width p 0
  | 2 => (factor width p 0 * factor width p 1) * factor width p 2
  | _ => faceProduct width p

def signed (s : Fin 4) (q : PolyQuaternion) : PolyQuaternion :=
  if 2 ≤ s.val then negQuaternion q else q

/-- The actual common-frame adjoint vector; negative inverse-link signs
are outside the conjugation, and there is no normalization factor 1/2. -/
def commonVector (width : Nat) (p : Z4Plaq) (s : Fin 4) (i : Fin 3) : PolyQuaternion :=
  signed s ((commonPrefix width p s * imaginaryBasis i) * PolyQuaternion.conj (commonPrefix width p s))

theorem original_word {width : Nat} {p : Z4Plaq} (hp : p ∈ spatialFaces width) :
    PolyQuaternionCoeffEqv (plaquette width p) (faceProduct width p) :=
  plaquette_fourWord hp

private theorem factor_supported {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) (s : Fin 4) :
    Supported (baseLinks width).length (factor width p s) := by
  rcases cases4 s with rfl | rfl | rfl | rfl
  · exact Supported.coordinate (slotIndex_lt hp 0)
  · exact Supported.coordinate (slotIndex_lt hp 1)
  · exact (Supported.coordinate (slotIndex_lt hp 2)).conj
  · exact (Supported.coordinate (slotIndex_lt hp 3)).conj

theorem prefix_supported {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) (s : Fin 4) :
    Supported (baseLinks width).length (commonPrefix width p s) := by
  rcases cases4 s with rfl | rfl | rfl | rfl
  · exact Supported.one _
  · exact factor_supported hp 0
  · exact ((factor_supported hp 0).mul (factor_supported hp 1)).mul (factor_supported hp 2)
  · exact (((factor_supported hp 0).mul (factor_supported hp 1)).mul
      (factor_supported hp 2)).mul (factor_supported hp 3)

private theorem factor_unit {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) (s : Fin 4) :
    HaarCarrierEqv (baseLinks width).length (polyQuaternionNorm (factor width p s)) polyOne := by
  rcases cases4 s with rfl | rfl | rfl | rfl
  · exact haarNorm_coordinate (slotIndex_lt hp 0)
  · exact haarNorm_coordinate (slotIndex_lt hp 1)
  · exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
      (haarNorm_coordinate (slotIndex_lt hp 2))
  · exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
      (haarNorm_coordinate (slotIndex_lt hp 3))

/-- Produced unit norm of every actual prefix, with arbitrary insertions. -/
theorem prefix_unit {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) (s : Fin 4) :
    HaarCarrierEqv (baseLinks width).length (polyQuaternionNorm (commonPrefix width p s)) polyOne := by
  rcases cases4 s with rfl | rfl | rfl | rfl
  · exact RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one
  · exact factor_unit hp 0
  · exact haarNorm_mul (haarNorm_mul (factor_unit hp 0) (factor_unit hp 1)) (factor_unit hp 2)
  · exact haarNorm_mul (haarNorm_mul (haarNorm_mul (factor_unit hp 0)
      (factor_unit hp 1)) (factor_unit hp 2)) (factor_unit hp 3)

private def qAdd (p q : PolyQuaternion) : PolyQuaternion :=
  ⟨polyAdd p.scalar q.scalar, polyAdd p.iPart q.iPart,
    polyAdd p.jPart q.jPart, polyAdd p.kPart q.kPart⟩
private def exprAdd (p q : PolyQuaternionExpr) : PolyQuaternionExpr :=
  ⟨.add p.scalar q.scalar, .add p.iPart q.iPart, .add p.jPart q.jPart, .add p.kPart q.kPart⟩
private def exprNeg (p : PolyQuaternionExpr) : PolyQuaternionExpr :=
  ⟨.neg p.scalar, .neg p.iPart, .neg p.jPart, .neg p.kPart⟩
private def evalQ (env : Nat → RatPoly) (q : PolyQuaternionExpr) : PolyQuaternion :=
  ⟨coeffEvalExpr env q.scalar, coeffEvalExpr env q.iPart,
    coeffEvalExpr env q.jPart, coeffEvalExpr env q.kPart⟩
private def env4 (p q r s : PolyQuaternion) : Nat → RatPoly
  | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
  | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | 7 => q.kPart
  | 8 => r.scalar | 9 => r.iPart | 10 => r.jPart | 11 => r.kPart
  | 12 => s.scalar | 13 => s.iPart | 14 => s.jPart | 15 => s.kPart
  | _ => polyZero
private theorem reflect (p q : PolyQuaternionExpr) (env : Nat → RatPoly)
    (h : normalize p.scalar = normalize q.scalar ∧ normalize p.iPart = normalize q.iPart ∧
      normalize p.jPart = normalize q.jPart ∧ normalize p.kPart = normalize q.kPart) :
    PolyQuaternionCoeffEqv (evalQ env p) (evalQ env q) :=
  ⟨coeffEvalExpr_eqv_of_normalize_eq _ _ h.1 env,
    coeffEvalExpr_eqv_of_normalize_eq _ _ h.2.1 env,
    coeffEvalExpr_eqv_of_normalize_eq _ _ h.2.2.1 env,
    coeffEvalExpr_eqv_of_normalize_eq _ _ h.2.2.2 env⟩

private def four (negative : Bool) (a b c d : RatPoly) : RatPoly :=
  if negative then polyAdd a (polyNeg (polyAdd b (polyAdd c d)))
  else polyAdd a (polyAdd b (polyAdd c (polyNeg d)))
private theorem four_congr (negative : Bool) {a a' b b' c c' d d' : RatPoly}
    (ha : RatPolyCoeffEqv a a') (hb : RatPolyCoeffEqv b b')
    (hc : RatPolyCoeffEqv c c') (hd : RatPolyCoeffEqv d d') :
    RatPolyCoeffEqv (four negative a b c d) (four negative a' b' c' d') := by
  cases negative
  · exact ha.add (hb.add (hc.add (RatPolyCoeffEqv.neg hd)))
  · exact ha.add (RatPolyCoeffEqv.neg (hb.add (hc.add hd)))
private theorem derivative_four (b : Nat) (i : Fin 3) (negative : Bool) (a c d e : RatPoly) :
    RatPolyCoeffEqv (frameDerivativeAt false b i (four negative a c d e))
      (four negative (frameDerivativeAt false b i a) (frameDerivativeAt false b i c)
        (frameDerivativeAt false b i d) (frameDerivativeAt false b i e)) := by
  cases negative
  · exact (frameDerivativeAt_add false b i a _).trans
      ((RatPolyCoeffEqv.refl _).add ((frameDerivativeAt_add false b i c _).trans
        ((RatPolyCoeffEqv.refl _).add ((frameDerivativeAt_add false b i d _).trans
          ((RatPolyCoeffEqv.refl _).add (frameDerivativeAt_neg false b i e))))))
  · exact (frameDerivativeAt_add false b i a _).trans
      ((RatPolyCoeffEqv.refl _).add ((frameDerivativeAt_neg false b i _).trans
        (RatPolyCoeffEqv.neg ((frameDerivativeAt_add false b i c _).trans
          ((RatPolyCoeffEqv.refl _).add (frameDerivativeAt_add false b i d e))))))
private theorem derivative_four_products (b : Nat) (i : Fin 3) (negative : Bool)
    (a c d e f g h j : RatPoly) :
    RatPolyCoeffEqv (frameDerivativeAt false b i
      (four negative (polyMul a c) (polyMul d e) (polyMul f g) (polyMul h j)))
      (four negative
        (polyAdd (polyMul (frameDerivativeAt false b i a) c) (polyMul a (frameDerivativeAt false b i c)))
        (polyAdd (polyMul (frameDerivativeAt false b i d) e) (polyMul d (frameDerivativeAt false b i e)))
        (polyAdd (polyMul (frameDerivativeAt false b i f) g) (polyMul f (frameDerivativeAt false b i g)))
        (polyAdd (polyMul (frameDerivativeAt false b i h) j) (polyMul h (frameDerivativeAt false b i j)))) :=
  (derivative_four b i negative _ _ _ _).trans
    (four_congr negative (frameDerivativeAt_mul false b i a c) (frameDerivativeAt_mul false b i d e)
      (frameDerivativeAt_mul false b i f g) (frameDerivativeAt_mul false b i h j))
private def jet (a b da db : PolyExpr) : PolyExpr := .add (.mul da b) (.mul a db)
private def jetProduct : PolyQuaternionExpr :=
  ⟨.add (jet (.var 0) (.var 4) (.var 8) (.var 12))
      (.neg (.add (jet (.var 1) (.var 5) (.var 9) (.var 13))
        (.add (jet (.var 2) (.var 6) (.var 10) (.var 14)) (jet (.var 3) (.var 7) (.var 11) (.var 15))))),
    .add (jet (.var 0) (.var 5) (.var 8) (.var 13))
      (.add (jet (.var 1) (.var 4) (.var 9) (.var 12))
        (.add (jet (.var 2) (.var 7) (.var 10) (.var 15)) (.neg (jet (.var 3) (.var 6) (.var 11) (.var 14))))),
    .add (jet (.var 0) (.var 6) (.var 8) (.var 14))
      (.add (jet (.var 2) (.var 4) (.var 10) (.var 12))
        (.add (jet (.var 3) (.var 5) (.var 11) (.var 13)) (.neg (jet (.var 1) (.var 7) (.var 9) (.var 15))))),
    .add (jet (.var 0) (.var 7) (.var 8) (.var 15))
      (.add (jet (.var 3) (.var 4) (.var 11) (.var 12))
        (.add (jet (.var 1) (.var 6) (.var 9) (.var 14)) (.neg (jet (.var 2) (.var 5) (.var 10) (.var 13)))))⟩
private theorem action_mul (b : Nat) (i : Fin 3) (p q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (quaternionAction false b i (p*q))
      (qAdd (quaternionAction false b i p * q) (p * quaternionAction false b i q)) := by
  let env := env4 p q (quaternionAction false b i p) (quaternionAction false b i q)
  have h : PolyQuaternionCoeffEqv (quaternionAction false b i (p*q)) (evalQ env jetProduct) :=
    ⟨derivative_four_products b i true p.scalar q.scalar p.iPart q.iPart p.jPart q.jPart p.kPart q.kPart,
      derivative_four_products b i false p.scalar q.iPart p.iPart q.scalar p.jPart q.kPart p.kPart q.jPart,
      derivative_four_products b i false p.scalar q.jPart p.jPart q.scalar p.kPart q.iPart p.iPart q.kPart,
      derivative_four_products b i false p.scalar q.kPart p.kPart q.scalar p.iPart q.jPart p.jPart q.iPart⟩
  exact h.trans (reflect jetProduct
    (exprAdd (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 8) (PolyQuaternionExpr.coordinate 4))
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 12))) env (by decide))

private theorem padded_add {B : Nat} {p p' q q' : PolyQuaternion}
    (hp : PaddedQuaternionCoeffEqv B p p') (hq : PaddedQuaternionCoeffEqv B q q') :
    PaddedQuaternionCoeffEqv B (qAdd p q) (qAdd p' q') :=
  ⟨PaddedPolynomialCoeffEqv.add hp.scalar hq.scalar, PaddedPolynomialCoeffEqv.add hp.iPart hq.iPart,
    PaddedPolynomialCoeffEqv.add hp.jPart hq.jPart, PaddedPolynomialCoeffEqv.add hp.kPart hq.kPart⟩
private theorem q_mul_zero_right (p : PolyQuaternion) :
    PolyQuaternionCoeffEqv (p*zeroQuaternion) zeroQuaternion :=
  ⟨four_congr true (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _)
      (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _),
    four_congr false (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _)
      (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _),
    four_congr false (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _)
      (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _),
    four_congr false (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _)
      (RatPolyCoeffEqv.mul_zero_right _) (RatPolyCoeffEqv.mul_zero_right _)⟩
private theorem q_add_zero (p : PolyQuaternion) : PolyQuaternionCoeffEqv (qAdd p zeroQuaternion) p :=
  ⟨RatPolyCoeffEqv.add_zero _, RatPolyCoeffEqv.add_zero _,
    RatPolyCoeffEqv.add_zero _, RatPolyCoeffEqv.add_zero _⟩
private theorem q_zero_add (p : PolyQuaternion) : PolyQuaternionCoeffEqv (qAdd zeroQuaternion p) p :=
  ⟨RatPolyCoeffEqv.zero_add _, RatPolyCoeffEqv.zero_add _,
    RatPolyCoeffEqv.zero_add _, RatPolyCoeffEqv.zero_add _⟩
private theorem active_left {B b : Nat} (i : Fin 3) {p q dp : PolyQuaternion}
    (hp : PaddedQuaternionCoeffEqv B (quaternionAction false b i p) dp)
    (hq : PaddedQuaternionCoeffEqv B (quaternionAction false b i q) zeroQuaternion) :
    PaddedQuaternionCoeffEqv B (quaternionAction false b i (p*q)) (dp*q) := by
  exact (PaddedQuaternionCoeffEqv.of_coeff (action_mul b i p q)).trans
    ((padded_add (hp.mul (PaddedQuaternionCoeffEqv.refl B q))
      ((PaddedQuaternionCoeffEqv.refl B p).mul hq)).trans
      ((padded_add (PaddedQuaternionCoeffEqv.refl B (dp*q)) (.of_coeff (q_mul_zero_right p))).trans
        (.of_coeff (q_add_zero (dp*q)))))
private theorem active_right {B b : Nat} (i : Fin 3) {p q dq : PolyQuaternion}
    (hp : PaddedQuaternionCoeffEqv B (quaternionAction false b i p) zeroQuaternion)
    (hq : PaddedQuaternionCoeffEqv B (quaternionAction false b i q) dq) :
    PaddedQuaternionCoeffEqv B (quaternionAction false b i (p*q)) (p*dq) := by
  exact (PaddedQuaternionCoeffEqv.of_coeff (action_mul b i p q)).trans
    ((padded_add (hp.mul (PaddedQuaternionCoeffEqv.refl B q))
      ((PaddedQuaternionCoeffEqv.refl B p).mul hq)).trans
      (.of_coeff (q_zero_add (p*dq))))
private theorem inactive_mul {B b : Nat} (i : Fin 3) {p q : PolyQuaternion}
    (hp : PaddedQuaternionCoeffEqv B (quaternionAction false b i p) zeroQuaternion)
    (hq : PaddedQuaternionCoeffEqv B (quaternionAction false b i q) zeroQuaternion) :
    PaddedQuaternionCoeffEqv B (quaternionAction false b i (p*q)) zeroQuaternion :=
  (active_left i hp hq).trans (.of_coeff (.refl _))

private def insertion (q0 q1 q2 q3 e : PolyQuaternion) (s : Fin 4) : PolyQuaternion :=
  match s.val with
  | 0 => (((e*q0)*q1)*q2)*q3
  | 1 => ((q0*(e*q1))*q2)*q3
  | 2 => ((q0*q1)*negQuaternion (q2*e))*q3
  | _ => ((q0*q1)*q2)*negQuaternion (q3*e)

private theorem factor_active {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) (s : Fin 4) (i : Fin 3) :
    PaddedQuaternionCoeffEqv (baseLinks width).length
      (quaternionAction false (slotIndex width p s) i (factor width p s))
      (if 2 ≤ s.val then negQuaternion (factor width p s * imaginaryBasis i)
        else imaginaryBasis i * factor width p s) := by
  rcases cases4 s with rfl | rfl | rfl | rfl
  · exact coordinate_action false (slotIndex_lt hp 0) i
  · exact coordinate_action false (slotIndex_lt hp 1) i
  · exact conjugate_coordinate_action false (slotIndex_lt hp 2) i
  · exact conjugate_coordinate_action false (slotIndex_lt hp 3) i
private theorem factor_inactive {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) {s t : Fin 4} (hst : s ≠ t) (i : Fin 3) :
    PaddedQuaternionCoeffEqv (baseLinks width).length
      (quaternionAction false (slotIndex width p s) i (factor width p t)) zeroQuaternion := by
  rcases cases4 t with rfl | rfl | rfl | rfl
  · exact other_coordinate_action false (slotIndex_lt hp s)
      (slotIndex_lt hp 0) (slotIndex_ne hp hst) i
  · exact other_coordinate_action false (slotIndex_lt hp s)
      (slotIndex_lt hp 1) (slotIndex_ne hp hst) i
  · exact other_conjugate_coordinate_action false (slotIndex_lt hp s)
      (slotIndex_lt hp 2) (slotIndex_ne hp hst) i
  · exact other_conjugate_coordinate_action false (slotIndex_lt hp s)
      (slotIndex_lt hp 3) (slotIndex_ne hp hst) i

private theorem four_first_jet {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) (s : Fin 4) (i : Fin 3) :
    PaddedQuaternionCoeffEqv (baseLinks width).length
      (quaternionAction false (slotIndex width p s) i (faceProduct width p))
      (insertion (factor width p 0) (factor width p 1)
        (factor width p 2) (factor width p 3) (imaginaryBasis i) s) := by
  rcases cases4 s with rfl | rfl | rfl | rfl
  · exact active_left i (active_left i (active_left i (factor_active hp 0 i)
      (factor_inactive hp (by decide : (0:Fin 4) ≠ 1) i))
      (factor_inactive hp (by decide : (0:Fin 4) ≠ 2) i))
      (factor_inactive hp (by decide : (0:Fin 4) ≠ 3) i)
  · exact active_left i (active_left i (active_right i
      (factor_inactive hp (by decide : (1:Fin 4) ≠ 0) i) (factor_active hp 1 i))
      (factor_inactive hp (by decide : (1:Fin 4) ≠ 2) i))
      (factor_inactive hp (by decide : (1:Fin 4) ≠ 3) i)
  · exact active_left i (active_right i (inactive_mul i
      (factor_inactive hp (by decide : (2:Fin 4) ≠ 0) i)
      (factor_inactive hp (by decide : (2:Fin 4) ≠ 1) i)) (factor_active hp 2 i))
      (factor_inactive hp (by decide : (2:Fin 4) ≠ 3) i)
  · exact active_right i (inactive_mul i (inactive_mul i
      (factor_inactive hp (by decide : (3:Fin 4) ≠ 0) i)
      (factor_inactive hp (by decide : (3:Fin 4) ≠ 1) i))
      (factor_inactive hp (by decide : (3:Fin 4) ≠ 2) i)) (factor_active hp 3 i)

private theorem support_neg {B : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks B p) : SupportedQuaternionBlocks B (polyNeg p) := by
  intro t ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  exact hp a ha
private theorem support_smul (B : Nat) (c : Q') : SupportedQuaternionBlocks B (polySmul c polyOne) := by
  intro t ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  exact supported_one B a ha
private theorem basis_supported (B : Nat) (i : Fin 3) : Supported B (imaginaryBasis i) :=
  ⟨support_smul B _, support_smul B _, support_smul B _, support_smul B _⟩
private theorem neg_supported {B : Nat} {q : PolyQuaternion} (hq : Supported B q) :
    Supported B (negQuaternion q) :=
  ⟨support_neg hq.scalar, support_neg hq.iPart, support_neg hq.jPart, support_neg hq.kPart⟩

theorem commonVector_supported {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) (s : Fin 4) (i : Fin 3) :
    Supported (baseLinks width).length (commonVector width p s i) := by
  have h := ((prefix_supported hp s).mul (basis_supported (baseLinks width).length i)).mul
    (prefix_supported hp s).conj
  unfold commonVector signed
  split
  · exact neg_supported h
  · exact h
private theorem insertion_supported {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) (s : Fin 4) (i : Fin 3) :
    Supported (baseLinks width).length
      (insertion (factor width p 0) (factor width p 1)
        (factor width p 2) (factor width p 3) (imaginaryBasis i) s) := by
  have h0 := factor_supported hp 0
  have h1 := factor_supported hp 1
  have h2 := factor_supported hp 2
  have h3 := factor_supported hp 3
  have he := basis_supported (baseLinks width).length i
  rcases cases4 s with rfl | rfl | rfl | rfl
  · exact (((he.mul h0).mul h1).mul h2).mul h3
  · exact ((h0.mul (he.mul h1)).mul h2).mul h3
  · exact ((h0.mul h1).mul (neg_supported (h2.mul he))).mul h3
  · exact ((h0.mul h1).mul h2).mul (neg_supported (h3.mul he))

private theorem padded_carrier {B : Nat} {p q : PolyQuaternion}
    (hp : Supported B p) (hq : Supported B q) (h : PaddedQuaternionCoeffEqv B p q) :
    PolyQuaternionHaarCarrierEqv B p q := by
  constructor
  · exact carrier_of_supported hp.scalar hq.scalar
      (PaddedPolynomialCoeffEqv.haar_insert h.scalar hp.scalar hq.scalar)
  · exact carrier_of_supported hp.iPart hq.iPart
      (PaddedPolynomialCoeffEqv.haar_insert h.iPart hp.iPart hq.iPart)
  · exact carrier_of_supported hp.jPart hq.jPart
      (PaddedPolynomialCoeffEqv.haar_insert h.jPart hp.jPart hq.jPart)
  · exact carrier_of_supported hp.kPart hq.kPart
      (PaddedPolynomialCoeffEqv.haar_insert h.kPart hp.kPart hq.kPart)

private theorem inverse_prefix {B : Nat} {f : PolyQuaternion}
    (hf : HaarCarrierEqv B (polyQuaternionNorm f) polyOne) :
    PolyQuaternionHaarCarrierEqv B (PolyQuaternion.conj f * f) PolyQuaternion.one :=
  (PolyQuaternionHaarCarrierEqv.of_coeff (PolyQuaternionCoeffEqv.conj_mul f)).trans
    ⟨hf, HaarCarrierEqv.refl B polyZero, HaarCarrierEqv.refl B polyZero,
      HaarCarrierEqv.refl B polyZero⟩
private theorem sandwich {B : Nat} {f : PolyQuaternion}
    (hf : HaarCarrierEqv B (polyQuaternionNorm f) polyOne) (e t : PolyQuaternion) :
    PolyQuaternionHaarCarrierEqv B (((f*e)*PolyQuaternion.conj f)*(f*t)) ((f*e)*t) := by
  have ha : PolyQuaternionCoeffEqv (((f*e)*PolyQuaternion.conj f)*(f*t))
      ((f*e)*((PolyQuaternion.conj f*f)*t)) :=
    (PolyQuaternionCoeffEqv.mul_assoc (f*e) (PolyQuaternion.conj f) (f*t)).trans
      ((PolyQuaternionCoeffEqv.refl (f*e)).mul
        (PolyQuaternionCoeffEqv.mul_assoc (PolyQuaternion.conj f) f t).symm)
  exact (PolyQuaternionHaarCarrierEqv.of_coeff ha).trans
    (((PolyQuaternionHaarCarrierEqv.refl B (f*e)).mul
      ((inverse_prefix hf).mul (PolyQuaternionHaarCarrierEqv.refl B t))).trans
      (.of_coeff ((PolyQuaternionCoeffEqv.refl (f*e)).mul (PolyQuaternionCoeffEqv.one_mul t))))

private theorem carrier_neg {B : Nat} {p q : PolyQuaternion}
    (h : PolyQuaternionHaarCarrierEqv B p q) :
    PolyQuaternionHaarCarrierEqv B (negQuaternion p) (negQuaternion q) :=
  ⟨HaarCarrierEqv.neg h.scalar, HaarCarrierEqv.neg h.iPart,
    HaarCarrierEqv.neg h.jPart, HaarCarrierEqv.neg h.kPart⟩
private def suffix (width : Nat) (p : Z4Plaq) (s : Fin 4) : PolyQuaternion :=
  match s.val with
  | 0 => faceProduct width p
  | 1 => (factor width p 1 * factor width p 2) * factor width p 3
  | 2 => factor width p 3
  | _ => PolyQuaternion.one

private theorem prefix_suffix (width : Nat) (p : Z4Plaq) (s : Fin 4) :
    PolyQuaternionCoeffEqv (faceProduct width p) (commonPrefix width p s * suffix width p s) := by
  rcases cases4 s with rfl | rfl | rfl | rfl
  · exact (PolyQuaternionCoeffEqv.one_mul _).symm
  · exact ((PolyQuaternionCoeffEqv.mul_assoc (factor width p 0) (factor width p 1)
      (factor width p 2)).mul (PolyQuaternionCoeffEqv.refl (factor width p 3))).trans
      (PolyQuaternionCoeffEqv.mul_assoc (factor width p 0)
        (factor width p 1 * factor width p 2) (factor width p 3))
  · exact .refl _
  · exact (PolyQuaternionCoeffEqv.mul_one _).symm

private theorem coeff_neg {p q : PolyQuaternion} (h : PolyQuaternionCoeffEqv p q) :
    PolyQuaternionCoeffEqv (negQuaternion p) (negQuaternion q) :=
  ⟨RatPolyCoeffEqv.neg h.scalar, RatPolyCoeffEqv.neg h.iPart,
    RatPolyCoeffEqv.neg h.jPart, RatPolyCoeffEqv.neg h.kPart⟩
private theorem signed_mul (s : Fin 4) (p q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (signed s p * q) (signed s (p*q)) := by
  unfold signed
  split
  · exact reflect (PolyQuaternionExpr.mul (exprNeg (PolyQuaternionExpr.coordinate 0))
        (PolyQuaternionExpr.coordinate 4))
      (exprNeg (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 4)))
      (env4 p q zeroQuaternion zeroQuaternion) (by decide)
  · exact .refl _
private theorem signed_carrier {B : Nat} (s : Fin 4) {p q : PolyQuaternion}
    (h : PolyQuaternionHaarCarrierEqv B p q) :
    PolyQuaternionHaarCarrierEqv B (signed s p) (signed s q) := by
  unfold signed
  split
  · exact carrier_neg h
  · exact h

private theorem q_mul_neg_right (p q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (p*negQuaternion q) (negQuaternion (p*q)) :=
  reflect (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0)
      (exprNeg (PolyQuaternionExpr.coordinate 4)))
    (exprNeg (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 4)))
    (env4 p q zeroQuaternion zeroQuaternion) (by decide)

private theorem insertion_prefix (width : Nat) (p : Z4Plaq) (s : Fin 4) (i : Fin 3) :
    PolyQuaternionCoeffEqv
      (insertion (factor width p 0) (factor width p 1)
        (factor width p 2) (factor width p 3) (imaginaryBasis i) s)
      (signed s ((commonPrefix width p s * imaginaryBasis i) * suffix width p s)) := by
  let q0 := factor width p 0
  let q1 := factor width p 1
  let q2 := factor width p 2
  let q3 := factor width p 3
  let e := imaginaryBasis i
  rcases cases4 s with rfl | rfl | rfl | rfl
  · have h := (((PolyQuaternionCoeffEqv.mul_assoc e q0 q1).mul
      (PolyQuaternionCoeffEqv.refl q2)).mul (PolyQuaternionCoeffEqv.refl q3)).trans
      (((PolyQuaternionCoeffEqv.mul_assoc e (q0*q1) q2).mul
        (PolyQuaternionCoeffEqv.refl q3)).trans (PolyQuaternionCoeffEqv.mul_assoc e ((q0*q1)*q2) q3))
    exact h.trans ((PolyQuaternionCoeffEqv.one_mul e).symm.mul
      (PolyQuaternionCoeffEqv.refl (faceProduct width p)))
  · exact (((PolyQuaternionCoeffEqv.mul_assoc q0 e q1).symm.mul
      (PolyQuaternionCoeffEqv.refl q2)).mul (PolyQuaternionCoeffEqv.refl q3)).trans
      (((PolyQuaternionCoeffEqv.mul_assoc (q0*e) q1 q2).mul
        (PolyQuaternionCoeffEqv.refl q3)).trans (PolyQuaternionCoeffEqv.mul_assoc (q0*e) (q1*q2) q3))
  · exact ((q_mul_neg_right (q0*q1) (q2*e)).mul (PolyQuaternionCoeffEqv.refl q3)).trans
      (((coeff_neg (PolyQuaternionCoeffEqv.mul_assoc (q0*q1) q2 e).symm).mul
        (PolyQuaternionCoeffEqv.refl q3)).trans (signed_mul 2 (((q0*q1)*q2)*e) q3))
  · exact (q_mul_neg_right ((q0*q1)*q2) (q3*e)).trans
      ((coeff_neg (PolyQuaternionCoeffEqv.mul_assoc ((q0*q1)*q2) q3 e).symm).trans
        (coeff_neg (PolyQuaternionCoeffEqv.mul_one (faceProduct width p*e)).symm))

private theorem common_insertion {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) (s : Fin 4) (i : Fin 3) :
    PolyQuaternionHaarCarrierEqv (baseLinks width).length
      (commonVector width p s i * faceProduct width p)
      (insertion (factor width p 0) (factor width p 1)
        (factor width p 2) (factor width p 3) (imaginaryBasis i) s) := by
  have hP := prefix_suffix width p s
  have hmove := signed_mul s
    ((commonPrefix width p s * imaginaryBasis i) * PolyQuaternion.conj (commonPrefix width p s))
    (commonPrefix width p s * suffix width p s)
  exact ((PolyQuaternionHaarCarrierEqv.refl _ (commonVector width p s i)).mul
    (PolyQuaternionHaarCarrierEqv.of_coeff hP)).trans
    ((PolyQuaternionHaarCarrierEqv.of_coeff hmove).trans
      ((signed_carrier s (sandwich (prefix_unit hp s) (imaginaryBasis i) (suffix width p s))).trans
        (PolyQuaternionHaarCarrierEqv.of_coeff (insertion_prefix width p s i).symm)))

/-- Every literal physical slot and every imaginary direction are pinned
to the original plaquette in the SAME arbitrary-insertion Haar carrier. -/
theorem original_paired_first_jet {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) (s : Fin 4) (i : Fin 3) :
    HaarCarrierEqv (baseLinks width).length
      (pairedDerivativeAt (slotIndex width p s) i (plaquette width p).scalar)
      (commonVector width p s i * plaquette width p).scalar := by
  have hw := original_word hp
  have hs : Supported (baseLinks width).length (faceProduct width p) :=
    (((factor_supported hp 0).mul (factor_supported hp 1)).mul
      (factor_supported hp 2)).mul (factor_supported hp 3)
  have hd : Supported (baseLinks width).length
      (quaternionAction false (slotIndex width p s) i (faceProduct width p)) :=
    ⟨pairedDerivativeAt_supported (slotIndex_lt hp s) i hs.scalar,
      pairedDerivativeAt_supported (slotIndex_lt hp s) i hs.iPart,
      pairedDerivativeAt_supported (slotIndex_lt hp s) i hs.jPart,
      pairedDerivativeAt_supported (slotIndex_lt hp s) i hs.kPart⟩
  have hj := padded_carrier hd (insertion_supported hp s i) (four_first_jet hp s i)
  have hraw : RatPolyCoeffEqv
      (pairedDerivativeAt (slotIndex width p s) i (plaquette width p).scalar)
      (pairedDerivativeAt (slotIndex width p s) i (faceProduct width p).scalar) := by
    have h := fun a b => angularDerivative_congr (4*slotIndex width p s+a)
      (4*slotIndex width p s+b) hw.scalar
    have hi : i=0 ∨ i=1 ∨ i=2 := by simp only [Fin.ext_iff]; omega
    rcases hi with rfl | rfl | rfl
    · exact (h 0 1).add (h 2 3)
    · exact (h 0 2).add (RatPolyCoeffEqv.neg (h 1 3))
    · exact (h 0 3).add (h 1 2)
  exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier hraw)
    (HaarCarrierEqv.trans hj.scalar (HaarCarrierEqv.trans
      (HaarCarrierEqv.symm (common_insertion hp s i).scalar)
      (RatPolyCoeffEqv.haarCarrier
        ((PolyQuaternionCoeffEqv.refl (commonVector width p s i)).mul hw.symm).scalar)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCommonFrame

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCommonFrame.slotIndex_ne
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCommonFrame.prefix_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCommonFrame.prefix_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCommonFrame.commonVector_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCommonFrame.original_paired_first_jet
