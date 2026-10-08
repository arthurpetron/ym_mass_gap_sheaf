/-
# The origin spatial plaquette orbit on the SAME Wilson completion

Concrete ordered-word conjugation identifies the two checked spatial swaps
on the origin fundamental characters. Their differences have identical
responses at EVERY actual completed lag and mixed response minus one half
of that common response. Arbitrary signed rational coefficients therefore
only rescale this response by a*a-a*b+b*b.

The cleared ratio identity also holds after one COMMON time filter. This
does not identify independently filtered basis vectors, prove that this
source span is invariant under time, or supply a slow rate. Other sites,
spins and independent Krylov lags remain possible multiplicity directions.
The continuum theory and physical Hamiltonian gap remain open.
-/

import YMGap.Continuum.BF4WilsonAllNomeSpatialSwapBraid
import YMGap.Continuum.BF4WilsonAllNomeAntisymmetricPlaquette
import YMGap.Continuum.BF4WilsonAllNomeWindowPins
import YMGap.Continuum.BF4WilsonAllNomeBilinearTime
import YMGap.Continuum.BF4WilsonAllNomeLinearLaws
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram (faceLinkA faceLinkB faceLinkC faceLinkD)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation (plaquetteWord)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeWindowPins
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local notation "hGeom" => BF4ExactSlabSpatialHeadSwapGeometry.swapPlaquette
local notation "aGeom" => BF4ExactSlabSpatialAxisSwapGeometry.swapPlaquette
local notation "hEntry" => BF4ExactSlabSpatialHeadSwapWilsonLoop.swapEntry
local notation "aEntry" => BF4ExactSlabSpatialAxisSwapWilsonLoop.swapEntry

attribute [local irreducible] BF4ExactSlabFixedSpatialSliceCarrier.baseLinks link

private theorem rightFour (a b c d : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.mul a (PolyQuaternion.mul b
        (PolyQuaternion.mul (PolyQuaternion.conj c)
          (PolyQuaternion.mul (PolyQuaternion.conj d) PolyQuaternion.one))))
      (plaquetteWord a b c d) :=
  ((PolyQuaternionCoeffEqv.refl a).mul
    ((PolyQuaternionCoeffEqv.refl b).mul
      ((PolyQuaternionCoeffEqv.refl (PolyQuaternion.conj c)).mul
        (PolyQuaternionCoeffEqv.mul_one (PolyQuaternion.conj d))))).trans
    ((PolyQuaternionCoeffEqv.mul_assoc a b
      (PolyQuaternion.mul (PolyQuaternion.conj c) (PolyQuaternion.conj d))).symm.trans
      (PolyQuaternionCoeffEqv.mul_assoc (PolyQuaternion.mul a b)
        (PolyQuaternion.conj c) (PolyQuaternion.conj d)).symm)

private theorem faceWord (width : Nat) (face : Z4Plaq) :
    PolyQuaternionCoeffEqv (sourceWord width (orientedPlaquetteBoundary face))
      (plaquetteWord (link width (faceLinkA face)) (link width (faceLinkB face))
        (link width (faceLinkC face)) (link width (faceLinkD face))) := by
  rcases face with ⟨⟨i,j,k,t⟩,plane⟩
  cases plane <;>
    simp only [sourceWord, orientedPlaquetteBoundary, wordWith, orientedLink,
      faceLinkA, faceLinkB, faceLinkC, faceLinkD, dirsOf, Bool.false_eq_true,
      if_false, if_true] <;>
    exact rightFour _ _ _ _

private theorem headFaceWord (width : Nat) (face : Z4Plaq) :
    PolyQuaternionCoeffEqv (sourceWord width ((orientedPlaquetteBoundary face).map hEntry))
      (BF4ExactSlabSpatialHeadSwapWord.swappedFaceWord (link width) face) := by
  rcases face with ⟨⟨i,j,k,t⟩,plane⟩
  cases plane <;>
    simp only [sourceWord, orientedPlaquetteBoundary, wordWith, orientedLink,
      BF4ExactSlabSpatialHeadSwapWilsonLoop.swapEntry,
      BF4ExactSlabSpatialHeadSwapWord.swappedFaceWord,
      List.map_cons, List.map_nil, faceLinkA, faceLinkB, faceLinkC, faceLinkD,
      dirsOf, Bool.false_eq_true, if_false, if_true] <;>
    exact rightFour _ _ _ _

private theorem axisFaceWord (width : Nat) (face : Z4Plaq) :
    PolyQuaternionCoeffEqv (sourceWord width ((orientedPlaquetteBoundary face).map aEntry))
      (BF4ExactSlabSpatialAxisSwapWord.swappedFaceWord (link width) face) := by
  rcases face with ⟨⟨i,j,k,t⟩,plane⟩
  cases plane <;>
    simp only [sourceWord, orientedPlaquetteBoundary, wordWith, orientedLink,
      BF4ExactSlabSpatialAxisSwapWilsonLoop.swapEntry,
      BF4ExactSlabSpatialAxisSwapWord.swappedFaceWord,
      List.map_cons, List.map_nil, faceLinkA, faceLinkB, faceLinkC, faceLinkD,
      dirsOf, Bool.false_eq_true, if_false, if_true] <;>
    exact rightFour _ _ _ _

/-- Ordered source-character equality includes the reversed p01 boundary. -/
theorem head_sourceCharacter (width : Nat) (face : Z4Plaq) (spin : Nat) :
    RatPolyCoeffEqv (sourceCharacter width ((orientedPlaquetteBoundary face).map hEntry) spin)
      (sourceCharacter width (orientedPlaquetteBoundary (hGeom face)) spin) :=
  characterPolynomial_coeffEqv
    ((headFaceWord width face).scalar.trans
      ((BF4ExactSlabSpatialHeadSwapWord.swappedFaceWord_scalar (link width) face).trans
        (faceWord width (hGeom face)).scalar.symm)) spin

/-- Ordered source-character equality includes the reversed p12 boundary. -/
theorem axis_sourceCharacter (width : Nat) (face : Z4Plaq) (spin : Nat) :
    RatPolyCoeffEqv (sourceCharacter width ((orientedPlaquetteBoundary face).map aEntry) spin)
      (sourceCharacter width (orientedPlaquetteBoundary (aGeom face)) spin) :=
  characterPolynomial_coeffEqv
    ((axisFaceWord width face).scalar.trans
      ((BF4ExactSlabSpatialAxisSwapWord.swappedFaceWord_scalar (link width) face).trans
        (faceWord width (aGeom face)).scalar.symm)) spin

def face01 : Z4Plaq := ((0,0,0,0), .p01)
def face02 : Z4Plaq := ((0,0,0,0), .p02)
def face12 : Z4Plaq := ((0,0,0,0), .p12)

private theorem origin_physical {width : Nat} (hw : 1 ≤ width) (plane : Z4Plane)
    (hp : (dirsOf plane).2 ≠ Dir4.x3) : ((0,0,0,0),plane) ∈ spatialFaces width :=
  (spatialFaces_mem_iff width _).mpr
    ⟨(show 0 < width by omega), (show 0 < width by omega),
      (show 0 < width by omega), rfl, hp⟩

def faceExpression {width : Nat} (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    WindowExpression width := .loop 0 (plaquetteLoop face hf) 1

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "N" => completedNeg hw0 hw1
local notation "D" => completedSub hw0 hw1
local notation "H" => BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap hw0 hw1
local notation "U" => BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap hw0 hw1

def faceVector (face : Z4Plaq) (hf : face ∈ spatialFaces width) : V :=
  embedWindow hw0 hw1 0 (faceExpression face hf) (Nat.le_refl 0)

/-- Descend the concrete conjugate-word pin through the existing source identity API. -/
theorem head_faceVector (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    H (faceVector hw0 hw1 face hf) = faceVector hw0 hw1 (hGeom face)
      ((BF4ExactSlabSpatialHeadSwapGeometry.swapPlaquette_spatialFaces_mem_iff width face).mpr hf) := by
  unfold faceVector embedWindow
  rw [BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_embed]
  change embedWindow hw0 hw1 0
      (BF4ExactSlabSpatialHeadSwapWilsonWindow.swapExpression (faceExpression face hf)) _ =
    embedWindow hw0 hw1 0 (faceExpression (hGeom face) _) _
  have hp : RatPolyCoeffEqv
      (sourcePolynomial
        (BF4ExactSlabSpatialHeadSwapWilsonWindow.swapExpression (faceExpression face hf)))
      (sourcePolynomial (faceExpression (hGeom face)
        ((BF4ExactSlabSpatialHeadSwapGeometry.swapPlaquette_spatialFaces_mem_iff width face).mpr hf))) := by
    simpa only [faceExpression, sourcePolynomial,
      BF4ExactSlabSpatialHeadSwapWilsonWindow.swapExpression,
      BF4ExactSlabSpatialHeadSwapWilsonLoop.swapSourceLoop, plaquetteLoop,
      Nat.zero_mul, liftBoundary] using head_sourceCharacter width face 1
  exact embedWindow_eq_of_source_identity hw0 hw1 0 _ _ _ _
    hp

theorem axis_faceVector (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    U (faceVector hw0 hw1 face hf) = faceVector hw0 hw1 (aGeom face)
      ((BF4ExactSlabSpatialAxisSwapGeometry.swapPlaquette_spatialFaces_mem_iff width face).mpr hf) := by
  unfold faceVector embedWindow
  rw [BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_embed]
  change embedWindow hw0 hw1 0
      (BF4ExactSlabSpatialAxisSwapWilsonWindow.swapExpression (faceExpression face hf)) _ =
    embedWindow hw0 hw1 0 (faceExpression (aGeom face) _) _
  have hp : RatPolyCoeffEqv
      (sourcePolynomial
        (BF4ExactSlabSpatialAxisSwapWilsonWindow.swapExpression (faceExpression face hf)))
      (sourcePolynomial (faceExpression (aGeom face)
        ((BF4ExactSlabSpatialAxisSwapGeometry.swapPlaquette_spatialFaces_mem_iff width face).mpr hf))) := by
    simpa only [faceExpression, sourcePolynomial,
      BF4ExactSlabSpatialAxisSwapWilsonWindow.swapExpression,
      BF4ExactSlabSpatialAxisSwapWilsonLoop.swapSourceLoop, plaquetteLoop,
      Nat.zero_mul, liftBoundary] using axis_sourceCharacter width face 1
  exact embedWindow_eq_of_source_identity hw0 hw1 0 _ _ _ _
    hp

def h01 (hw : 1 ≤ width) : V := faceVector hw0 hw1 face01 (origin_physical hw .p01 (by decide))
def h02 (hw : 1 ≤ width) : V := faceVector hw0 hw1 face02 (origin_physical hw .p02 (by decide))
def h12 (hw : 1 ≤ width) : V := faceVector hw0 hw1 face12 (origin_physical hw .p12 (by decide))
def x (hw : 1 ≤ width) : V := D (h01 hw0 hw1 hw) (h02 hw0 hw1 hw)
def y (hw : 1 ≤ width) : V := D (h02 hw0 hw1 hw) (h12 hw0 hw1 hw)

private theorem sub_chain (p q r : V) : A (D p q) (D q r) = D p r := by
  unfold completedSub
  rw [completedAdd_assoc, ← completedAdd_assoc hw0 hw1 (N q) q (N r),
    completedNeg_add, completedZero_add]

private theorem sub_reverse (p q : V) : D q p = N (D p q) := by
  unfold completedSub completedNeg
  rw [completedSmul_add, completedSmul_mul,
    completedSmul_congr hw0 hw1 (by decide : ((-1 : Q')*(-1)).eqv 1),
    completedSmul_one]
  exact completedAdd_comm hw0 hw1 q (S (-1) p)

theorem axis_x (hw : 1 ≤ width) : U (x hw0 hw1 hw) = N (x hw0 hw1 hw) := by
  unfold x h01 h02
  rw [BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_sub, axis_faceVector,
    axis_faceVector]
  exact sub_reverse hw0 hw1 _ _

theorem axis_y (hw : 1 ≤ width) :
    U (y hw0 hw1 hw) = A (x hw0 hw1 hw) (y hw0 hw1 hw) := by
  unfold y h02 h12
  rw [BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_sub, axis_faceVector,
    axis_faceVector]
  exact (sub_chain hw0 hw1 (h01 hw0 hw1 hw) (h02 hw0 hw1 hw) (h12 hw0 hw1 hw)).symm

theorem head_x (hw : 1 ≤ width) :
    H (x hw0 hw1 hw) = A (x hw0 hw1 hw) (y hw0 hw1 hw) := by
  unfold x h01 h02
  rw [BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_sub, head_faceVector,
    head_faceVector]
  exact (sub_chain hw0 hw1 (h01 hw0 hw1 hw) (h02 hw0 hw1 hw) (h12 hw0 hw1 hw)).symm

theorem head_y (hw : 1 ≤ width) : H (y hw0 hw1 hw) = N (y hw0 hw1 hw) := by
  unfold y h02 h12
  rw [BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_sub, head_faceVector,
    head_faceVector]
  exact sub_reverse hw0 hw1 _ _

/-- The SAME source as the already constructed antisymmetric excitation. -/
theorem x_antisymmetric (hw : 1 ≤ width) :
    x hw0 hw1 hw = embed hw0 hw1 (BF4WilsonAllNomeAntisymmetricPlaquette.state hw) := by
  unfold x h01 h02 faceVector
  unfold completedSub completedNeg
  rw [completedSmul_embedWindow, completedAdd_embedWindow]
  apply embedWindow_eq_of_source_identity hw0 hw1 0
  change RatPolyCoeffEqv (polyAdd _ (polySmul (-1) _))
    (polyAdd (polySmul 1 _) (polyAdd (polySmul (-1) _) (polySmul 0 polyOne)))
  exact (RatPolyCoeffEqv.one_smul _).symm.add
    (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.zero_smul _)).trans
      (RatPolyCoeffEqv.add_zero _)).symm

attribute [local irreducible] h01 h02 h12 x y faceVector

def lagPair (n : Nat) (p q : V) : RC := B p (T n q)

theorem lagPair_symm (n : Nat) (p q : V) :
    lagPair hw0 hw1 n p q = lagPair hw0 hw1 n q p := by
  unfold lagPair
  rw [completedInner_symm, completedInner_time_balance]

private theorem lag_add_left (n : Nat) (p q r : V) :
    lagPair hw0 hw1 n (A p q) r =
      RCadd (lagPair hw0 hw1 n p r) (lagPair hw0 hw1 n q r) :=
  completedInner_add_left hw0 hw1 p q (T n r)

private theorem lag_add_right (n : Nat) (p q r : V) :
    lagPair hw0 hw1 n p (A q r) =
      RCadd (lagPair hw0 hw1 n p q) (lagPair hw0 hw1 n p r) := by
  unfold lagPair
  rw [completedTime_additive, completedInner_add_right]

private theorem lag_smul_left (n : Nat) (c : Q') (p q : V) :
    lagPair hw0 hw1 n (S c p) q = RCscale c (lagPair hw0 hw1 n p q) :=
  completedInner_smul_left hw0 hw1 c p (T n q)

private theorem lag_smul_right (n : Nat) (c : Q') (p q : V) :
    lagPair hw0 hw1 n p (S c q) = RCscale c (lagPair hw0 hw1 n p q) := by
  unfold lagPair
  rw [completedTime_smul, completedInner_smul_right]

private theorem axis_lag (n : Nat) (p q : V) :
    lagPair hw0 hw1 n (U p) (U q) = lagPair hw0 hw1 n p q := by
  unfold lagPair
  rw [← BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_time,
    BF4WilsonAllNomeSpatialAxisSwapCompletion.completedInner_swap]

private theorem head_lag (n : Nat) (p q : V) :
    lagPair hw0 hw1 n (H p) (H q) = lagPair hw0 hw1 n p q := by
  unfold lagPair
  rw [← BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_time,
    BF4WilsonAllNomeSpatialHeadSwapCompletion.completedInner_swap]

private theorem double (a : RC) : RCadd a a = RCscale 2 a := by
  refine Quotient.inductionOn a ?_
  intro p
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
      (by decide) (fun _ => p.approx k))

private theorem rc_comm (a b : RC) : RCadd a b = RCadd b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun k => Q'.add_comm_eqv (p.approx k) (q.approx k))

private theorem negative_sum_cancel (a b : RC) :
    RCadd (RCscale (-1) (RCadd b a)) a = RCscale (-1) b := by
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq
      (.add (.mul (.const (-1)) (.add (.var 1) (.var 0))) (.var 0))
      (.mul (.const (-1)) (.var 1)) (by decide)
      (fun | 0 => p.approx k | _ => q.approx k))

private theorem solve_mixed (a b : RC)
    (h : a = RCscale (-1) (RCadd b a)) : RCscale 2 a = RCscale (-1) b := by
  have hh := congrArg (fun t => RCadd t a) h
  change RCadd a a = RCadd (RCscale (-1) (RCadd b a)) a at hh
  rw [double, negative_sum_cancel] at hh
  exact hh

private theorem negative_involutive (a : RC) : RCscale (-1) (RCscale (-1) a) = a := by
  rw [RCscale_RCscale, RCSignedPairBudget.scale_congr (by decide : ((-1 : Q')*(-1)).eqv 1),
    RCscale_one]

/-- The literal axis generator fixes the mixed response at its negative sum. -/
theorem mixed_response (hw : 1 ≤ width) (n : Nat) :
    RCscale 2 (lagPair hw0 hw1 n (x hw0 hw1 hw) (y hw0 hw1 hw)) =
      RCscale (-1) (lagPair hw0 hw1 n (x hw0 hw1 hw) (x hw0 hw1 hw)) := by
  apply solve_mixed
  have h := (axis_lag hw0 hw1 n (x hw0 hw1 hw) (y hw0 hw1 hw)).symm
  rw [axis_x, axis_y] at h
  rw [completedNeg, lag_smul_left, lag_add_right] at h
  exact h

theorem diagonal_response (hw : 1 ≤ width) (n : Nat) :
    lagPair hw0 hw1 n (y hw0 hw1 hw) (y hw0 hw1 hw) =
      lagPair hw0 hw1 n (x hw0 hw1 hw) (x hw0 hw1 hw) := by
  have h := (head_lag hw0 hw1 n (x hw0 hw1 hw) (y hw0 hw1 hw)).symm
  rw [head_x, head_y] at h
  simp only [completedNeg, lag_smul_right, lag_add_left] at h
  rw [rc_comm (lagPair hw0 hw1 n (x hw0 hw1 hw) (y hw0 hw1 hw))
    (lagPair hw0 hw1 n (y hw0 hw1 hw) (y hw0 hw1 hw))] at h
  have hd := solve_mixed _ _ h
  rw [mixed_response] at hd
  have hh := congrArg (RCscale (-1)) hd
  rw [negative_involutive, negative_involutive] at hh
  exact hh.symm

theorem mixed_response_half (hw : 1 ≤ width) (n : Nat) :
    lagPair hw0 hw1 n (x hw0 hw1 hw) (y hw0 hw1 hw) =
      RCscale (-HalfPow.half) (lagPair hw0 hw1 n (x hw0 hw1 hw) (x hw0 hw1 hw)) := by
  have h := congrArg (RCscale HalfPow.half) (mixed_response hw0 hw1 hw n)
  rw [RCscale_RCscale, RCscale_RCscale,
    RCSignedPairBudget.scale_congr (by decide : (HalfPow.half*(2 : Q')).eqv 1), RCscale_one,
    RCSignedPairBudget.scale_congr (by decide : (HalfPow.half*(-1 : Q')).eqv (-HalfPow.half))] at h
  exact h

def trial (hw : 1 ≤ width) (a b : Q') : V := A (S a (x hw0 hw1 hw)) (S b (y hw0 hw1 hw))
def trialFactor (a b : Q') : Q' := a*a-a*b+b*b

private theorem quadratic_scalar (a b : Q') (r m : RC) :
    RCadd (RCadd (RCscale a (RCscale a r))
        (RCscale a (RCscale b m)))
      (RCadd (RCscale b (RCscale a m))
        (RCscale b (RCscale b r))) =
      RCadd (RCscale (a*a+b*b) r) (RCscale (a*b) (RCscale 2 m)) := by
  refine Quotient.inductionOn₂ r m ?_
  intro p q
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.mul (.var 0) (.var 2)))
        (.mul (.var 0) (.mul (.var 1) (.var 3))))
        (.add (.mul (.var 1) (.mul (.var 0) (.var 3)))
          (.mul (.var 1) (.mul (.var 1) (.var 2)))))
      (.add (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.var 2))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.const 2) (.var 3)))) (by decide)
      (fun | 0 => a | 1 => b | 2 => p.approx k | _ => q.approx k))

private theorem quadratic_finish (a b : Q') (r : RC) :
    RCadd (RCscale (a*a+b*b) r) (RCscale (a*b) (RCscale (-1) r)) =
      RCscale (trialFactor a b) r := by
  refine Quotient.inductionOn r ?_
  intro p
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq
      (.add (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.var 2))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.const (-1)) (.var 2))))
      (.mul (.add (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 0) (.var 1))))
        (.mul (.var 1) (.var 1))) (.var 2)) (by decide)
      (fun | 0 => a | 1 => b | _ => p.approx k))

/-- Every actual completed lag, with arbitrary signed rational coefficients. -/
theorem trial_response (hw : 1 ≤ width) (a b : Q') (n : Nat) :
    lagPair hw0 hw1 n (trial hw0 hw1 hw a b) (trial hw0 hw1 hw a b) =
      RCscale (trialFactor a b) (lagPair hw0 hw1 n (x hw0 hw1 hw) (x hw0 hw1 hw)) := by
  unfold trial
  rw [lag_add_left, lag_add_right, lag_add_right,
    lag_smul_left, lag_smul_left, lag_smul_left, lag_smul_left,
    lag_smul_right, lag_smul_right, lag_smul_right, lag_smul_right]
  simp only [lagPair_symm hw0 hw1 n (y hw0 hw1 hw) (x hw0 hw1 hw),
    diagonal_response]
  rw [quadratic_scalar, mixed_response]
  exact quadratic_finish a b _

/-- A COMMON time filter shifts every response by the same doubled lag. -/
theorem common_time_filter_response (hw : 1 ≤ width) (a b : Q') (u n : Nat) :
    lagPair hw0 hw1 n (T u (trial hw0 hw1 hw a b)) (T u (trial hw0 hw1 hw a b)) =
      RCscale (trialFactor a b) (lagPair hw0 hw1 n (T u (x hw0 hw1 hw))
        (T u (x hw0 hw1 hw))) := by
  unfold lagPair
  rw [← completedTime_add, completedInner_time_sum, ← completedTime_add,
    completedInner_time_sum]
  exact trial_response hw0 hw1 hw a b (u+(n+u))

private theorem scaled_cross (c : Q') (r s : RC) :
    RCmul (RCscale c r) s = RCmul (RCscale c s) r := by
  refine Quotient.inductionOn₂ r s ?_
  intro p q
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => c | 1 => p.approx k | _ => q.approx k))

/-- Division-free response-ratio pin after one common time filter; zero
coefficients or vanishing responses require no special case. -/
theorem common_time_filter_cleared_ratio (hw : 1 ≤ width) (a b : Q') (u n m : Nat) :
    RCmul (lagPair hw0 hw1 n (T u (trial hw0 hw1 hw a b)) (T u (trial hw0 hw1 hw a b)))
        (lagPair hw0 hw1 m (T u (x hw0 hw1 hw)) (T u (x hw0 hw1 hw))) =
      RCmul (lagPair hw0 hw1 m (T u (trial hw0 hw1 hw a b)) (T u (trial hw0 hw1 hw a b)))
        (lagPair hw0 hw1 n (T u (x hw0 hw1 hw)) (T u (x hw0 hw1 hw))) := by
  rw [common_time_filter_response, common_time_filter_response]
  exact scaled_cross _ _ _

end YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse

#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.head_sourceCharacter
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.axis_sourceCharacter
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.face01
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.face02
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.face12
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.faceExpression
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.faceVector
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.head_faceVector
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.axis_faceVector
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.h01
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.h02
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.h12
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.x
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.y
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.axis_x
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.axis_y
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.head_x
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.head_y
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.x_antisymmetric
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lagPair
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lagPair_symm
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.mixed_response
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.diagonal_response
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.mixed_response_half
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.trial
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.trialFactor
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.trial_response
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.common_time_filter_response
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse.common_time_filter_cleared_ratio
