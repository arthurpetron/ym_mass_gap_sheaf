/-
# Volume-independent local-collar error relative to the full spectator Zsp

The ORIGINAL product remainder receives the sharp Haar interval cap
(1+delta(w))^N-1, not a syntactic coefficient norm. The translated lower
collar and its explicit upper reflected face list have at most 24 entries.
Both signed remainder integrals are consequently bounded by this local cap
times the SAME spectator OS background. Extra interval insertions retain
their explicit caps. At w=1/1024 the 24-face cap is at most 1/262144.

This does not yet estimate the scalar-weighted interacting determinant or
compare the full partition. Thermodynamic nontriviality remains open.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground
import YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation

namespace YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
open YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

def productErrorCap (w : Q') (n : Nat) : Q' := (1+heatRemainderBound w)^n + -1

theorem productErrorCap_step (w : Q') (n : Nat) : productErrorCap w (n+1) ≈
    productErrorCap w n + heatRemainderBound w * (1+heatRemainderBound w)^n :=
  poly_identity_of_normal_eq
    (.add (.mul (.add (.const 1) (.var 0)) (.var 1)) (.neg (.const 1)))
    (.add (.add (.var 1) (.neg (.const 1))) (.mul (.var 0) (.var 1)))
    (by decide) (fun i => if i = 0 then heatRemainderBound w else (1+heatRemainderBound w)^n)

theorem productErrorCap_mono {w : Q'} (hw : (0 : Q') ≤ w) {m n : Nat} (hmn : m ≤ n) :
    productErrorCap w m ≤ productErrorCap w n := by
  have step : ∀ k, productErrorCap w k ≤ productErrorCap w (k+1) := fun k =>
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _)))
      (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _
        (Q'.mul_nonneg _ _ (heatRemainderBound_nonnegative hw)
          (Q'.pow_nonneg _ (Q'.zero_le_add _ _ Q'.zero_le_one (heatRemainderBound_nonnegative hw)) k)))
        (Q'.ge_of_eqv (productErrorCap_step w k)))
  induction n with
  | zero => have he : m = 0 := Nat.eq_zero_of_le_zero hmn; subst m; exact Q'.le_refl' _
  | succ n ih =>
      by_cases he : m = n+1
      · subst m; exact Q'.le_refl' _
      · exact Q'.le_trans' _ _ _ (ih (by omega)) (step n)

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half)

def faceInterval (K extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) :
    Interval (boundaryCompleteSlabLinks extent).length (faceHeatPolynomial w K extent id) (1+heatRemainderBound w) :=
  .ofCoeff (heatFace_supported w K extent id) (faceHeat_eq_one_add w extent id K)
    ((Interval.one _).add (faceRemainderInterval hw0 hw1 hsmall extent id hi K))

def productInterval (K extent : Nat) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    Interval (boundaryCompleteSlabLinks extent).length (polynomialProduct (faceHeatPolynomial w K extent) ids)
      ((1+heatRemainderBound w)^ids.length) :=
  Interval.productUniform _ _ ids (fun id hid => faceInterval hw0 hw1 hsmall K extent id (hi id hid))

/-- Reuses the existing coefficient-pinned ORIGINAL telescoping remainder. -/
def productErrorInterval (K extent : Nat) : (ids : List Nat) →
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    Interval (boundaryCompleteSlabLinks extent).length (productPerturbation w extent K ids)
      (productErrorCap w ids.length)
  | [], _ => (Interval.zero _).changeCap (by change (0 : Q') ≈ 1 + -1; decide)
  | id :: ids, hi =>
      (((Interval.one _).mul (productErrorInterval K extent ids
        (fun j hj => hi j (List.mem_cons_of_mem id hj)))).changeCap (Q'.one_mul_eqv _)).add
        ((faceRemainderInterval hw0 hw1 hsmall extent id (hi id List.mem_cons_self) K).mul
          (productInterval hw0 hw1 hsmall K extent ids (fun j hj => hi j (List.mem_cons_of_mem id hj))))
      |>.changeCap (Q'.eqv_symm (productErrorCap_step w ids.length))

def reflectedCollarIds (half : Nat) : List Nat := (lowerCollar half).map (slabFaceReflectId (centralExtent half))

theorem lowerCollar_physical {half id : Nat} (hi : id ∈ lowerCollar half) :
    id ∈ slabPhysicalFaceEdges (centralExtent half) := (mem_centralLowerFaceIds.mp (collar_mem hi)).1

def collarInterval (K half : Nat) :
    Interval (blocks half) (productPerturbation w (centralExtent half) K (lowerCollar half)) (productErrorCap w 24) :=
  (productErrorInterval hw0 hw1 hsmall K _ _ (fun _ hi => lowerCollar_physical hi)).weaken
    (productErrorCap_mono hw0 (lowerCollar_length_le half))

def reflectedCollarInterval (K half : Nat) :
    Interval (blocks half) (productPerturbation w (centralExtent half) K (reflectedCollarIds half)) (productErrorCap w 24) :=
  (productErrorInterval hw0 hw1 hsmall K _ _ (fun _ hi => by
    obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hi
    exact slabFaceReflectId_physical (lowerCollar_physical hid))).weaken
      (productErrorCap_mono hw0 (by simpa only [reflectedCollarIds, List.length_map] using lowerCollar_length_le half))

variable (hdelta : heatRemainderBound w ≤ 1)
include hw0 hw1 hsmall hdelta

theorem collar_relative_bound (K half : Nat) :
    Q'.abs (quaternionHaar (blocks half) (polyMul (originalBackground w K half)
      (productPerturbation w (centralExtent half) K (lowerCollar half)))) ≤
        productErrorCap w 24 * backgroundMass w K half :=
  background_weighted_bound hw0 hw1 hsmall hdelta K half (collarInterval hw0 hw1 hsmall K half)

/-- Signed extra insertions remain explicit; there is no hidden L1(Zsp) cost. -/
theorem reflectedCollar_insert_bound (K half : Nat) {p : RatPoly} {c : Q'} (P : Interval (blocks half) p c) :
    Q'.abs (quaternionHaar (blocks half) (polyMul (originalBackground w K half)
      (polyMul p (productPerturbation w (centralExtent half) K (reflectedCollarIds half))))) ≤
        (c * productErrorCap w 24) * backgroundMass w K half :=
  background_weighted_bound hw0 hw1 hsmall hdelta K half (P.mul (reflectedCollarInterval hw0 hw1 hsmall K half))

omit hw0 hw1 hsmall hdelta in
/-- Independently kernel-checked counterpart of the exact-rational pilot. -/
theorem existingNome_collar_cap :
    productErrorCap BF4ExactSlabPlaquetteSmallNomeCertificate.nome 24 ≤ Q'.invSucc 262143 := by decide

omit hw0 hw1 hsmall hdelta in
/-- Fully discharged fixed-nome comparison, every cutoff and translated volume. -/
theorem existingNome_collar_relative_bound (K half : Nat) :
    let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
    Q'.abs (quaternionHaar (blocks half) (polyMul (originalBackground w K half)
      (productPerturbation w (centralExtent half) K (lowerCollar half)))) ≤
        Q'.invSucc 262143 * backgroundMass w K half :=
  Q'.le_trans' _ _ _
    (collar_relative_bound (Q'.le_of_lt BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos)
      (Q'.le_of_lt BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one)
      existingNome_guards.1 (Q'.le_of_lt existingNome_guards.2) K half)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ existingNome_collar_cap
      (Q'.le_of_lt (existingNome_background_positive K half)))

end YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.productErrorCap
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.productErrorCap_step
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.productErrorCap_mono
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.faceInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.productInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.productErrorInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.reflectedCollarIds
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.lowerCollar_physical
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.collarInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.reflectedCollarInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.collar_relative_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.reflectedCollar_insert_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.existingNome_collar_cap
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval.existingNome_collar_relative_bound
