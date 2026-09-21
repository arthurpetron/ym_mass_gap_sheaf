/-
# Grouped harmonic norms on the original quaternion-Haar carrier

Fischer modes of the same harmonic degree are added BEFORE squaring.
Only different degrees are orthogonal. The resulting partial-Haar identity
retains every tail coefficient; the full-Haar identity applies to an arbitrary
supported original polynomial through the proved carrier reassembly.
This is a finite norm identity, not an interacting spectral-gap estimate.
-/

import YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
import YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection
open YMGap.Continuum.SU2QuaternionFischerDecomposition
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

theorem headComponent_of_degree {n : Nat} (d : Nat) {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 n p) :
    headComponent d p = if n = d then p else polyZero := by
  induction p with
  | nil => simp [headComponent, polyZero]
  | cons t ts ih =>
      have ht := hp t List.mem_cons_self
      have hs : HasQuaternionBlockDegree 0 n ts :=
        fun s h => hp s (List.mem_cons_of_mem t h)
      have hi := ih hs
      by_cases hnd : n = d
      · simp [headComponent, ht, hnd] at hi ⊢
        exact hi
      · simp [headComponent, ht, hnd] at hi ⊢
        exact hi

/-- All signed contributions at this degree, with within-degree cross terms. -/
def grouped {blocks : Nat} (d : Nat) (ms : List (Mode blocks)) : RatPoly :=
  headComponent d (sumHarmonics ms)

theorem grouped_filter {blocks : Nat} (d : Nat) : ∀ ms : List (Mode blocks),
    grouped d ms = sumHarmonics (ms.filter fun m => decide (m.degree = d))
  | [] => rfl
  | m::ms => by
      change headComponent d (polyAdd (harmonicPart m) (sumHarmonics ms)) = _
      have ha : headComponent d (polyAdd (harmonicPart m) (sumHarmonics ms)) =
          polyAdd (headComponent d (harmonicPart m)) (grouped d ms) := List.filter_append _ _
      rw [ha, headComponent_of_degree d (harmonicPart_degree m), grouped_filter d ms]
      by_cases hd : m.degree = d
      · simp [hd, sumHarmonics]
      · simp [hd, polyAdd, polyZero]

theorem sumHarmonics_harmonic {blocks : Nat} : ∀ ms : List (Mode blocks),
    RatPolyCoeffEqv (headLaplacian (sumHarmonics ms)) polyZero
  | [] => RatPolyCoeffEqv.refl _
  | m::ms => (headLaplacian_add _ _).trans
      ((harmonicPart_harmonic m).add (sumHarmonics_harmonic ms))

theorem grouped_harmonic {blocks : Nat} (d : Nat) (ms : List (Mode blocks)) :
    RatPolyCoeffEqv (headLaplacian (grouped d ms)) polyZero := by
  rw [grouped_filter]
  exact sumHarmonics_harmonic _

theorem grouped_degree {blocks : Nat} (d : Nat) (ms : List (Mode blocks)) :
    HasQuaternionBlockDegree 0 d (grouped d ms) := headComponent_degree _ _

theorem grouped_supported {blocks : Nat} (d : Nat) (ms : List (Mode blocks)) :
    SupportedQuaternionBlocks blocks (grouped d ms) :=
  headComponent_supported (sumHarmonics_supported ms)

/-- Orthogonality is only claimed across unequal harmonic degrees. -/
theorem harmonic_cross_degree {n d : Nat} {p q : RatPoly}
    (hp : HasQuaternionBlockDegree 0 n p)
    (hhp : RatPolyCoeffEqv (headLaplacian p) polyZero)
    (hq : HasQuaternionBlockDegree 0 d q)
    (hhq : RatPolyCoeffEqv (headLaplacian q) polyZero) (hne : n ≠ d) :
    RatPolyCoeffEqv (partialHaarHead (polyMul p q)) polyZero := by
  by_cases hdn : d < n
  · exact partialHaarHead_harmonic_lower_degree hp hhp hq hdn
  · exact (partialHaarHead_congr (RatPolyCoeffEqv.mul_comm p q)).trans
      (partialHaarHead_harmonic_lower_degree hq hhq hp (by omega))

private theorem partial_cross_sum (f : Nat → RatPoly)
    (hf : ∀ d, HasQuaternionBlockDegree 0 d (f d))
    (hh : ∀ d, RatPolyCoeffEqv (headLaplacian (f d)) polyZero)
    (n : Nat) : ∀ ids : List Nat, n ∉ ids →
    RatPolyCoeffEqv (partialHaarHead (polyMul (f n) (polySum (ids.map f)))) polyZero
  | [], _ => partialHaarHead_congr (RatPolyCoeffEqv.mul_zero_right _)
  | d::ds, hn => by
      have hd : n ≠ d := fun h => hn (h ▸ List.mem_cons_self)
      have hs : n ∉ ds := fun h => hn (List.mem_cons_of_mem d h)
      have hsplit := partialHaarHead_congr
        (RatPolyCoeffEqv.mul_add_right (f n) (f d) (polySum (ds.map f)))
      rw [partialHaarHead_add] at hsplit
      exact hsplit.trans ((harmonic_cross_degree (hf n) (hh n) (hf d) (hh d) hd).add
        (partial_cross_sum f hf hh n ds hs))

/-- Polynomial-valued Pythagoras for distinct harmonic-degree groups. -/
theorem partial_norm_sum (f : Nat → RatPoly)
    (hf : ∀ d, HasQuaternionBlockDegree 0 d (f d))
    (hh : ∀ d, RatPolyCoeffEqv (headLaplacian (f d)) polyZero) :
    ∀ ids : List Nat, ids.Nodup →
    RatPolyCoeffEqv
      (partialHaarHead (polyMul (polySum (ids.map f)) (polySum (ids.map f))))
      (polySum (ids.map fun d => partialHaarHead (polyMul (f d) (f d))))
  | [], _ => RatPolyCoeffEqv.refl _
  | n::ns, hids => by
      have hn := (List.nodup_cons.mp hids).1
      have hs := (List.nodup_cons.mp hids).2
      let s := polySum (ns.map f)
      have hcross := partial_cross_sum f hf hh n ns hn
      have hrev := (partialHaarHead_congr (RatPolyCoeffEqv.mul_comm s (f n))).trans hcross
      have hleft := partialHaarHead_congr (RatPolyCoeffEqv.mul_add_right (f n) (f n) s)
      rw [partialHaarHead_add] at hleft
      have hright := partialHaarHead_congr (RatPolyCoeffEqv.mul_add_right s (f n) s)
      rw [partialHaarHead_add] at hright
      have hl := hleft.trans (((RatPolyCoeffEqv.refl _).add hcross).trans
        (RatPolyCoeffEqv.add_zero _))
      have hr := hright.trans ((hrev.add (partial_norm_sum f hf hh ns hs)).trans
        (RatPolyCoeffEqv.zero_add _))
      change RatPolyCoeffEqv (partialHaarHead (polyMul (polyAdd (f n) s) (polyAdd (f n) s))) _
      rw [polyMul_add_left_exact, partialHaarHead_add]
      exact hl.add hr

/-- The actual computed harmonic representative, grouped rather than termwise. -/
theorem grouped_partial_norm {blocks : Nat} (ms : List (Mode blocks)) :
    RatPolyCoeffEqv
      (partialHaarHead (polyMul (sumHarmonics ms) (sumHarmonics ms)))
      (polySum ((headDegrees (sumHarmonics ms)).map fun d =>
        partialHaarHead (polyMul (grouped d ms) (grouped d ms)))) := by
  have he := headComponent_reassembly (sumHarmonics ms)
  exact (partialHaarHead_congr (he.symm.mul he.symm)).trans
    (partial_norm_sum (fun d => grouped d ms) (fun d => grouped_degree d ms)
      (fun d => grouped_harmonic d ms) _ (YMGap.Continuum.CayleyParentInj.range_nodup _))

private theorem haar_sum (blocks : Nat) (f : Nat → RatPoly) : ∀ ids : List Nat,
    quaternionHaar blocks (polySum (ids.map f)) ≈
      qListSum (ids.map fun d => quaternionHaar blocks (f d))
  | [] => Q'.eqv_refl _
  | _::ds => Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_sum blocks f ds))

private theorem qListSum_congr (f g : Nat → Q') : ∀ ids : List Nat,
    (∀ d, d ∈ ids → f d ≈ g d) → qListSum (ids.map f) ≈ qListSum (ids.map g)
  | [], _ => Q'.eqv_refl _
  | d::ds, h => Q'.add_eqv_congr' (h d List.mem_cons_self)
      (qListSum_congr f g ds (fun k hk => h k (List.mem_cons_of_mem d hk)))

/-- Full-Haar Pythagoras for the original, arbitrary supported input.
The computed groups include their complete signed within-degree sums. -/
theorem polynomial_norm {tail : Nat} (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1) (polyMul p p) ≈
      qListSum ((headDegrees (sumHarmonics (modes (tail+1) (by omega) p))).map fun d =>
        quaternionHaar (tail+1)
          (polyMul (grouped d (modes (tail+1) (by omega) p))
            (grouped d (modes (tail+1) (by omega) p)))) := by
  let ms := modes (tail+1) (by omega) p
  have hc := polynomial_harmonic_carrier (by omega : 0 < tail+1) p hp
  apply Q'.eqv_trans _ _ _ (haar_of_carrier (HaarCarrierEqv.mul hc hc))
  apply Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead tail _))
  apply Q'.eqv_trans _ _ _ (haar_of_coeff (grouped_partial_norm ms))
  apply Q'.eqv_trans _ _ _ (haar_sum tail _ _)
  exact qListSum_congr _ _ _ (fun _ _ => quaternionHaar_partialHaarHead tail _)

theorem grouped_norm_nonnegative {blocks : Nat} (d : Nat) (ms : List (Mode blocks)) :
    (0 : Q') ≤ quaternionHaar blocks (polyMul (grouped d ms) (grouped d ms)) :=
  (Certificate.square _ (grouped_supported d ms)).haar_nonnegative

end YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm

#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm.grouped_filter
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm.headComponent_of_degree
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm.sumHarmonics_harmonic
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm.grouped_harmonic
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm.grouped_degree
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm.grouped_supported
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm.harmonic_cross_degree
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm.partial_norm_sum
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm.grouped_partial_norm
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm.polynomial_norm
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm.grouped_norm_nonnegative
