/-
# Copying a head polynomial while adjoining a spare retained link

The four head exponents stay in place; a zero quaternion block is inserted
before all tail exponents. Thus p(x,z) becomes p(x,z) on (x,y,z), with the
new y slot unused. This explicit coordinate operation preserves the head
Laplacian and Haar norm. The retained substitution will identify its output
with p(y,z), not with a free or independently chosen observable.
-/

import YMGap.Continuum.SU2QuaternionGroupedHeatComparison
import YMGap.Continuum.SU2QuaternionHaarCertificateLift

namespace YMGap.Continuum.SU2QuaternionSpareHeadCopy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionFischerRadial
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution
open YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra

local infix:50 " ≈ " => Q'.eqv

def copyMonomial (m : List Nat) : List Nat :=
  [exponentAt m 0, exponentAt m 1, exponentAt m 2, exponentAt m 3,
    0, 0, 0, 0] ++ m.drop 4

def copy (p : RatPoly) : RatPoly := p.map fun t => (copyMonomial t.1, t.2)

theorem copy_add (p q : RatPoly) : copy (polyAdd p q) = polyAdd (copy p) (copy q) :=
  List.map_append

theorem copy_smul (c : Q') (p : RatPoly) : copy (polySmul c p) = polySmul c (copy p) := by
  simp only [copy, polySmul, List.map_map]
  rfl

theorem copy_congr {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (copy p) (copy q) := by
  intro weight
  have he : ∀ r : RatPoly, ratWeightedSum weight (copy r) =
      ratWeightedSum (fun m => weight (copyMonomial m)) r := by
    intro r
    induction r with
    | nil => rfl
    | cons t ts ih => change _ + ratWeightedSum weight (copy ts) = _; rw [ih]; rfl
  rw [he p, he q]
  exact h _

theorem copyMonomial_head (m : List Nat) {i : Nat} (hi : i < 4) :
    exponentAt (copyMonomial m) i = exponentAt m i := by
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

theorem copy_degree {d : Nat} {p : RatPoly} (hp : HasQuaternionBlockDegree 0 d p) :
    HasQuaternionBlockDegree 0 d (copy p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem copy_spare_independent (p : RatPoly) : HasQuaternionBlockDegree 1 0 (copy p) := by
  intro t ht
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
  rfl

theorem copy_supported {blocks : Nat} (hb : 0 < blocks) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks (blocks+1) (copy p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have h := hp s hs
  change (copyMonomial s.1).length ≤ _
  simp only [copyMonomial, List.length_append, List.length_cons, List.length_nil, List.length_drop]
  omega

theorem copy_padded (p : RatPoly) : HeadPadded (copy p) := by
  intro t ht
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
  change 4 ≤ (copyMonomial s.1).length
  simp [copyMonomial]

private theorem copyMonomial_lower {i : Nat} (hi : i < 4) (m : List Nat)
    (hm : 4 ≤ m.length) :
    copyMonomial (lowerExponentAt i m) = lowerExponentAt i (copyMonomial m) := by
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases m with _ | ⟨a, m⟩ <;> try simp at hm
  rcases m with _ | ⟨b, m⟩ <;> try simp at hm
  rcases m with _ | ⟨c, m⟩ <;> try simp at hm
  rcases m with _ | ⟨d, m⟩ <;> try simp at hm
  rcases h with rfl | rfl | rfl | rfl <;> rfl

theorem copy_derivative {i : Nat} (hi : i < 4) : ∀ p : RatPoly, HeadPadded p →
    copy (ratDerivative i p) = ratDerivative i (copy p)
  | [], _ => rfl
  | t::ts, hp => by
      simp only [copy, ratDerivative, List.map_cons]
      have he := copyMonomial_lower hi t.1 (hp t List.mem_cons_self)
      have hc := copyMonomial_head t.1 hi
      change (copyMonomial (lowerExponentAt i t.1), Q'.ofNat (exponentAt t.1 i)*t.2) :: _ =
        (lowerExponentAt i (copyMonomial t.1), Q'.ofNat (exponentAt (copyMonomial t.1) i)*t.2) :: _
      rw [he, hc]
      exact congrArg (List.cons _) (copy_derivative hi ts
        (fun s hs => hp s (List.mem_cons_of_mem t hs)))

private theorem lower_length (i : Nat) : ∀ m : List Nat,
    (lowerExponentAt i m).length = m.length
  | [] => by cases i <;> rfl
  | _::m => by
      cases i with
      | zero => rfl
      | succ i => exact congrArg Nat.succ (lower_length i m)

private theorem derivative_padded (i : Nat) {p : RatPoly} (hp : HeadPadded p) :
    HeadPadded (ratDerivative i p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  change 4 ≤ (lowerExponentAt i s.1).length
  rw [lower_length]
  exact hp s hs

theorem copy_laplacian {p : RatPoly} (hp : HeadPadded p) :
    copy (headLaplacian p) = headLaplacian (copy p) := by
  have h (i : Nat) (hi : i < 4) :
      copy (ratDerivative i (ratDerivative i p)) = ratDerivative i (ratDerivative i (copy p)) := by
    rw [copy_derivative hi _ (derivative_padded i hp), copy_derivative hi p hp]
  simp only [headLaplacian, copy_add, h 0 (by decide), h 1 (by decide),
    h 2 (by decide), h 3 (by decide)]

theorem copy_harmonic {p : RatPoly} (hp : HeadPadded p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    RatPolyCoeffEqv (headLaplacian (copy p)) polyZero := by
  rw [← copy_laplacian hp]
  exact copy_congr hh

theorem partial_copy (p : RatPoly) :
    partialHaarHead (copy p) = liftHead (partialHaarHead p) := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
      change partialHaarHeadTerm (copyMonomial t.1, t.2) :: _ =
        (0::0::0::0::(partialHaarHeadTerm t).1, (partialHaarHeadTerm t).2) :: _
      exact congrArg (List.cons _) ih

/-- Normalized Haar integration drops only the explicitly unused new slot. -/
theorem haar_copy (tail : Nat) (p : RatPoly) :
    quaternionHaar (tail+2) (copy p) ≈ quaternionHaar (tail+1) p :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead (tail+1) (copy p)))
    (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (congrArg (quaternionHaar (tail+1)) (partial_copy p)))
      (Q'.eqv_trans _ _ _ (haar_liftBoundary 1 tail (partialHaarHead p))
        (quaternionHaar_partialHaarHead tail p)))

private def varPowerMono (i : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => monoMul (varPowerMono i n) (varMono i)

private theorem var_power (i : Nat) : ∀ n,
    ratPolyPow (polyVar i) n = [(varPowerMono i n, (1 : Q'))]
  | 0 => rfl
  | n+1 => by rw [ratPolyPow, var_power i n]; rfl

private theorem varPowerMono_exponent (i j : Nat) : ∀ n,
    exponentAt (varPowerMono i n) j = if j = i then n else 0
  | 0 => by simp [varPowerMono, exponentAt]
  | n+1 => by
      rw [varPowerMono, SU2QuaternionRatPolyDifferential.exponentAt_monoMul,
        varPowerMono_exponent i j n, exponentAt_varMono]
      by_cases h : j = i <;> simp [h]

private def translatedCopyMono (m : List Nat) : List Nat :=
  monoMul
    (monoMul (varPowerMono 4 (exponentAt m 0))
      (monoMul (varPowerMono 5 (exponentAt m 1))
        (monoMul (varPowerMono 6 (exponentAt m 2)) (varPowerMono 7 (exponentAt m 3)))))
    (0::0::0::0::0::0::0::0::m.drop 4)

private theorem translated_copy_term (t : RatTerm) :
    translatedHeadTerm (PolyQuaternion.coordinateVariable 1) (copyMonomial t.1, t.2) =
      [(translatedCopyMono t.1, (1 : Q')*t.2)] := by
  unfold translatedHeadTerm translatedHeadMonomial
  change polyMul
    (polyMul (ratPolyPow (polyVar 4) (exponentAt t.1 0))
      (polyMul (ratPolyPow (polyVar 5) (exponentAt t.1 1))
        (polyMul (ratPolyPow (polyVar 6) (exponentAt t.1 2))
          (ratPolyPow (polyVar 7) (exponentAt t.1 3))))) _ = _
  rw [var_power, var_power, var_power, var_power]
  rfl

private theorem translatedCopyMono_exponent (m : List Nat) (j : Nat) :
    exponentAt ((translatedCopyMono m).drop 4) j = exponentAt m j := by
  rw [exponentAt_drop]
  simp only [translatedCopyMono, SU2QuaternionRatPolyDifferential.exponentAt_monoMul,
    varPowerMono_exponent]
  by_cases hj : j < 4
  · have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> simp [exponentAt]
  · have h0 : 4+j ≠ 4 := by omega
    have h1 : 4+j ≠ 5 := by omega
    have h2 : 4+j ≠ 6 := by omega
    have h3 : 4+j ≠ 7 := by omega
    simp only [h0, h1, h2, h3, if_false, Nat.zero_add]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hj)
    have he : 4+(4+k) = 8+k := by omega
    rw [he]
    rw [Nat.add_comm 8 k]
    change exponentAt (m.drop 4) k = exponentAt m (4+k)
    exact exponentAt_drop m 4 k

/-- Retained substitution is the original polynomial on (y,z), including
every spectator coordinate. Prefix equality records padding honestly. -/
theorem substitute_copy_prefix (blocks : Nat) : ∀ p : RatPoly,
    QuaternionPrefixPolynomialEqv blocks (substituteRetained (copy p)) p
  | [] => .nil
  | t::ts => by
      have ht := translated_copy_term t
      change QuaternionPrefixPolynomialEqv blocks
        (dropHeadPolynomial (polyAdd
          (translatedHeadTerm (PolyQuaternion.coordinateVariable 1) (copyMonomial t.1, t.2))
          (translatedHeadPolynomial (PolyQuaternion.coordinateVariable 1) (copy ts)))) _
      rw [ht]
      apply QuaternionPrefixPolynomialEqv.cons
      · exact ⟨Q'.one_mul_eqv _, fun j _ => translatedCopyMono_exponent t.1 j⟩
      · exact substitute_copy_prefix blocks ts

theorem substitute_copy_carrier {blocks : Nat} (hb : 0 < blocks) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    HaarCarrierEqv blocks (substituteRetained (copy p)) p :=
  carrierOfPrefix (substituteRetained_supported blocks hb (copy_supported hb hp)) hp
    (substitute_copy_prefix blocks p)

private def spareSwap (blocks : Nat) (hb : 0 < blocks) : QuaternionBlockInvolution (blocks+1) :=
  blockSwapInvolution (blocks+1) 0 1 (by omega) (by omega)

private theorem copy_reindex_prefix (blocks : Nat) (hb : 0 < blocks) : ∀ p : RatPoly,
    QuaternionPrefixPolynomialEqv (blocks+1)
      (reindexQuaternionPolynomial (spareSwap blocks hb) (liftHead p)) (copy p)
  | [] => .nil
  | t::ts => by
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, ?_⟩
        intro j hj
        change exponentAt (reindexQuaternionExponents (spareSwap blocks hb)
          (0::0::0::0::t.1)) j = exponentAt (copyMonomial t.1) j
        rw [exponentAt_reindexQuaternionExponents _ _ hj]
        by_cases hj8 : j < 8
        · have h : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
          rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
        · have h0 : j/4 ≠ 0 := by omega
          have h1 : j/4 ≠ 1 := by omega
          have hs : (spareSwap blocks hb).map (j/4) = j/4 := by
            simp [spareSwap, blockSwapInvolution, blockSwapMap, h0, h1]
          rw [hs, show 4*(j/4)+j%4=j by omega]
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hj8)
          rw [Nat.add_comm 8 k]
          change exponentAt t.1 (k+4) = exponentAt (t.1.drop 4) k
          rw [exponentAt_drop, Nat.add_comm 4 k]
      · exact copy_reindex_prefix blocks hb ts

/-- Copying is a genuine Haar-carrier embedding, not substitution of a
new surrogate input. Both support guards prevent dropping tail variables. -/
theorem copy_carrier {blocks : Nat} (hb : 0 < blocks) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (h : HaarCarrierEqv blocks p q) : HaarCarrierEqv (blocks+1) (copy p) (copy q) := by
  have cp := carrierOfPrefix (reindex_supported (spareSwap blocks hb) (liftHead p))
    (copy_supported hb hp) (copy_reindex_prefix blocks hb p)
  have cq := carrierOfPrefix (reindex_supported (spareSwap blocks hb) (liftHead q))
    (copy_supported hb hq) (copy_reindex_prefix blocks hb q)
  exact cp.symm.trans ((reindex_carrier (spareSwap blocks hb)
    (lift_supported hp 1) (lift_supported hq 1) (lift_carrier 1 h)).trans cq)

end YMGap.Continuum.SU2QuaternionSpareHeadCopy

#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.copy_congr
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.copy_add
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.copy_smul
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.copy_degree
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.copyMonomial_head
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.copy_spare_independent
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.copy_supported
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.copy_padded
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.copy_derivative
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.copy_laplacian
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.copy_harmonic
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.partial_copy
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.haar_copy
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.substitute_copy_prefix
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.substitute_copy_carrier
#print axioms YMGap.Continuum.SU2QuaternionSpareHeadCopy.copy_carrier
