/-
# Spectator equivariance of the actual head heat map

A block involution fixing the active block commutes with the literal head
heat update.  The proof extends it across the spare copied block and uses an
exact finite Haar change of variables, retaining arbitrary insertion tests.
-/

import YMGap.Continuum.SU2QuaternionConjugatedHeadHeat
import YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord

namespace YMGap.Continuum.SU2QuaternionHeadHeatSpectatorEquivariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionSpareHeadCopy
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionConjugatedHeadHeat
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private def spareExtension {blocks : Nat}
    (s : QuaternionBlockInvolution blocks) : QuaternionBlockInvolution (blocks+1) where
  map i := if i = 0 then 0 else s.map (i-1) + 1
  map_lt := by
    intro i hi
    by_cases h : i = 0
    · simp [h]
    · simp [h]
      have hs := s.map_lt (i-1) (by omega)
      omega
  involutive := by
    intro i hi
    by_cases h : i = 0
    · simp [h]
    · have hi : i-1 < blocks := by omega
      have hm : s.map (i-1)+1 ≠ 0 := by omega
      simp only [h, if_false, hm]
      rw [show s.map (i-1)+1-1=s.map (i-1) by omega,
        s.involutive (i-1) hi]
      omega

private theorem exponentAt_copy_tail (m : List Nat) (k : Nat) :
    exponentAt (copyMonomial m) (8+k) = exponentAt m (4+k) := by
  unfold copyMonomial
  have h8 := exponentAt_drop
    ([exponentAt m 0, exponentAt m 1, exponentAt m 2, exponentAt m 3,
      0, 0, 0, 0] ++ m.drop 4) 8 k
  have h4 := exponentAt_drop m 4 k
  simpa using h8.symm.trans h4

private theorem spareExtension_copy_prefix {blocks : Nat}
    (hb : 0 < blocks) (s : QuaternionBlockInvolution blocks)
    (h0 : s.map 0 = 0) : ∀ p : RatPoly,
    QuaternionPrefixPolynomialEqv (blocks+1)
      (reindexQuaternionPolynomial (spareExtension s)
        (copy (reindexQuaternionPolynomial s p)))
      (copy p)
  | [] => .nil
  | t :: ts => by
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, ?_⟩
        intro j hj
        change exponentAt (reindexQuaternionExponents (spareExtension s)
            (copyMonomial (reindexQuaternionExponents s t.1))) j =
          exponentAt (copyMonomial t.1) j
        rw [exponentAt_reindexQuaternionExponents _ _ hj]
        by_cases hj4 : j < 4
        · have hjb : j < 4*blocks := by omega
          have hd : j/4=0 := by omega
          have hr : j%4=j := by omega
          rw [hd, hr]
          rw [show (spareExtension s).map 0=0 by rfl]
          simp only [Nat.mul_zero, Nat.zero_add]
          rw [copyMonomial_head _ hj4, copyMonomial_head _ hj4,
            exponentAt_reindexQuaternionExponents s t.1 hjb]
          rw [hd, h0, hr]
          simp only [Nat.mul_zero, Nat.zero_add]
        · by_cases hj8 : j < 8
          · have h : j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
            rcases h with rfl | rfl | rfl | rfl <;>
              simp [spareExtension, copyMonomial, h0]
          · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hj8)
            have hk : 4+k < 4*blocks := by omega
            rw [show (8+k)/4=k/4+2 by omega, show (8+k)%4=k%4 by omega]
            simp only [spareExtension, if_neg (show k/4+2 ≠ 0 by omega)]
            rw [show k/4+2-1=k/4+1 by omega]
            have hb' : k/4+1 < blocks := by omega
            have hs0 : s.map (k/4+1) ≠ 0 := by
              intro hs
              have hi := s.involutive (k/4+1) hb'
              rw [hs, h0] at hi
              omega
            rw [show 4*(s.map (k/4+1)+1)+k%4 =
              8+(4*(s.map (k/4+1)-1)+k%4) by omega]
            rw [exponentAt_copy_tail]
            have hmapped : 4*s.map (k/4+1)+k%4 < 4*blocks := by
              have hm := s.map_lt (k/4+1) hb'
              omega
            have hre := exponentAt_reindexQuaternionExponents s t.1 hmapped
            rw [show (4*s.map (k/4+1)+k%4)/4=s.map (k/4+1) by omega,
              show (4*s.map (k/4+1)+k%4)%4=k%4 by omega,
              s.involutive (k/4+1) hb'] at hre
            rw [show 4+(4*(s.map (k/4+1)-1)+k%4) =
              4*s.map (k/4+1)+k%4 by omega, hre]
            rw [show 4*(k/4+1)+k%4=4+k by omega]
            simpa [Nat.add_comm] using (exponentAt_copy_tail t.1 k).symm
      · exact spareExtension_copy_prefix hb s h0 ts

private theorem spareExtension_lift_prefix {blocks : Nat}
    (s : QuaternionBlockInvolution blocks) : ∀ q : RatPoly,
    QuaternionPrefixPolynomialEqv (blocks+1)
      (reindexQuaternionPolynomial (spareExtension s) (liftHead q))
      (liftHead (reindexQuaternionPolynomial s q))
  | [] => .nil
  | t :: ts => by
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, ?_⟩
        intro j hj
        change exponentAt (reindexQuaternionExponents (spareExtension s)
            (0::0::0::0::t.1)) j =
          exponentAt (0::0::0::0::reindexQuaternionExponents s t.1) j
        rw [exponentAt_reindexQuaternionExponents _ _ hj]
        by_cases hj4 : j < 4
        · have h : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
          rcases h with rfl | rfl | rfl | rfl <;> rfl
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hj4)
          have hk : k < 4*blocks := by omega
          rw [show (4+k)/4=k/4+1 by omega, show (4+k)%4=k%4 by omega]
          simp only [spareExtension, if_neg (show k/4+1 ≠ 0 by omega)]
          rw [show k/4+1-1=k/4 by omega]
          rw [show 4*(s.map (k/4)+1)+k%4 = (4*s.map (k/4)+k%4)+4 by omega,
            Nat.add_comm 4 k]
          change exponentAt t.1 (4*s.map (k/4)+k%4) =
            exponentAt (reindexQuaternionExponents s t.1) k
          rw [exponentAt_reindexQuaternionExponents s t.1 hk]
      · exact spareExtension_lift_prefix s ts

private theorem spareExtension_relativeHeat_prefix {blocks : Nat} (hb : 0 < blocks)
    (s : QuaternionBlockInvolution blocks) (h0 : s.map 0 = 0)
    (w : Q') (K : Nat) :
    QuaternionPrefixPolynomialEqv (blocks+1)
      (reindexQuaternionPolynomial (spareExtension s) (relativeHeat w K))
      (relativeHeat w K) := by
  let S := spareExtension s
  have h1 : S.map 1 = 1 := by simp [S, spareExtension, h0]
  have hp : QuaternionPrefixPolyQuaternionEqv (blocks+1)
      (reindexPolyQuaternion S
        (PolyQuaternion.mul (PolyQuaternion.coordinateVariable 0)
          (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 1))))
      (PolyQuaternion.mul (PolyQuaternion.coordinateVariable 0)
        (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 1))) := by
    rw [reindexPolyQuaternion_mul, reindexPolyQuaternion_conj]
    exact (reindex_coordinateVariable_prefix S (by omega)
      (by simp [S, spareExtension])).mul
      (reindex_coordinateVariable_prefix S (by omega) h1).conj
  have hc (d : Nat) : QuaternionPrefixPolynomialEqv (blocks+1)
      (reindexQuaternionPolynomial S (characterPolynomial (scalarAt 0 1) d))
      (characterPolynomial (scalarAt 0 1) d) :=
    (reindexQuaternionPolynomial_character_prefix S _ d).trans (hp.scalar.character d)
  change QuaternionPrefixPolynomialEqv (blocks+1)
    (reindexQuaternionPolynomial S (heatAt 0 1 w K)) (heatAt 0 1 w K)
  unfold heatAt
  induction List.range (K+1) with
  | nil => exact .nil
  | cons d ds ih =>
      simp only [finitePolySum, reindexQuaternionPolynomial_add,
        reindexQuaternionPolynomial_smul]
      exact ((hc d).smul _).append ih

private theorem heatPair_reindex_fix_zero {blocks : Nat} (hb : 0 < blocks)
    (s : QuaternionBlockInvolution blocks) (h0 : s.map 0 = 0)
    (w : Q') (K : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q) :
    heatPair (blocks-1) w K (reindexQuaternionPolynomial s p) q ≈
      heatPair (blocks-1) w K p (reindexQuaternionPolynomial s q) := by
  unfold heatPair
  rw [show blocks-1+2=blocks+1 by omega]
  let S := spareExtension s
  have hrel := spareExtension_relativeHeat_prefix hb s h0 w K
  have hprefix : QuaternionPrefixPolynomialEqv (blocks+1)
      (reindexQuaternionPolynomial S
        (polyMul (polyMul (relativeHeat w K)
          (copy (reindexQuaternionPolynomial s p))) (liftHead q)))
      (polyMul (polyMul (relativeHeat w K) (copy p))
        (liftHead (reindexQuaternionPolynomial s q))) := by
    simp only [reindexQuaternionPolynomial_mul]
    exact (hrel.mul (spareExtension_copy_prefix hb s h0 p)).mul
      (spareExtension_lift_prefix s q)
  have hs := quaternionHaar_reindex S
    (polyMul (polyMul (relativeHeat w K)
      (copy (reindexQuaternionPolynomial s p))) (liftHead q))
    (supported_polyMul
      (supported_polyMul (heat_supported (by omega : 0 < blocks+1) (by omega : 1 < blocks+1) w K)
        (copy_supported hb (reindex_supported s p)))
      (lift_supported hq 1))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hs)
    (quaternionHaar_prefixPolynomialEqv (blocks+1) hprefix
      (reindex_supported S _)
      (supported_polyMul
        (supported_polyMul (heat_supported (by omega : 0 < blocks+1) (by omega : 1 < blocks+1) w K)
          (copy_supported hb hp))
        (lift_supported (reindex_supported s q) 1)))

theorem headMap_reindex_fix_zero_carrier {blocks : Nat} (hb : 0 < blocks)
    (s : QuaternionBlockInvolution blocks) (h0 : s.map 0 = 0)
    (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    HaarCarrierEqv blocks
      (headMap w K (reindexQuaternionPolynomial s p))
      (reindexQuaternionPolynomial s (headMap w K p)) := by
  cases blocks with
  | zero => exact False.elim (Nat.not_lt_zero 0 hb)
  | succ tail =>
      apply carrier_of_supported
        (headMap_supported tail w K (reindex_supported s p))
        (reindex_supported s (headMap w K p))
      intro q hq
      have hl := headMap_pairing tail w K (reindexQuaternionPolynomial s p) q
      have hr := headMap_pairing tail w K p (reindexQuaternionPolynomial s q)
      have hre := reindex_pair s q (headMap w K p) hq
        (headMap_supported tail w K hp)
      exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_trans _ _ _ hl
          (Q'.eqv_trans _ _ _ (heatPair_reindex_fix_zero hb s h0 w K p q hp hq)
            (Q'.eqv_trans _ _ _ (Q'.eqv_symm hr)
              (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
                (Q'.eqv_symm hre)))))

theorem conjugatedHeadMap_fix_zero_carrier {blocks : Nat} (hb : 0 < blocks)
    (s : QuaternionBlockInvolution blocks) (h0 : s.map 0 = 0)
    (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    HaarCarrierEqv blocks (conjugatedHeadMap s w K p) (headMap w K p) := by
  cases blocks with
  | zero => exact False.elim (Nat.not_lt_zero 0 hb)
  | succ tail =>
      have hh := headMap_reindex_fix_zero_carrier hb s h0 w K p hp
      have hm := headMap_supported tail w K (reindex_supported s p)
      have hr := reindex_supported s (headMap w K p)
      have hmap := reindex_carrier s hm hr hh
      have htwice := carrierOfPrefix (reindex_supported s _)
        (headMap_supported tail w K hp)
        (reindex_twice_prefix s (headMap w K p))
      exact HaarCarrierEqv.trans hmap htwice

end YMGap.Continuum.SU2QuaternionHeadHeatSpectatorEquivariance

#print axioms YMGap.Continuum.SU2QuaternionHeadHeatSpectatorEquivariance.headMap_reindex_fix_zero_carrier
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatSpectatorEquivariance.conjugatedHeadMap_fix_zero_carrier
