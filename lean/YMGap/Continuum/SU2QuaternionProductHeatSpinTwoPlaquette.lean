/-
Exact product-heat transmission for the label-two plaquette character.

The four one-link steps are the literal arbitrary-chart transmission theorem.
Cyclic Haar invariance only changes which link is exposed next; it does not
change the kinetic carrier or the spectator.  The result is therefore an
identity for the original product heat, not for an interacting transfer map.
-/

import YMGap.Continuum.SU2QuaternionSpinTwoPlaquetteLiteral
import YMGap.Continuum.SU2QuaternionProductHeatPlaquette

namespace YMGap.Continuum.SU2QuaternionProductHeatSpinTwoPlaquette

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex select_perm)
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionSpinTwoPlaquetteLiteral
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem cyclic_inside (blocks a b c d : Nat)
    (r0 r1 r2 r3 : Bool) (A q : RatPoly) :
    quaternionHaar blocks (polyMul A (polyMul
      (characterPolynomial (word a b c d r0 r1 r2 r3).scalar 2) q)) ≈
    quaternionHaar blocks (polyMul A (polyMul
      (characterPolynomial (word b c d a r1 r2 r3 r0).scalar 2) q)) := by
  have rearrange (s : RatPoly) : RatPolyCoeffEqv
      (polyMul A (polyMul s q)) (polyMul s (polyMul A q)) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => A | 1 => s | _ => q)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (rearrange _))
    (Q'.eqv_trans _ _ _ (haar_cyclic blocks a b c d r0 r1 r2 r3 2 (polyMul A q))
      (haar_of_coeff (rearrange _).symm))

private theorem remove_selected (n : Nat) (w : Q') (K lower b c d : Nat)
    (ids : List Nat) (hlower : lower < n) (hb : b < n+n) (hc : c < n+n)
    (hd : d < n+n) (hnot : lower ∉ ids)
    (hids : ∀ j, j ∈ ids → j < n)
    (hlu : lower ≠ n+lower) (hlb : lower ≠ b) (hlc : lower ≠ c)
    (hub : n+lower ≠ b) (huc : n+lower ≠ c) (hbc : b ≠ c)
    (hld : lower ≠ d) (hud : n+lower ≠ d) (hbd : b ≠ d)
    (hcd : c ≠ d) (r0 r1 r2 r3 : Bool) (hK : 2 ≤ K)
    (g : RatPoly) (hg : SupportedQuaternionBlocks n g) :
    quaternionHaar (n+n) (polyMul (productHeat n w K (lower::ids))
      (polyMul (characterPolynomial (word lower b c d r0 r1 r2 r3).scalar 2)
        (liftBoundary n g))) ≈
    qpow w 8 * quaternionHaar (n+n) (polyMul (productHeat n w K ids)
      (polyMul (characterPolynomial (word (n+lower) b c d r0 r1 r2 r3).scalar 2)
        (liftBoundary n g))) := by
  have hs := supported_polyMul (productHeat_supported n w K ids hids) (lift_supported hg n)
  have hi := (independent_has_degree_zero
    (productHeat_independent_lower n w K ids hids lower hlower hnot)).mul
      (independent_has_degree_zero (lift_lower_independent n g lower hlower))
  have heq : n+n-1+1 = n+n := by omega
  have h := spinTwoPlaquette_literal_heat_pairing (tail := n+n-1) (by omega)
    ⟨lower, by omega⟩ ⟨n+lower, by omega⟩
    ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, by omega⟩
    hlu hlb hlc hub huc hbc hld hud hbd hcd r0 r1 r2 r3 w K hK
    (polyMul (productHeat n w K ids) (liftBoundary n g))
    (by simpa only [heq] using hs) hi
  dsimp only at h
  rw [heq] at h
  have rearrange (s : RatPoly) : RatPolyCoeffEqv
      (polyMul (productHeat n w K ids) (polyMul s (liftBoundary n g)))
      (polyMul s (polyMul (productHeat n w K ids) (liftBoundary n g))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => productHeat n w K ids | 1 => s | _ => liftBoundary n g)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.mul_assoc _ _ _).trans
      (((rearrange _).mul_left _).trans (RatPolyCoeffEqv.mul_assoc _ _ _).symm)))
    (Q'.eqv_trans _ _ _ h
      (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (rearrange _).symm)))

private theorem four_factors (w z : Q') :
    qpow w 8 * (qpow w 8 * (qpow w 8 * (qpow w 8 * z))) ≈ qpow w 32 * z :=
  poly_identity_of_normal_eq
    (.mul (.pow (.var 0) 8) (.mul (.pow (.var 0) 8)
      (.mul (.pow (.var 0) 8) (.mul (.pow (.var 0) 8) (.var 1)))))
    (.mul (.pow (.var 0) 32) (.var 1)) (by decide) (fun | 0 => w | _ => z)

private def chi2 (a b c d : Nat) : RatPoly :=
  characterPolynomial (word a b c d false false true true).scalar 2

theorem selected_pairing (n : Nat) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (a b c d : Nat) (ids : List Nat) (hn : (a::b::c::d::ids).Nodup)
    (hids : ∀ i, i ∈ a::b::c::d::ids → i < n)
    (g : RatPoly) (hg : SupportedQuaternionBlocks n g) :
    quaternionHaar n (polyMul g (productMap n w K (a::b::c::d::ids)
      (characterPolynomial (word a b c d false false true true).scalar 2))) ≈
      qpow w 32 * quaternionHaar n (polyMul g
        (characterPolynomial (word a b c d false false true true).scalar 2)) := by
  have hna := List.nodup_cons.mp hn
  have hnb := List.nodup_cons.mp hna.2
  have hnc := List.nodup_cons.mp hnb.2
  have hnd := List.nodup_cons.mp hnc.2
  have ha : a < n := hids a (by simp)
  have hb : b < n := hids b (by simp)
  have hc : c < n := hids c (by simp)
  have hd : d < n := hids d (by simp)
  have hab : a ≠ b := fun he => hna.1 (by simp [he])
  have hac : a ≠ c := fun he => hna.1 (by simp [he])
  have had : a ≠ d := fun he => hna.1 (by simp [he])
  have hbc : b ≠ c := fun he => hnb.1 (by simp [he])
  have hbd : b ≠ d := fun he => hnb.1 (by simp [he])
  have hcd : c ≠ d := fun he => hnc.1 (by simp [he])
  have h0 := remove_selected n w K a b c d (b::c::d::ids) ha (by omega) (by omega)
    (by omega) hna.1 (fun i hi => hids i (List.mem_cons_of_mem a hi))
    (by omega) hab hac (by omega) (by omega) hbc had (by omega) hbd hcd
    false false true true hK g hg
  have c0 := cyclic_inside (n+n) (n+a) b c d false false true true
    (productHeat n w K (b::c::d::ids)) (liftBoundary n g)
  have h1 := remove_selected n w K b c d (n+a) (c::d::ids) hb (by omega) (by omega)
    (by omega) hnb.1
    (fun i hi => hids i (List.mem_cons_of_mem a (List.mem_cons_of_mem b hi)))
    (by omega) hbc hbd (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) false true true false hK g hg
  have c1 := cyclic_inside (n+n) (n+b) c d (n+a) false true true false
    (productHeat n w K (c::d::ids)) (liftBoundary n g)
  have h2 := remove_selected n w K c d (n+a) (n+b) (d::ids) hc (by omega) (by omega)
    (by omega) hnc.1
    (fun i hi => hids i (List.mem_cons_of_mem a (List.mem_cons_of_mem b
      (List.mem_cons_of_mem c hi))))
    (by omega) hcd (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) true true false false hK g hg
  have c2 := cyclic_inside (n+n) (n+c) d (n+a) (n+b) true true false false
    (productHeat n w K (d::ids)) (liftBoundary n g)
  have h3 := remove_selected n w K d (n+a) (n+b) (n+c) ids hd (by omega) (by omega)
    (by omega) hnd.1
    (fun i hi => hids i (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hi)))))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) true false false true hK g hg
  have c3 := cyclic_inside (n+n) (n+d) (n+a) (n+b) (n+c) true false false true
    (productHeat n w K ids) (liftBoundary n g)
  have htail : quaternionHaar (n+n) (polyMul (productHeat n w K ids)
      (polyMul (chi2 (n+a) (n+b) (n+c) (n+d)) (liftBoundary n g))) ≈
      quaternionHaar n (polyMul g (chi2 a b c d)) := by
    have hlift := lift_word_character (n+n) n a b c d false false true true 2
    have hpadded := (PaddedPolynomialCoeffEqv.refl (n+n) (productHeat n w K ids)).mul
      (hlift.mul (PaddedPolynomialCoeffEqv.refl (n+n) (liftBoundary n g)))
    have hsleft : SupportedQuaternionBlocks (n+n)
        (polyMul (productHeat n w K ids)
          (polyMul (chi2 (n+a) (n+b) (n+c) (n+d)) (liftBoundary n g))) :=
      supported_polyMul (productHeat_supported n w K ids
      (fun i hi => hids i (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hi))))))
      (supported_polyMul (word_supported (by omega) (by omega) (by omega) (by omega)
        false false true true 2) (lift_supported hg n))
    have hsright : SupportedQuaternionBlocks (n+n)
        (polyMul (productHeat n w K ids)
          (polyMul (liftBoundary n (chi2 a b c d)) (liftBoundary n g))) := by
      rw [← lift_product]
      exact supported_polyMul (productHeat_supported n w K ids
        (fun i hi => hids i (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hi))))))
        (lift_supported (supported_polyMul
          (word_supported ha hb hc hd false false true true 2) hg) n)
    have hm := productHeat_upper_marginal n w K ids hnd.2
      (fun i hi => hids i (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hi)))))
      (polyMul (chi2 a b c d) g)
      (supported_polyMul (word_supported ha hb hc hd false false true true 2) hg)
    rw [lift_product] at hm
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hpadded.haar hsright hsleft))
      (Q'.eqv_trans _ _ _ hm (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
  have e3 := Q'.eqv_trans _ _ _ h3 (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ c3 htail))
  have e2 := Q'.eqv_trans _ _ _ h2 (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ c2 e3))
  have e1 := Q'.eqv_trans _ _ _ h1 (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ c1 e2))
  have e0 := Q'.eqv_trans _ _ _ h0 (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ c0 e1))
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K _ _ g)
    (Q'.eqv_trans _ _ _ e0 (four_factors w _))

theorem productMap_spinTwoPlaquette_of_perm
    (n : Nat) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (a b c d : Nat) (ids rest : List Nat) (hn : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) (hp : ids.Perm (a::b::c::d::rest)) :
    SupportedHaarEqv n (productMap n w K ids
      (characterPolynomial (word a b c d false false true true).scalar 2))
      (polySmul (qpow w 32)
        (characterPolynomial (word a b c d false false true true).scalar 2)) := by
  intro g hg
  have hchange := haar_of_coeff (blocks := n+n)
    ((polynomialProduct_perm (fun i => heatAt i (n+i) w K) hp).mul_right
      (polyMul (chi2 a b c d) (liftBoundary n g)))
  have hpair := selected_pairing n w K hK a b c d rest (hp.nodup_iff.mp hn)
    (fun i hi => hids i (hp.mem_iff.mpr hi)) g hg
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K ids _ g)
    (Q'.eqv_trans _ _ _ hchange (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (productMap_pairing n w K (a::b::c::d::rest) _ g))
      (Q'.eqv_trans _ _ _ hpair
        (Q'.eqv_symm (quaternionHaar_polyMul_smul_right n _ g _)))))

end YMGap.Continuum.SU2QuaternionProductHeatSpinTwoPlaquette

#print axioms YMGap.Continuum.SU2QuaternionProductHeatSpinTwoPlaquette.selected_pairing
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSpinTwoPlaquette.productMap_spinTwoPlaquette_of_perm
