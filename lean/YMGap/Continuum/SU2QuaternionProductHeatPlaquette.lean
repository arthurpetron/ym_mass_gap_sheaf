/-
# Exact plaquette transmission on the original product-heat carrier

Four distinct selected links may occupy arbitrary positions in the slice.
Transmit each coordinate through its full heat packet, retaining all other
kinetic factors, and then use the exact remaining marginal. This proves
P(chi_plaquette)=w^12*chi_plaquette under every supported Haar test.

This is a kinetic identity, not an eigenidentity for the interacting map
P(V*f). A dependent spatial/terminal weight is allowed in the final Haar
test, not falsely treated as independent during lower-link integration.
-/

import YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.QuaternionHaarWordLift
import YMGap.Continuum.SU2QuaternionWeightedProductLocalGap

namespace YMGap.Continuum.SU2QuaternionProductHeatPlaquette

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
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionLinearHeatPropagation
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex select_perm)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWordLift

local infix:50 " ≈ " => Q'.eqv

private theorem support_smul {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (c : Q') :
    SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem fourWord_supported {n a b c d : Nat} (ha : a < n) (hb : b < n)
    (hc : c < n) (hd : d < n) : SupportedQuaternionBlocks n (plaquette a b c d) := by
  exact support_smul
    ((((QuaternionSupported.coordinate ha).mul (QuaternionSupported.coordinate hb)).mul
      (QuaternionSupported.coordinate hc).conj).mul (QuaternionSupported.coordinate hd).conj).scalar 2

/-- No unit-polynomial padding issue occurs in this degree-one character. -/
theorem lift_plaquette (n a b c d : Nat) :
    liftBoundary n (plaquette a b c d) = plaquette (n+a) (n+b) (n+c) (n+d) := by
  change liftBoundary n (polySmul 2 _) = polySmul 2 _
  rw [lift_smul]
  change polySmul 2 (liftQuaternion n (PolyQuaternion.mul
    (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.coordinateVariable a)
      (PolyQuaternion.coordinateVariable b)) (PolyQuaternion.conj (PolyQuaternion.coordinateVariable c)))
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable d)))).scalar = _
  simp only [liftQuaternion_mul, liftQuaternion_conj, liftQuaternion_coordinateVariable]

private theorem coordinate_step {n i : Nat} (hi : i < n) (w : Q') (K : Nat) (hK : 1 ≤ K) :
    QuaternionPropagates (n+n) i (n+i) w K
      (PolyQuaternion.coordinateVariable i) (PolyQuaternion.coordinateVariable (n+i)) := by
  have he : n+n = (n+n-1)+1 := by omega
  rw [he]
  exact QuaternionPropagates.coordinate (n+n-1) (by omega)
    ⟨i, by omega⟩ ⟨n+i, by omega⟩ (by change i ≠ n+i; omega) w K hK

private theorem coordinate_independent (i j : Nat) (h : i ≠ j) :
    HasPolyQuaternionBlockDegree i 0 (PolyQuaternion.coordinateVariable j) := by
  have hd := hasPolyQuaternionBlockDegree_coordinateVariable j i
  rw [if_neg h] at hd
  exact hd

/-- A single selected factor, with the complete remaining kinetic product.
Only the original lower coordinate is integrated at this step. -/
private theorem remove_selected (n : Nat) (w : Q') (K i : Nat) (ids : List Nat)
    (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    {p q : RatPoly} (hp : Propagates (n+n) i (n+i) w K p q)
    (g : RatPoly) (hg : SupportedQuaternionBlocks n g) :
    quaternionHaar (n+n) (polyMul (productHeat n w K (i::ids)) (polyMul p (liftBoundary n g))) ≈
      qpow w 3 * quaternionHaar (n+n)
        (polyMul (productHeat n w K ids) (polyMul q (liftBoundary n g))) := by
  have hs := supported_polyMul (productHeat_supported n w K ids hids) (lift_supported hg n)
  have hd := (independent_has_degree_zero (productHeat_independent_lower n w K ids hids i hi hnot)).mul
    (independent_has_degree_zero (lift_lower_independent n g i hi))
  have h := hp.pairing _ hs hd
  have rearrange (s : RatPoly) : RatPolyCoeffEqv
      (polyMul (productHeat n w K ids) (polyMul s (liftBoundary n g)))
      (polyMul s (polyMul (productHeat n w K ids) (liftBoundary n g))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => productHeat n w K ids | 1 => s | _ => liftBoundary n g)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.mul_assoc _ _ _).trans ((rearrange p).mul_left _)))
    (Q'.eqv_trans _ _ _ h
      (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (rearrange q).symm)))

private theorem four_factors (w z : Q') :
    qpow w 3 * (qpow w 3 * (qpow w 3 * (qpow w 3 * z))) ≈ qpow w 12 * z :=
  poly_identity_of_normal_eq
    (.mul (.pow (.var 0) 3) (.mul (.pow (.var 0) 3)
      (.mul (.pow (.var 0) 3) (.mul (.pow (.var 0) 3) (.var 1)))))
    (.mul (.pow (.var 0) 12) (.var 1)) (by decide) (fun | 0 => w | _ => z)

/-- All packet spins and all unselected factors are retained, then integrated
by their actual marginal. The final test g is arbitrary and may be interacting. -/
theorem selected_pairing (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (a b c d : Nat) (ids : List Nat) (hn : (a::b::c::d::ids).Nodup)
    (hids : ∀ i, i ∈ a::b::c::d::ids → i < n)
    (g : RatPoly) (hg : SupportedQuaternionBlocks n g) :
    quaternionHaar n (polyMul g (productMap n w K (a::b::c::d::ids) (plaquette a b c d))) ≈
      qpow w 12 * quaternionHaar n (polyMul g (plaquette a b c d)) := by
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
  let C := PolyQuaternion.coordinateVariable
  have s (j : Nat) (hj : j < n+n) : QuaternionSupported (n+n) (C j) :=
    QuaternionSupported.coordinate hj
  have z (i j : Nat) (hij : i ≠ j) : HasPolyQuaternionBlockDegree i 0 (C j) :=
    coordinate_independent i j hij
  have p0 : Propagates (n+n) a (n+a) w K (plaquette a b c d) (plaquette (n+a) b c d) :=
    ((((coordinate_step ha w K hK).mul_right (C b) (s b (by omega)) (z a b hab)).mul_right
      (PolyQuaternion.conj (C c)) (s c (by omega)).conj (z a c hac).conj).mul_right
      (PolyQuaternion.conj (C d)) (s d (by omega)).conj (z a d had).conj).scalar.smul 2
  have p1 : Propagates (n+n) b (n+b) w K (plaquette (n+a) b c d) (plaquette (n+a) (n+b) c d) :=
    ((((coordinate_step hb w K hK).mul_left (C (n+a)) (s (n+a) (by omega)) (z b (n+a) (by omega))).mul_right
      (PolyQuaternion.conj (C c)) (s c (by omega)).conj (z b c hbc).conj).mul_right
      (PolyQuaternion.conj (C d)) (s d (by omega)).conj (z b d hbd).conj).scalar.smul 2
  have p2 : Propagates (n+n) c (n+c) w K (plaquette (n+a) (n+b) c d) (plaquette (n+a) (n+b) (n+c) d) :=
    (((coordinate_step hc w K hK).conj.mul_left (PolyQuaternion.mul (C (n+a)) (C (n+b)))
      ((s (n+a) (by omega)).mul (s (n+b) (by omega)))
      ((z c (n+a) (by omega)).mul (z c (n+b) (by omega)))).mul_right
      (PolyQuaternion.conj (C d)) (s d (by omega)).conj (z c d hcd).conj).scalar.smul 2
  have p3 : Propagates (n+n) d (n+d) w K (plaquette (n+a) (n+b) (n+c) d) (plaquette (n+a) (n+b) (n+c) (n+d)) :=
    ((coordinate_step hd w K hK).conj.mul_left
      (PolyQuaternion.mul (PolyQuaternion.mul (C (n+a)) (C (n+b))) (PolyQuaternion.conj (C (n+c))))
      (((s (n+a) (by omega)).mul (s (n+b) (by omega))).mul (s (n+c) (by omega)).conj)
      (((z d (n+a) (by omega)).mul (z d (n+b) (by omega))).mul (z d (n+c) (by omega)).conj)).scalar.smul 2
  have h0 := remove_selected n w K a (b::c::d::ids) ha hna.1
    (fun i hi => hids i (List.mem_cons_of_mem a hi)) p0 g hg
  have h1 := remove_selected n w K b (c::d::ids) hb hnb.1
    (fun i hi => hids i (List.mem_cons_of_mem a (List.mem_cons_of_mem b hi))) p1 g hg
  have h2 := remove_selected n w K c (d::ids) hc hnc.1
    (fun i hi => hids i (List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_of_mem c hi)))) p2 g hg
  have h3 := remove_selected n w K d ids hd hnd.1
    (fun i hi => hids i (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hi))))) p3 g hg
  have htail : quaternionHaar (n+n) (polyMul (productHeat n w K ids)
      (polyMul (plaquette (n+a) (n+b) (n+c) (n+d)) (liftBoundary n g))) ≈
      quaternionHaar n (polyMul g (plaquette a b c d)) := by
    rw [← lift_plaquette, ← lift_product]
    exact Q'.eqv_trans _ _ _ (productHeat_upper_marginal n w K ids hnd.2
      (fun i hi => hids i (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hi)))))
      _ (supported_polyMul (fourWord_supported ha hb hc hd) hg))
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
  have e3 := Q'.eqv_trans _ _ _ h3 (Q'.mul_eqv_congr_left _ _ _ htail)
  have e2 := Q'.eqv_trans _ _ _ h2 (Q'.mul_eqv_congr_left _ _ _ e3)
  have e1 := Q'.eqv_trans _ _ _ h1 (Q'.mul_eqv_congr_left _ _ _ e2)
  have e0 := Q'.eqv_trans _ _ _ h0 (Q'.mul_eqv_congr_left _ _ _ e1)
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K _ _ g)
    (Q'.eqv_trans _ _ _ e0 (four_factors w _))

/-- Transmit the plaquette while retaining an arbitrary lower-slice spectator
independent of its four selected coordinates. The unselected heat factors
still act on that spectator; this is a supported-Haar identity, not a raw
polynomial eigenidentity. -/
theorem selected_pairing_spectator (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (a b c d : Nat) (ids : List Nat) (hn : (a::b::c::d::ids).Nodup)
    (hids : ∀ i, i ∈ a::b::c::d::ids → i < n)
    (A : RatPoly) (hA : SupportedQuaternionBlocks n A)
    (hAa : QuaternionBlockIndependent a A) (hAb : QuaternionBlockIndependent b A)
    (hAc : QuaternionBlockIndependent c A) (hAd : QuaternionBlockIndependent d A) :
    SupportedHaarEqv n
      (productMap n w K (a::b::c::d::ids) (polyMul (plaquette a b c d) A))
      (polySmul (qpow w 12)
        (polyMul (plaquette a b c d) (productMap n w K ids A))) := by
  intro g hg
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
  have hA2 : SupportedQuaternionBlocks (n+n) A :=
    fun t ht => Nat.le_trans (hA t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right n n))
  let C := PolyQuaternion.coordinateVariable
  have s (j : Nat) (hj : j < n+n) : QuaternionSupported (n+n) (C j) :=
    QuaternionSupported.coordinate hj
  have z (i j : Nat) (hij : i ≠ j) : HasPolyQuaternionBlockDegree i 0 (C j) :=
    coordinate_independent i j hij
  have p0 : Propagates (n+n) a (n+a) w K (plaquette a b c d) (plaquette (n+a) b c d) :=
    ((((coordinate_step ha w K hK).mul_right (C b) (s b (by omega)) (z a b hab)).mul_right
      (PolyQuaternion.conj (C c)) (s c (by omega)).conj (z a c hac).conj).mul_right
      (PolyQuaternion.conj (C d)) (s d (by omega)).conj (z a d had).conj).scalar.smul 2
  have p1 : Propagates (n+n) b (n+b) w K (plaquette (n+a) b c d) (plaquette (n+a) (n+b) c d) :=
    ((((coordinate_step hb w K hK).mul_left (C (n+a)) (s (n+a) (by omega)) (z b (n+a) (by omega))).mul_right
      (PolyQuaternion.conj (C c)) (s c (by omega)).conj (z b c hbc).conj).mul_right
      (PolyQuaternion.conj (C d)) (s d (by omega)).conj (z b d hbd).conj).scalar.smul 2
  have p2 : Propagates (n+n) c (n+c) w K (plaquette (n+a) (n+b) c d) (plaquette (n+a) (n+b) (n+c) d) :=
    (((coordinate_step hc w K hK).conj.mul_left (PolyQuaternion.mul (C (n+a)) (C (n+b)))
      ((s (n+a) (by omega)).mul (s (n+b) (by omega)))
      ((z c (n+a) (by omega)).mul (z c (n+b) (by omega)))).mul_right
      (PolyQuaternion.conj (C d)) (s d (by omega)).conj (z c d hcd).conj).scalar.smul 2
  have p3 : Propagates (n+n) d (n+d) w K (plaquette (n+a) (n+b) (n+c) d) (plaquette (n+a) (n+b) (n+c) (n+d)) :=
    ((coordinate_step hd w K hK).conj.mul_left
      (PolyQuaternion.mul (PolyQuaternion.mul (C (n+a)) (C (n+b))) (PolyQuaternion.conj (C (n+c))))
      (((s (n+a) (by omega)).mul (s (n+b) (by omega))).mul (s (n+c) (by omega)).conj)
      (((z d (n+a) (by omega)).mul (z d (n+b) (by omega))).mul (z d (n+c) (by omega)).conj)).scalar.smul 2
  have h0 := remove_selected n w K a (b::c::d::ids) ha hna.1
    (fun i hi => hids i (List.mem_cons_of_mem a hi))
    (p0.mul_right A hA2 (independent_has_degree_zero hAa)) g hg
  have h1 := remove_selected n w K b (c::d::ids) hb hnb.1
    (fun i hi => hids i (List.mem_cons_of_mem a (List.mem_cons_of_mem b hi)))
    (p1.mul_right A hA2 (independent_has_degree_zero hAb)) g hg
  have h2 := remove_selected n w K c (d::ids) hc hnc.1
    (fun i hi => hids i (List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_of_mem c hi))))
    (p2.mul_right A hA2 (independent_has_degree_zero hAc)) g hg
  have h3 := remove_selected n w K d ids hd hnd.1
    (fun i hi => hids i (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hi)))))
    (p3.mul_right A hA2 (independent_has_degree_zero hAd)) g hg
  have hshape : RatPolyCoeffEqv
      (polyMul (polyMul (plaquette (n+a) (n+b) (n+c) (n+d)) A) (liftBoundary n g))
      (polyMul A (liftBoundary n (polyMul g (plaquette a b c d)))) := by
    rw [lift_product, lift_plaquette]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 2) (.var 0)))
      (by decide)
      (fun | 0 => plaquette (n+a) (n+b) (n+c) (n+d)
           | 1 => A | _ => liftBoundary n g)
  have htail : quaternionHaar (n+n) (polyMul (productHeat n w K ids)
      (polyMul (polyMul (plaquette (n+a) (n+b) (n+c) (n+d)) A) (liftBoundary n g))) ≈
      quaternionHaar n (polyMul (polyMul g (plaquette a b c d))
        (productMap n w K ids A)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (hshape.mul_left _))
      (Q'.eqv_symm (productMap_pairing n w K ids A (polyMul g (plaquette a b c d))))
  have e3 := Q'.eqv_trans _ _ _ h3 (Q'.mul_eqv_congr_left _ _ _ htail)
  have e2 := Q'.eqv_trans _ _ _ h2 (Q'.mul_eqv_congr_left _ _ _ e3)
  have e1 := Q'.eqv_trans _ _ _ h1 (Q'.mul_eqv_congr_left _ _ _ e2)
  have e0 := Q'.eqv_trans _ _ _ h0 (Q'.mul_eqv_congr_left _ _ _ e1)
  have hfinal : quaternionHaar n (polyMul (polyMul g (plaquette a b c d))
      (productMap n w K ids A)) ≈
      quaternionHaar n (polyMul g
        (polyMul (plaquette a b c d) (productMap n w K ids A))) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc g (plaquette a b c d) _)
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K _ _ g)
    (Q'.eqv_trans _ _ _ e0
      (Q'.eqv_trans _ _ _ (four_factors w _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hfinal)
          (Q'.eqv_symm (quaternionHaar_polyMul_smul_right n _ g _)))))

/-- The selected factors also leave an independent spectator unchanged as
an input, under every supported Haar test. -/
private theorem selected_input_removed (n : Nat) (w : Q') (K : Nat)
    (a b c d : Nat) (ids : List Nat) (hn : (a::b::c::d::ids).Nodup)
    (hids : ∀ i, i ∈ a::b::c::d::ids → i < n)
    (A : RatPoly) (hA : SupportedQuaternionBlocks n A)
    (hAa : QuaternionBlockIndependent a A) (hAb : QuaternionBlockIndependent b A)
    (hAc : QuaternionBlockIndependent c A) (hAd : QuaternionBlockIndependent d A) :
    SupportedHaarEqv n (productMap n w K (a::b::c::d::ids) A)
      (productMap n w K ids A) := by
  have hna := List.nodup_cons.mp hn
  have hnb := List.nodup_cons.mp hna.2
  have hnc := List.nodup_cons.mp hnb.2
  have hnd := List.nodup_cons.mp hnc.2
  have ha : a < n := hids a (by simp)
  have hb : b < n := hids b (by simp)
  have hc : c < n := hids c (by simp)
  have hd : d < n := hids d (by simp)
  have h0 := productMap_cons_input_independent n w K a (b::c::d::ids) ha hna.1
    (fun i hi => hids i (List.mem_cons_of_mem a hi)) A hA hAa
  have h1 := productMap_cons_input_independent n w K b (c::d::ids) hb hnb.1
    (fun i hi => hids i (List.mem_cons_of_mem a (List.mem_cons_of_mem b hi))) A hA hAb
  have h2 := productMap_cons_input_independent n w K c (d::ids) hc hnc.1
    (fun i hi => hids i (List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_of_mem c hi)))) A hA hAc
  have h3 := productMap_cons_input_independent n w K d ids hd hnd.1
    (fun i hi => hids i (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hi))))) A hA hAd
  exact h0.trans (h1.trans (h2.trans h3))

/-- Full-output form: the unchanged product heat acts on the spectator,
while the four-link plaquette is transmitted by its exact fundamental mode. -/
theorem selected_pairing_spectator_full (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (a b c d : Nat) (ids : List Nat) (hn : (a::b::c::d::ids).Nodup)
    (hids : ∀ i, i ∈ a::b::c::d::ids → i < n)
    (A : RatPoly) (hA : SupportedQuaternionBlocks n A)
    (hAa : QuaternionBlockIndependent a A) (hAb : QuaternionBlockIndependent b A)
    (hAc : QuaternionBlockIndependent c A) (hAd : QuaternionBlockIndependent d A) :
    SupportedHaarEqv n
      (productMap n w K (a::b::c::d::ids) (polyMul (plaquette a b c d) A))
      (polySmul (qpow w 12)
        (polyMul (plaquette a b c d) (productMap n w K (a::b::c::d::ids) A))) := by
  have hword := selected_pairing_spectator n w K hK a b c d ids hn hids A hA hAa hAb hAc hAd
  have herase := selected_input_removed n w K a b c d ids hn hids A hA hAa hAb hAc hAd
  have hmul : SupportedHaarEqv n
      (polyMul (plaquette a b c d) (productMap n w K ids A))
      (polyMul (plaquette a b c d) (productMap n w K (a::b::c::d::ids) A)) :=
    (SupportedHaarEqv.refl n (plaquette a b c d)).mul herase.symm
      (productMap_supported n w K ids (fun i hi => hids i
        (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hi))))) hA)
      (fourWord_supported (hids a (by simp)) (hids b (by simp))
        (hids c (by simp)) (hids d (by simp)))
  exact hword.trans (hmul.smul (qpow w 12))

/-- A literal finite permutation suffices to put the four physical links first. -/
theorem productMap_plaquette_of_perm (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (a b c d : Nat) (ids rest : List Nat) (hn : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) (hp : ids.Perm (a::b::c::d::rest)) :
    SupportedHaarEqv n (productMap n w K ids (plaquette a b c d))
      (polySmul (qpow w 12) (plaquette a b c d)) := by
  intro g hg
  have hchange := haar_of_coeff (blocks := n+n)
    ((polynomialProduct_perm (fun i => heatAt i (n+i) w K) hp).mul_right
      (polyMul (plaquette a b c d) (liftBoundary n g)))
  have hpair := selected_pairing n w K hK a b c d rest (hp.nodup_iff.mp hn)
    (fun i hi => hids i (hp.mem_iff.mpr hi)) g hg
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K ids _ g)
    (Q'.eqv_trans _ _ _ hchange (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (productMap_pairing n w K (a::b::c::d::rest) _ g))
      (Q'.eqv_trans _ _ _ hpair (Q'.eqv_symm (quaternionHaar_polyMul_smul_right n _ g _)))))

end YMGap.Continuum.SU2QuaternionProductHeatPlaquette

#print axioms YMGap.Continuum.SU2QuaternionProductHeatPlaquette.fourWord_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPlaquette.lift_plaquette
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPlaquette.selected_pairing
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPlaquette.selected_pairing_spectator
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPlaquette.selected_input_removed
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPlaquette.selected_pairing_spectator_full
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPlaquette.productMap_plaquette_of_perm
