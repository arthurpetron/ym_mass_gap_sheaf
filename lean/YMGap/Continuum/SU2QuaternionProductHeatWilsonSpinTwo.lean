/-
# Original product heat of the label-two ordered Wilson word

Selected links are removed in their original quaternion order. The upper
prefix retains its genuine Haar-unit certificate, support and independence;
its identification with the lifted lower prefix is explicitly coefficient
padded. No pointwise unit identity or multiplicativity of the heat map is
used. The conclusion is a bare kinetic image, not an interacting eigenmode.
-/

import YMGap.Continuum.SU2QuaternionProductHeatWilsonWord
import YMGap.Continuum.SU2QuaternionSpinTwoWordStep
import YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare

namespace YMGap.Continuum.SU2QuaternionProductHeatWilsonSpinTwo

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
  (orientedCoordinateQuaternion orientedCoordinateQuaternion_blockDegree)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare (first_character_square)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex select_perm)
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWordLift
open YMGap.Continuum.QuaternionHaarWordDifference (word_unit)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt word_independent)
open YMGap.Continuum.SU2QuaternionSpinTwoWordStep

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul

private theorem one_supported (n : Nat) : QuaternionSupported n PolyQuaternion.one :=
  ⟨supported_one n, (fun _ h => False.elim (List.not_mem_nil h)),
    (fun _ h => False.elim (List.not_mem_nil h)),
    (fun _ h => False.elim (List.not_mem_nil h))⟩

private theorem one_independent (i : Nat) : HasPolyQuaternionBlockDegree i 0 PolyQuaternion.one :=
  ⟨hasQuaternionBlockDegree_one i, hasQuaternionBlockDegree_zero i 0,
    hasQuaternionBlockDegree_zero i 0, hasQuaternionBlockDegree_zero i 0⟩

private theorem letter_supported {n i : Nat} (hi : i < n) (reverse : Bool) :
    QuaternionSupported n (orientedCoordinateQuaternion i reverse) := by
  cases reverse
  · exact QuaternionSupported.coordinate hi
  · exact (QuaternionSupported.coordinate hi).conj

private theorem letter_unit {n i : Nat} (hi : i < n) (reverse : Bool) :
    HaarCarrierEqv n (polyQuaternionNorm (orientedCoordinateQuaternion i reverse)) polyOne := by
  cases reverse
  · exact haarNorm_coordinate hi
  · exact (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)).trans (haarNorm_coordinate hi)

private theorem word_supported (n : Nat) (block : OrientedBF4Link → Nat) :
    ∀ es, (∀ e, e ∈ es → block e < n) → QuaternionSupported n (wordAt block es)
  | [], _ => one_supported n
  | e::es, h => (letter_supported (h e List.mem_cons_self) e.reverse).mul
      (word_supported n block es (fun f hf => h f (List.mem_cons_of_mem e hf)))

private theorem lifted_supported {n : Nat} {p : PolyQuaternion} (hp : QuaternionSupported n p) :
    QuaternionSupported (n+n) (liftQuaternion n p) :=
  ⟨lift_supported hp.scalar n, lift_supported hp.iPart n,
    lift_supported hp.jPart n, lift_supported hp.kPart n⟩

private theorem lift_letter (n i : Nat) (reverse : Bool) :
    liftQuaternion n (orientedCoordinateQuaternion i reverse) =
      orientedCoordinateQuaternion (n+i) reverse := by
  cases reverse <;> simp only [orientedCoordinateQuaternion, Bool.false_eq_true,
    if_false, if_true, liftQuaternion_conj, liftQuaternion_coordinateVariable]

private theorem swap (d f g : RatPoly) :
    RatPolyCoeffEqv (polyMul d (polyMul f g)) (polyMul (polyMul d g) f) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
    (fun | 0 => d | 1 => f | _ => g)

private theorem padded_pairing {n : Nat} {f h : RatPoly}
    (he : PaddedPolynomialCoeffEqv (n+n) f h)
    (hf : SupportedQuaternionBlocks (n+n) f) (hh : SupportedQuaternionBlocks (n+n) h)
    (d g : RatPoly) (hd : SupportedQuaternionBlocks (n+n) d)
    (hg : SupportedQuaternionBlocks (n+n) g) :
    quaternionHaar (n+n) (polyMul d (polyMul f g)) ≈
      quaternionHaar (n+n) (polyMul d (polyMul h g)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (swap d f g))
    (Q'.eqv_trans _ _ _ (he.haar_insert hf hh (polyMul d g) (supported_polyMul hd hg))
      (haar_of_coeff (swap d h g).symm))

private theorem rate_step (w z : Q') (k : Nat) :
    qpow w 8 * (qpow w (8*k)*z) ≈ qpow w (8*(k+1))*z := by
  rw [show 8*(k+1) = 8+8*k by omega]
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (qpow_add w 8 (8*k))))

private theorem remove_pairing (blocks : Nat) (mu d f h g : RatPoly) (a : Q')
    (hstep : quaternionHaar blocks (polyMul (polyMul mu f) (polyMul d g)) ≈
      a * quaternionHaar blocks (polyMul h (polyMul d g))) :
    quaternionHaar blocks (polyMul (polyMul mu d) (polyMul f g)) ≈
      a * quaternionHaar blocks (polyMul d (polyMul h g)) := by
  have hl : RatPolyCoeffEqv (polyMul (polyMul mu d) (polyMul f g))
      (polyMul (polyMul mu f) (polyMul d g)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
      (fun | 0 => mu | 1 => d | 2 => f | _ => g)
  have hr : RatPolyCoeffEqv (polyMul h (polyMul d g)) (polyMul d (polyMul h g)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => h | 1 => d | _ => g)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hl)
    (Q'.eqv_trans _ _ _ hstep (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff hr)))

/-- Removal with a genuinely unit upper prefix and its explicit lower pin.
Every remaining original heat factor and supported final insertion survives. -/
theorem pairing_with_prefix (n : Nat) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (p u : PolyQuaternion) (hp : QuaternionSupported n p)
    (hu : QuaternionSupported (n+n) u)
    (hdu : ∀ i, i < n → HasPolyQuaternionBlockDegree i 0 u)
    (hunit : HaarCarrierEqv (n+n) (polyQuaternionNorm u) polyOne)
    (hpin : PaddedQuaternionCoeffEqv (n+n) u (liftQuaternion n p))
    (g : RatPoly) (hg : SupportedQuaternionBlocks n g) :
    quaternionHaar (n+n) (polyMul (productHeat n w K ids)
      (polyMul (characterPolynomial (u ⋄ wordAt block es).scalar 2) (liftBoundary n g))) ≈
      qpow w (8*es.length) * quaternionHaar n
        (polyMul g (characterPolynomial (p ⋄ wordAt block es).scalar 2)) := by
  induction es generalizing ids p u with
  | nil =>
      have hc := haar_of_coeff (blocks := n+n)
        (((characterPolynomial_coeffEqv (PolyQuaternionCoeffEqv.mul_one u).scalar 2).mul_right
          (liftBoundary n g)).mul_left (productHeat n w K ids))
      have hps : PaddedPolynomialCoeffEqv (n+n) u.scalar (liftBoundary n p.scalar) := hpin.scalar
      have hch := (hps.character 2).trans (lift_character (n+n) n p.scalar 2).symm
      have he := padded_pairing hch (character_supported hu.scalar 2)
        (lift_supported (character_supported hp.scalar 2) n)
        (productHeat n w K ids) (liftBoundary n g)
        (productHeat_supported n w K ids hids) (lift_supported hg n)
      have hm := productHeat_upper_marginal n w K ids hnd hids
        (polyMul (characterPolynomial p.scalar 2) g)
        (supported_polyMul (character_supported hp.scalar 2) hg)
      rw [lift_product] at hm
      have ht := haar_of_coeff (blocks := n)
        ((RatPolyCoeffEqv.mul_comm _ g).trans
          ((characterPolynomial_coeffEqv (PolyQuaternionCoeffEqv.mul_one p).scalar.symm 2).mul_left g))
      exact Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ hm
        (Q'.eqv_trans _ _ _ ht (Q'.eqv_symm (Q'.one_mul_eqv _)))))
  | cons e es ih =>
      have hmap := List.nodup_cons.mp hword
      let i := block e
      let rest := eraseIndex i ids
      have hperm := select_perm i (hselected e List.mem_cons_self)
      have hnrest := List.nodup_cons.mp (hperm.nodup_iff.mp hnd)
      have hrest : ∀ j, j ∈ rest → j < n :=
        fun j hj => hids j (hperm.mem_iff.mpr (List.mem_cons_of_mem i hj))
      have hi : i < n := hids i (hselected e List.mem_cons_self)
      have htail : ∀ f, f ∈ es → block f ∈ rest := by
        intro f hf
        have hm := List.mem_cons.mp (hperm.mem_iff.mp (hselected f (List.mem_cons_of_mem e hf)))
        exact hm.elim (fun he => False.elim (hmap.1 (List.mem_map.mpr ⟨f,hf,he⟩))) id
      have htailIndex : ∀ f, f ∈ es → block f < n+n :=
        fun f hf => Nat.lt_of_lt_of_le (hrest _ (htail f hf)) (Nat.le_add_right n n)
      have hs := word_supported (n+n) block es htailIndex
      have hd := word_independent i block es
        (fun f hf he => hmap.1 (List.mem_map.mpr ⟨f,hf,he.symm⟩))
      have hnorm : HaarCarrierEqv (n+n) (polyQuaternionNorm (wordAt block es)) polyOne :=
        word_unit (fun f => orientedCoordinateQuaternion (block f) f.reverse) es
          (fun f hf => letter_unit (htailIndex f hf) f.reverse)
      let c := orientedCoordinateQuaternion i e.reverse
      let v := orientedCoordinateQuaternion (n+i) e.reverse
      have hv := letter_supported (show n+i < n+n by omega) e.reverse
      have hp' := hp.mul (letter_supported hi e.reverse)
      have hu' := hu.mul hv
      have hdu' : ∀ j, j < n → HasPolyQuaternionBlockDegree j 0 (u ⋄ v) := by
        intro j hj
        have hc := orientedCoordinateQuaternion_blockDegree (n+i) j e.reverse
        rw [if_neg (show j ≠ n+i by omega)] at hc
        exact (hdu j hj).mul hc
      have hunit' := haarNorm_mul hunit (letter_unit (show n+i < n+n by omega) e.reverse)
      have hpin' : PaddedQuaternionCoeffEqv (n+n) (u ⋄ v) (liftQuaternion n (p ⋄ c)) := by
        rw [liftQuaternion_mul, show liftQuaternion n c = v from lift_letter n i e.reverse]
        exact hpin.mul (PaddedQuaternionCoeffEqv.refl _ _)
      let r := polyMul (productHeat n w K rest) (liftBoundary n g)
      have hr := supported_polyMul (productHeat_supported n w K rest hrest) (lift_supported hg n)
      have hdr := (independent_has_degree_zero
          (productHeat_independent_lower n w K rest hrest i hi hnrest.1)).mul
        (independent_has_degree_zero (lift_lower_independent n g i hi))
      have hstep : quaternionHaar (n+n)
          (polyMul (polyMul (heatAt i (n+i) w K)
            (characterPolynomial (u ⋄ (c ⋄ wordAt block es)).scalar 2)) r) ≈
          qpow w 8 * quaternionHaar (n+n)
            (polyMul (characterPolynomial (u ⋄ (v ⋄ wordAt block es)).scalar 2) r) := by
        have he : n+n = (n+n-1)+1 := by omega
        rw [he] at hu hs hunit hnorm hr ⊢
        exact spinTwo_word_step (n+n-1) (by omega) ⟨i, by omega⟩ ⟨n+i, by omega⟩
          (by change i ≠ n+i; omega) w K hK u (wordAt block es)
          hu (hdu i hi) hunit hs hd hnorm e.reverse r hr hdr
      have hout := characterPolynomial_coeffEqv
        (PolyQuaternionCoeffEqv.mul_assoc u v (wordAt block es)).scalar.symm 2
      have hstep' := Q'.eqv_trans _ _ _ hstep
        (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (hout.mul_right r)))
      have hremove := remove_pairing (n+n) (heatAt i (n+i) w K)
        (productHeat n w K rest)
        (characterPolynomial (u ⋄ (c ⋄ wordAt block es)).scalar 2)
        (characterPolynomial ((u ⋄ v) ⋄ wordAt block es).scalar 2)
        (liftBoundary n g) (qpow w 8) hstep'
      have hchange := haar_of_coeff (blocks := n+n)
        ((polynomialProduct_perm (fun j => heatAt j (n+j) w K) hperm).mul_right
          (polyMul (characterPolynomial (u ⋄ wordAt block (e::es)).scalar 2) (liftBoundary n g)))
      have hrec := ih rest hnrest.2 hrest hmap.2 htail (p ⋄ c) (u ⋄ v) hp' hu' hdu' hunit' hpin'
      have hfinal := haar_of_coeff (blocks := n)
        ((characterPolynomial_coeffEqv (PolyQuaternionCoeffEqv.mul_assoc p c (wordAt block es)).scalar 2).mul_left g)
      exact Q'.eqv_trans _ _ _ hchange (Q'.eqv_trans _ _ _ hremove
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hrec)
          (Q'.eqv_trans _ _ _ (rate_step w _ es.length) (Q'.mul_eqv_congr_left _ _ _ hfinal))))

/-- Label-two transmission on the original supported Haar quotient. -/
theorem productMap_spinTwo_word (n : Nat) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids) :
    let f := characterPolynomial (wordAt block es).scalar 2
    SupportedHaarEqv n (productMap n w K ids f) (polySmul (qpow w (8*es.length)) f) := by
  dsimp only
  intro g hg
  have hp := pairing_with_prefix n w K hK block es ids hnd hids hword hselected
    PolyQuaternion.one PolyQuaternion.one (one_supported n) (one_supported (n+n))
    (fun i _ => one_independent i) (RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one)
    (liftQuaternion_one (n+n) n).symm g hg
  have hc := characterPolynomial_coeffEqv (PolyQuaternionCoeffEqv.one_mul (wordAt block es)).scalar 2
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K ids _ g)
    (Q'.eqv_trans _ _ _ (haar_of_coeff ((hc.symm.mul_right (liftBoundary n g)).mul_left _))
      (Q'.eqv_trans _ _ _ hp
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (hc.mul_left g)))
          (Q'.eqv_symm (quaternionHaar_polyMul_smul_right n _ g _)))))

/-- The full square image is vacuum plus the transmitted spin-two channel;
it is NOT obtained by squaring the fundamental heat multiplier. -/
theorem productMap_fundamental_square (n : Nat) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids) :
    let f := characterPolynomial (wordAt block es).scalar 1
    let c := characterPolynomial (wordAt block es).scalar 2
    SupportedHaarEqv n (productMap n w K ids (polyMul f f))
      (polyAdd polyOne (polySmul (qpow w (8*es.length)) c)) := by
  dsimp only
  have h1 := SupportedHaarEqv.of_carrier (blocks := n) (RatPolyCoeffEqv.haarCarrier
    (productMap_congr n w K ids (first_character_square (wordAt block es).scalar)))
  have h2 := SupportedHaarEqv.of_carrier (blocks := n) (RatPolyCoeffEqv.haarCarrier
    (productMap_add n w K ids polyOne (characterPolynomial (wordAt block es).scalar 2)))
  exact h1.trans (h2.trans ((productMap_one n w K ids hnd hids).add
    (productMap_spinTwo_word n w K hK block es ids hnd hids hword hselected)))

#print axioms pairing_with_prefix
#print axioms productMap_spinTwo_word
#print axioms productMap_fundamental_square

end YMGap.Continuum.SU2QuaternionProductHeatWilsonSpinTwo
