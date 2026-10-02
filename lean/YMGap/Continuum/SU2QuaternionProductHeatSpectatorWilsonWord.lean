/-
# Full original product heat with a retained Wilson-word spectator

An insertion independent only of the distinct word blocks retains every
remaining kinetic factor. Its full product-heat image multiplies the exact
fundamental word transmission. This does not assert independence of the
original interacting source or an interacting eigenpin.
-/

import YMGap.Continuum.SU2QuaternionProductHeatWilsonWord
import YMGap.Continuum.SU2QuaternionIndependentTailMoments

namespace YMGap.Continuum.SU2QuaternionProductHeatSpectatorWilsonWord

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionLinearHeatPropagation
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
  (orientedCoordinateQuaternion orientedCoordinateQuaternion_blockDegree)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant (productMap_smul)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex select_perm)
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWordLift

open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt word_independent)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)
open YMGap.Continuum.SU2QuaternionIndependentTailMoments (fundamental_first_moment)

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul

private theorem one_supported (n : Nat) : QuaternionSupported n PolyQuaternion.one :=
  ⟨supported_one n, (fun _ h => False.elim (List.not_mem_nil h)),
    (fun _ h => False.elim (List.not_mem_nil h)),
    (fun _ h => False.elim (List.not_mem_nil h))⟩

private theorem letter_supported {n i : Nat} (hi : i < n) (reverse : Bool) :
    QuaternionSupported n (orientedCoordinateQuaternion i reverse) := by
  cases reverse
  · exact QuaternionSupported.coordinate hi
  · exact (QuaternionSupported.coordinate hi).conj

private theorem word_supported (n : Nat) (block : OrientedBF4Link → Nat) :
    ∀ es, (∀ e, e ∈ es → block e < n) → QuaternionSupported n (wordAt block es)
  | [], _ => one_supported n
  | e::es, h => (letter_supported (h e List.mem_cons_self) e.reverse).mul
      (word_supported n block es (fun f hf => h f (List.mem_cons_of_mem e hf)))

private theorem lifted_supported {n : Nat} {p : PolyQuaternion} (hp : QuaternionSupported n p) :
    QuaternionSupported (n+n) (liftQuaternion n p) :=
  ⟨lift_supported hp.scalar n, lift_supported hp.iPart n,
    lift_supported hp.jPart n, lift_supported hp.kPart n⟩

private theorem lifted_independent (n i : Nat) (hi : i < n) (p : PolyQuaternion) :
    HasPolyQuaternionBlockDegree i 0 (liftQuaternion n p) :=
  ⟨independent_has_degree_zero (lift_lower_independent n p.scalar i hi),
    independent_has_degree_zero (lift_lower_independent n p.iPart i hi),
    independent_has_degree_zero (lift_lower_independent n p.jPart i hi),
    independent_has_degree_zero (lift_lower_independent n p.kPart i hi)⟩

private theorem lift_letter (n i : Nat) (reverse : Bool) :
    liftQuaternion n (orientedCoordinateQuaternion i reverse) =
      orientedCoordinateQuaternion (n+i) reverse := by
  cases reverse <;> simp only [orientedCoordinateQuaternion, Bool.false_eq_true,
    if_false, if_true, liftQuaternion_conj, liftQuaternion_coordinateVariable]

private theorem letter_step {n i : Nat} (hi : i < n) (reverse : Bool)
    (w : Q') (K : Nat) (hK : 1 ≤ K) :
    QuaternionPropagates (n+n) i (n+i) w K
      (orientedCoordinateQuaternion i reverse) (orientedCoordinateQuaternion (n+i) reverse) := by
  have hc : QuaternionPropagates (n+n) i (n+i) w K
      (PolyQuaternion.coordinateVariable i) (PolyQuaternion.coordinateVariable (n+i)) := by
    have he : n+n = (n+n-1)+1 := by omega
    rw [he]
    exact QuaternionPropagates.coordinate (n+n-1) (by omega)
      ⟨i, by omega⟩ ⟨n+i, by omega⟩ (by change i ≠ n+i; omega) w K hK
  cases reverse
  · exact hc
  · exact hc.conj

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

private theorem rate_step (w z : Q') (k : Nat) :
    qpow w 3 * (qpow w (3*k)*z) ≈ qpow w (3*(k+1))*z := by
  rw [show 3*(k+1) = 3+3*k by omega]
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (qpow_add w 3 (3*k))))


private theorem map_perm (n : Nat) (w : Q') (K : Nat)
    {ids rest : List Nat} (hp : ids.Perm rest) (R : RatPoly) :
    RatPolyCoeffEqv (productMap n w K ids R) (productMap n w K rest R) :=
  partialHaarHeads_congr n
    ((polynomialProduct_perm (fun i => heatAt i (n+i) w K) hp).mul_right R)

/-- The lower spectator is retained through every selected-letter removal.
The heat image on the right is the SAME full selected product map. -/
theorem pairing_with_prefix_spectator (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (R : RatPoly) (hR : SupportedQuaternionBlocks n R)
    (hRI : ∀ e, e ∈ es → QuaternionBlockIndependent (block e) R)
    (p : PolyQuaternion) (hp : QuaternionSupported n p)
    (g : RatPoly) (hg : SupportedQuaternionBlocks n g) :
    quaternionHaar (n+n) (polyMul (productHeat n w K ids)
      (polyMul (polyMul (liftQuaternion n p ⋄ wordAt block es).scalar R)
        (liftBoundary n g))) ≈
      qpow w (3*es.length) * quaternionHaar n
        (polyMul (polyMul g (p ⋄ wordAt block es).scalar)
          (productMap n w K ids R)) := by
  have hR2 : SupportedQuaternionBlocks (n+n) R :=
    fun t ht => Nat.le_trans (hR t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right n n))
  induction es generalizing ids p with
  | nil =>
      have hc : RatPolyCoeffEqv
          (polyMul (polyMul (liftQuaternion n p ⋄ wordAt block []).scalar R)
            (liftBoundary n g))
          (polyMul R (liftBoundary n (polyMul g p.scalar))) := by
        change RatPolyCoeffEqv
          (polyMul (polyMul (liftQuaternion n p ⋄ PolyQuaternion.one).scalar R)
            (liftBoundary n g)) _
        rw [lift_product]
        exact (((PolyQuaternionCoeffEqv.mul_one (liftQuaternion n p)).scalar.mul_right R).mul_right
          (liftBoundary n g)).trans
          (coeffEvalExpr_eqv_of_normalize_eq
            (.mul (.mul (.var 0) (.var 1)) (.var 2))
            (.mul (.var 1) (.mul (.var 2) (.var 0))) (by decide)
            (fun | 0 => (liftQuaternion n p).scalar | 1 => R | _ => liftBoundary n g))
      have hm := Q'.eqv_symm (productMap_pairing n w K ids R (polyMul g p.scalar))
      have ht := haar_of_coeff (blocks := n)
        (((PolyQuaternionCoeffEqv.mul_one p).scalar.symm.mul_left g).mul_right
          (productMap n w K ids R))
      exact Q'.eqv_trans _ _ _ (haar_of_coeff (hc.mul_left _))
        (Q'.eqv_trans _ _ _ hm
          (Q'.eqv_trans _ _ _ ht (Q'.eqv_symm (Q'.one_mul_eqv _))))
  | cons e es ih =>
      have hmap := List.nodup_cons.mp hword
      let i := block e
      let rest := eraseIndex i ids
      have hperm := select_perm i (hselected e List.mem_cons_self)
      have hnrest := List.nodup_cons.mp (hperm.nodup_iff.mp hnd)
      have hrest : ∀ j, j ∈ rest → j < n :=
        fun j hj => hids j (hperm.mem_iff.mpr (List.mem_cons_of_mem i hj))
      have hi : i < n := hids i (hselected e List.mem_cons_self)
      have htail : ∀ d, d ∈ es → block d ∈ rest := by
        intro d hd
        have hm := List.mem_cons.mp (hperm.mem_iff.mp (hselected d (List.mem_cons_of_mem e hd)))
        exact hm.elim (fun he => False.elim (hmap.1 (List.mem_map.mpr ⟨d,hd,he⟩))) id
      have hs := word_supported (n+n) block es
        (fun d hd => Nat.lt_of_lt_of_le (hrest _ (htail d hd)) (Nat.le_add_right n n))
      have hd := word_independent i block es
        (fun d hd he => hmap.1 (List.mem_map.mpr ⟨d,hd,he.symm⟩))
      let c := orientedCoordinateQuaternion i e.reverse
      have hp' : QuaternionSupported n (p ⋄ c) := hp.mul (letter_supported hi e.reverse)
      have hout : RatPolyCoeffEqv
          (liftQuaternion n p ⋄ (orientedCoordinateQuaternion (n+i) e.reverse ⋄ wordAt block es)).scalar
          (liftQuaternion n (p ⋄ c) ⋄ wordAt block es).scalar := by
        rw [liftQuaternion_mul, show liftQuaternion n c = orientedCoordinateQuaternion (n+i) e.reverse
          from lift_letter n i e.reverse]
        exact (PolyQuaternionCoeffEqv.mul_assoc _ _ _).scalar.symm
      have step := ((letter_step hi e.reverse w K hK).mul_right (wordAt block es) hs hd).mul_left
        (liftQuaternion n p) (lifted_supported hp) (lifted_independent n i hi p)
      have hprop := (Propagates.recode (RatPolyCoeffEqv.refl _) hout step.scalar).mul_right
        R hR2 (independent_has_degree_zero (hRI e List.mem_cons_self))
      have hremove := remove_selected n w K i rest hi hnrest.1 hrest hprop g hg
      have hchange := haar_of_coeff (blocks := n+n)
        ((polynomialProduct_perm (fun j => heatAt j (n+j) w K) hperm).mul_right
          (polyMul (polyMul (liftQuaternion n p ⋄ wordAt block (e::es)).scalar R)
            (liftBoundary n g)))
      have hrec := ih rest hnrest.2 hrest hmap.2 htail
        (fun d hd => hRI d (List.mem_cons_of_mem e hd)) (p ⋄ c) hp'
      have herase : SupportedHaarEqv n (productMap n w K ids R) (productMap n w K rest R) :=
        (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier (map_perm n w K hperm R))).trans
          (productMap_cons_input_independent n w K i rest hi hnrest.1 hrest R hR
            (hRI e List.mem_cons_self))
      have hfull := herase.symm
        (polyMul g (p ⋄ wordAt block (e::es)).scalar)
        (supported_polyMul hg (hp.mul (word_supported n block (e::es)
          (fun d hd => hids _ (hselected d hd)))).scalar)
      have hshape := haar_of_coeff (blocks := n)
        (((PolyQuaternionCoeffEqv.mul_assoc p c (wordAt block es)).scalar.mul_left g).mul_right
          (productMap n w K rest R))
      have hfinal := Q'.eqv_trans _ _ _ hshape hfull
      exact Q'.eqv_trans _ _ _ hchange
        (Q'.eqv_trans _ _ _ hremove
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hrec)
            (Q'.eqv_trans _ _ _ (rate_step w _ es.length)
              (Q'.mul_eqv_congr_left _ _ _ hfinal))))

/-- Scalar word transmission with the complete transformed spectator. -/
theorem productMap_word_scalar_spectator (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (R : RatPoly) (hR : SupportedQuaternionBlocks n R)
    (hRI : ∀ e, e ∈ es → QuaternionBlockIndependent (block e) R) :
    SupportedHaarEqv n (productMap n w K ids (polyMul R (wordAt block es).scalar))
      (polySmul (qpow w (3*es.length))
        (polyMul (productMap n w K ids R) (wordAt block es).scalar)) := by
  intro g hg
  have hw2 := word_supported (n+n) block es
    (fun e he => Nat.lt_of_lt_of_le (hids _ (hselected e he)) (Nat.le_add_right n n))
  have hR2 : SupportedQuaternionBlocks (n+n) R :=
    fun t ht => Nat.le_trans (hR t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right n n))
  have hu := ((liftQuaternion_one (n+n) n).mul
      (PaddedQuaternionCoeffEqv.refl (n+n) (wordAt block es))).trans
    (PaddedQuaternionCoeffEqv.of_coeff (PolyQuaternionCoeffEqv.one_mul _))
  have hweighted := PaddedPolynomialCoeffEqv.haar_insert (blocks := n+n)
    (p := (liftQuaternion n PolyQuaternion.one ⋄ wordAt block es).scalar)
    (q := (wordAt block es).scalar) hu.scalar
    ((lifted_supported (one_supported n)).mul hw2).scalar hw2.scalar
    (polyMul (productHeat n w K ids) (polyMul R (liftBoundary n g)))
    (supported_polyMul (productHeat_supported n w K ids hids)
      (supported_polyMul hR2 (lift_supported hg n)))
  have swap (s : RatPoly) : RatPolyCoeffEqv
      (polyMul (productHeat n w K ids) (polyMul (polyMul s R) (liftBoundary n g)))
      (polyMul (polyMul (productHeat n w K ids) (polyMul R (liftBoundary n g))) s) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.mul (.var 0) (.mul (.var 2) (.var 3))) (.var 1)) (by decide)
      (fun | 0 => productHeat n w K ids | 1 => s | 2 => R | _ => liftBoundary n g)
  have hleft := Q'.eqv_trans _ _ _ (haar_of_coeff
    (((RatPolyCoeffEqv.mul_comm R (wordAt block es).scalar).mul_right
      (liftBoundary n g)).mul_left (productHeat n w K ids)))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (swap _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hweighted) (haar_of_coeff (swap _).symm)))
  have hp := pairing_with_prefix_spectator n w K hK block es ids hnd hids hword hselected
    R hR hRI PolyQuaternion.one (one_supported n) g hg
  have hright := haar_of_coeff (blocks := n)
    ((((PolyQuaternionCoeffEqv.one_mul (wordAt block es)).scalar.mul_left g).mul_right
      (productMap n w K ids R)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
        (fun | 0 => g | 1 => (wordAt block es).scalar | _ => productMap n w K ids R)))
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K ids _ g)
    (Q'.eqv_trans _ _ _ hleft (Q'.eqv_trans _ _ _ hp
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hright)
        (Q'.eqv_symm (quaternionHaar_polyMul_smul_right n _ g _)))))

/-- Fundamental transmission, independent only on the word blocks. The
spectator heat on the right is not replaced by a constant or a partial map. -/
theorem productMap_fundamental_word_spectator (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (R : RatPoly) (hR : SupportedQuaternionBlocks n R)
    (hRI : ∀ e, e ∈ es → QuaternionBlockIndependent (block e) R) :
    let f := characterPolynomial (wordAt block es).scalar 1
    SupportedHaarEqv n (productMap n w K ids (polyMul R f))
      (polySmul (qpow w (3*es.length)) (polyMul (productMap n w K ids R) f)) := by
  dsimp only
  have hs := productMap_word_scalar_spectator n w K hK block es ids hnd hids hword hselected R hR hRI
  have hl := (productMap_congr n w K ids
    (RatPolyCoeffEqv.polyMul_smul_right 2 R (wordAt block es).scalar)).trans
      (productMap_smul n w K ids 2 (polyMul R (wordAt block es).scalar))
  have hr : RatPolyCoeffEqv
      (polySmul 2 (polySmul (qpow w (3*es.length))
        (polyMul (productMap n w K ids R) (wordAt block es).scalar)))
      (polySmul (qpow w (3*es.length))
        (polyMul (productMap n w K ids R) (polySmul 2 (wordAt block es).scalar))) := by
    let a := qpow w (3*es.length)
    let s := polyMul (productMap n w K ids R) (wordAt block es).scalar
    have hswap : RatPolyCoeffEqv (polySmul 2 (polySmul a s)) (polySmul a (polySmul 2 s)) := by
      intro weight
      exact Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight 2 _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (ratWeightedSum_smul weight a s))
          (Q'.eqv_trans _ _ _
            (poly_identity_of_normal_eq (.mul (.const 2) (.mul (.var 0) (.var 1)))
              (.mul (.var 0) (.mul (.const 2) (.var 1))) (by decide)
              (fun | 0 => a | _ => ratWeightedSum weight s))
            (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (ratWeightedSum_smul weight 2 s)))
              (Q'.eqv_symm (ratWeightedSum_smul weight a _)))))
    exact hswap.trans ((RatPolyCoeffEqv.polyMul_smul_right 2
      (productMap n w K ids R) (wordAt block es).scalar).symm.smul a)
  exact (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hl)).trans
    ((hs.smul 2).trans (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hr)))

/-- One forward exposed word edge annihilates the first moment against an
arbitrary independent insertion. No positivity or heat cutoff is needed. -/
theorem fundamental_word_first_moment (n : Nat)
    (block : OrientedBF4Link → Nat) (e : OrientedBF4Link) (es : List OrientedBF4Link)
    (he : block e < n) (hforward : e.reverse = false)
    (habsent : ∀ d, d ∈ es → block e ≠ block d)
    (r : RatPoly) (hr : QuaternionBlockIndependent (block e) r) :
    quaternionHaar n (polyMul
      (characterPolynomial (wordAt block (e::es)).scalar 1) r) ≈ 0 := by
  have htail := word_independent (block e) block es habsent
  have h := fundamental_first_moment n (block e) he (wordAt block es) r htail hr
  simpa only [wordAt, wordWith, hforward, orientedCoordinateQuaternion,
    Bool.false_eq_true, if_false] using h

#print axioms pairing_with_prefix_spectator
#print axioms productMap_word_scalar_spectator
#print axioms productMap_fundamental_word_spectator
#print axioms fundamental_word_first_moment

end YMGap.Continuum.SU2QuaternionProductHeatSpectatorWilsonWord
