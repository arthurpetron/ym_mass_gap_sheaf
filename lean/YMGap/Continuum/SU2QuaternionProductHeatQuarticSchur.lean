/-
# Signed quartic Schur bound with the ENTIRE original product heat retained

The selected quartic factor and every other distinct selected heat factor
have computed constant marginals on the original doubled carrier. The endpoint
may depend on every lower coordinate, including spectators and inactive links.
The bound costs the raw Haar source square, not interacting OWN variance.
-/

import YMGap.Continuum.SU2QuaternionHeatQuarticSchur

namespace YMGap.Continuum.SU2QuaternionProductHeatQuarticSchur

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum finSum_eqv_congr)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial PolyQuaternion)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatVacuum
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum (pair_vacuum)
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionProductHeatPositive (insertion)
open YMGap.Continuum.SU2QuaternionHeatQuarticExpansion (defect)
open YMGap.Continuum.SU2QuaternionHeatQuarticMoment (response quartic_value_regrouped)
open YMGap.Continuum.SU2HeatQuarticFiniteRegroup (quarticCoeff cutCoeff)
open YMGap.Continuum.SU2HeatQuarticLowCoefficients (zeroCoeff zeroCoeff_le_sixty)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMomentDefect (rawSourceMoment)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (haar_liftBoundary)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem support_lower {n : Nat} {f : RatPoly} (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks (n+n) f :=
  fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (by omega))

private theorem support_neg {n : Nat} {f : RatPoly} (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks n (polyNeg f) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hf s hs

private theorem support_cap (n : Nat) (c : Q') : SupportedQuaternionBlocks n (cap c) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact supported_one n s hs

private theorem deficit_supported {n a b : Nat} (ha : a < n) (hb : b < n) :
    SupportedQuaternionBlocks n (defect (scalarAt a b)) :=
  supported_add (support_cap n 2) (support_neg (character_supported (scalar_supported ha hb) 1))

private def pairQuartic (a b : Nat) (q : Q') (K : Nat) : RatPoly :=
  polyMul (polyMul (defect (scalarAt a b)) (defect (scalarAt a b))) (heatAt a b q K)

private theorem pair_supported {n a b : Nat} (ha : a < n) (hb : b < n) (q : Q') (K : Nat) :
    SupportedQuaternionBlocks n (pairQuartic a b q K) :=
  supported_polyMul (supported_polyMul (deficit_supported ha hb) (deficit_supported ha hb))
    (heat_supported ha hb q K)

/-- Literal selected quartic defect times the complete original selected product. -/
def quarticProduct (n : Nat) (q : Q') (K i : Nat) (ids : List Nat) : RatPoly :=
  polyMul (polyMul (defect (scalarAt i (n+i))) (defect (scalarAt i (n+i))))
    (productHeat n q K (i::ids))

theorem quarticProduct_supported (n : Nat) (q : Q') (K i : Nat) (ids : List Nat)
    (hi : i < n) (hids : ∀ j, j ∈ ids → j < n) :
    SupportedQuaternionBlocks (n+n) (quarticProduct n q K i ids) :=
  supported_polyMul (supported_polyMul (deficit_supported (by omega) (by omega))
    (deficit_supported (by omega) (by omega)))
    (productHeat_supported n q K (i::ids) (fun j hj => (List.mem_cons.mp hj).elim
      (fun he => by subst j; exact hi) (hids j)))

def quarticProduct_certificate (n : Nat) {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K i : Nat) (ids : List Nat) (hK : headCutoff q ≤ K) (hi : i < n)
    (hids : ∀ j, j ∈ ids → j < n) : Certificate (n+n) (quarticProduct n q K i ids) :=
  Certificate.multiplySquare _ (deficit_supported (by omega) (by omega))
    (productHeatCertificate n hq0 hq1 K hK (i::ids) (fun j hj => (List.mem_cons.mp hj).elim
      (fun he => by subst j; exact hi) (hids j)))

private theorem pair_character_vacuum (blocks : Nat) (hb : 1 < blocks)
    (a b : Fin blocks) (hab : a.val ≠ b.val) (j : Nat) (r : RatPoly)
    (hr : SupportedQuaternionBlocks blocks r) (hd : HasQuaternionBlockDegree a.val 0 r) :
    H blocks (polyMul (characterPolynomial (scalarAt a.val b.val) j) r) ≈
      (if j = 0 then H blocks r else 0) := by
  let steps := pairSteps hb a b
  let tr := applyQuaternionBlockSwapChain steps r
  have htr := applyQuaternionBlockSwapChain_supported steps r hr
  have hd0 : HasQuaternionBlockDegree 0 0 tr := by
    apply chain_degree steps (by omega)
    rw [pair_zero hb a b hab]
    exact hd
  have hc : PaddedPolynomialCoeffEqv blocks
      (applyQuaternionBlockSwapChain steps (characterPolynomial (scalarAt a.val b.val) j))
      (relativeCharacter j) :=
    PaddedPolynomialCoeffEqv.of_prefix ((applyQuaternionBlockSwapChain_character_prefix _ _ _).trans
      ((scalar_exposed hb a b hab).character j))
  have hp := supported_polyMul (character_supported (scalar_supported a.isLt b.isLt) j) hr
  have hs := quaternionHaar_applyQuaternionBlockSwapChain steps _ hp
  rw [chain_mul] at hs
  have he : (blocks-1)+1 = blocks := by omega
  have hv := character_vacuum (blocks-1) (by omega) j tr hd0
  rw [he] at hv
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hs) (Q'.eqv_trans _ _ _
    ((hc.mul (PaddedPolynomialCoeffEqv.refl blocks tr)).haar
      (supported_polyMul (applyQuaternionBlockSwapChain_supported steps _ (character_supported (scalar_supported a.isLt b.isLt) j)) htr)
      (supported_polyMul (character_supported (scalar_supported (by omega) (by omega)) j) htr)) ?_)
  exact Q'.eqv_trans _ _ _ hv (by
    by_cases hj : j = 0
    · rw [if_pos hj, if_pos hj]
      exact quaternionHaar_applyQuaternionBlockSwapChain steps r hr
    · rw [if_neg hj, if_neg hj]
      exact Q'.eqv_refl _)

private theorem insertion_one (n : Nat) (W p : RatPoly)
    (hW : SupportedQuaternionBlocks (n+n) W) (hp : SupportedQuaternionBlocks (n+n) p) :
    insertion n W polyOne p ≈ H (n+n) (polyMul p W) := by
  have hpair : PaddedPolynomialCoeffEqv (n+n)
      (polyMul polyOne (liftBoundary n polyOne)) polyOne :=
    ((PaddedPolynomialCoeffEqv.refl _ polyOne).mul (lift_one (n+n) n)).trans
      (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.one_mul polyOne))
  have hinner : PaddedPolynomialCoeffEqv (n+n)
      (polyMul W (polyMul polyOne (liftBoundary n polyOne))) W :=
    ((PaddedPolynomialCoeffEqv.refl _ W).mul hpair).trans
      (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_one W))
  have he : PaddedPolynomialCoeffEqv (n+n)
      (polyMul (polyMul W (polyMul polyOne (liftBoundary n polyOne))) p) (polyMul W p) :=
    hinner.mul (PaddedPolynomialCoeffEqv.refl _ p)
  exact Q'.eqv_trans _ _ _ (he.haar
    (supported_polyMul (supported_polyMul hW (supported_polyMul (supported_one _) (lift_supported (supported_one n) n))) hp)
    (supported_polyMul hW hp)) (haar_of_coeff (RatPolyCoeffEqv.mul_comm W p))

private theorem sum_zero_slot (v : Q') : ∀ M,
    finSum (fun j => if j = 0 then v else 0) (M+1) ≈ v
  | 0 => Q'.eqv_of_eq (Q'.zero_add' v)
  | M+1 => Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) (sum_zero_slot v M)

private theorem finite_sum_congr (f g : Nat → RatPoly) : ∀ xs,
    (∀ j, j ∈ xs → f j = g j) → finitePolySum f xs = finitePolySum g xs
  | [], _ => rfl
  | j::js, h => by
      simp only [finitePolySum, h j List.mem_cons_self,
        finite_sum_congr f g js (fun s hs => h s (List.mem_cons_of_mem j hs))]

private theorem heat_prefix (a b : Nat) (q : Q') (K : Nat) :
    heatAt a b q K = heatPrefix q K (scalarAt a b) := by
  unfold heatAt heatPrefix
  apply finite_sum_congr
  intro j hj
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hj)]

private theorem pair_quartic_vacuum (n a b : Nat) (ha : a < n+n) (hb : b < n+n)
    (hab : a ≠ b) (q : Q') (K : Nat) (hK2 : 2 ≤ K) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (n+n) r) (hd : HasQuaternionBlockDegree a 0 r) :
    H (n+n) (polyMul (pairQuartic a b q K) r) ≈ zeroCoeff q*H (n+n) r := by
  let x := scalarAt a b
  have hpair := pair_supported ha hb q K
  have hc (j : Nat) : response n r polyOne x j ≈ (if j = 0 then H (n+n) r else 0) :=
    Q'.eqv_trans _ _ _ (insertion_one n r _ hr (character_supported (scalar_supported ha hb) j))
      (pair_character_vacuum (n+n) (by omega) ⟨a,ha⟩ ⟨b,hb⟩ hab j r hr hd)
  have hsum : finSum (fun j => quarticCoeff (cutCoeff q K) j*response n r polyOne x j) (K+3) ≈
      quarticCoeff (cutCoeff q K) 0*H (n+n) r := by
    refine Q'.eqv_trans _ _ _ (finSum_eqv_congr _ _ (fun j => ?_) (K+3)) (sum_zero_slot _ (K+2))
    by_cases hj : j = 0
    · subst j; exact Q'.mul_eqv_congr_left _ _ _ (hc 0)
    · rw [if_neg hj]
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (hc j))
        (by rw [if_neg hj]; exact Q'.mul_zero_eqv _)
  have hz : quarticCoeff (cutCoeff q K) 0 = zeroCoeff q := by
    simp only [quarticCoeff, cutCoeff, if_pos (show 0 ≤ K by omega),
      if_pos (show 1 ≤ K by omega), if_pos hK2, zeroCoeff]
  have hv := quartic_value_regrouped n r polyOne x q K
  rw [← heat_prefix a b q K] at hv
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (insertion_one n r (pairQuartic a b q K) hr hpair))
    (Q'.eqv_trans _ _ _ hv (by rw [hz] at hsum; exact hsum))

private theorem scalar_symm (a b : Nat) : RatPolyCoeffEqv (scalarAt a b) (scalarAt b a) := by
  let E : Nat → RatPoly := fun
    | 0 => (PolyQuaternion.coordinateVariable a).scalar
    | 1 => (PolyQuaternion.coordinateVariable a).iPart
    | 2 => (PolyQuaternion.coordinateVariable a).jPart
    | 3 => (PolyQuaternion.coordinateVariable a).kPart
    | 4 => (PolyQuaternion.coordinateVariable b).scalar
    | 5 => (PolyQuaternion.coordinateVariable b).iPart
    | 6 => (PolyQuaternion.coordinateVariable b).jPart
    | _ => (PolyQuaternion.coordinateVariable b).kPart
  simpa only [scalarAt, PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
    PolyQuaternionExpr.coordinate, coeffEvalExpr, E, PolyQuaternion.mul, PolyQuaternion.conj] using
    (coeffEvalExpr_eqv_of_normalize_eq
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 4))).scalar
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 4) (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))).scalar
      (by decide) E)

private theorem pair_symm (a b : Nat) (q : Q') (K : Nat) :
    RatPolyCoeffEqv (pairQuartic a b q K) (pairQuartic b a q K) := by
  have hc := characterPolynomial_coeffEqv (scalar_symm a b) 1
  have hd := (RatPolyCoeffEqv.refl (cap 2)).add (RatPolyCoeffEqv.neg hc)
  exact (hd.mul hd).mul (heatAt_symm a b q K)

private theorem pair_independent (slot a b : Nat) (ha : slot ≠ a) (hb : slot ≠ b) (q : Q') (K : Nat) :
    HasQuaternionBlockDegree slot 0 (pairQuartic a b q K) := by
  have hs := scalar_independent slot a b ha hb
  have hc := character_independent hs 1
  have hd : HasQuaternionBlockDegree slot 0 (defect (scalarAt a b)) :=
    ((hasQuaternionBlockDegree_one slot).smul 2).add hc.neg
  exact (hd.mul hd).mul (heat_independent slot a b ha hb q K)

private theorem peel (n : Nat) (q : Q') (K : Nat) (upper : Bool) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (n+n) r) : ∀ ids : List Nat,
    ids.Nodup → (∀ j, j ∈ ids → j < n) →
    (∀ j, j ∈ ids → HasQuaternionBlockDegree (if upper then n+j else j) 0 r) →
    H (n+n) (polyMul (productHeat n q K ids) r) ≈ H (n+n) r
  | [], _, _, _ => haar_of_coeff (RatPolyCoeffEqv.one_mul r)
  | j::js, hn, hi, hd => by
      have hj := hi j List.mem_cons_self
      have ht := List.nodup_cons.mp hn
      have hit (k : Nat) (hk : k ∈ js) := hi k (List.mem_cons_of_mem j hk)
      have hrest := supported_polyMul (productHeat_supported n q K js hit) hr
      have hleft := independent_has_degree_zero (productHeat_independent_lower n q K js hit j hj ht.1)
      have hright := independent_has_degree_zero (productHeat_independent_upper n q K js hit j hj ht.1)
      have hp : H (n+n) (polyMul (heatAt j (n+j) q K) (polyMul (productHeat n q K js) r)) ≈
          H (n+n) (polyMul (productHeat n q K js) r) := by
        have he : (n+n-1)+1 = n+n := by omega
        cases upper with
        | false =>
            have hv := pair_vacuum (n+n-1) (by omega) ⟨j,by omega⟩ ⟨n+j,by omega⟩
              (by change j ≠ n+j; omega) q K _ (by simpa only [he] using hrest)
              (hleft.mul (hd j List.mem_cons_self))
            simpa only [he] using hv
        | true =>
            have hv := pair_vacuum (n+n-1) (by omega) ⟨n+j,by omega⟩ ⟨j,by omega⟩
              (by change n+j ≠ j; omega) q K _ (by simpa only [he] using hrest)
              (hright.mul (hd j List.mem_cons_self))
            exact Q'.eqv_trans _ _ _ (haar_of_coeff ((heatAt_symm j (n+j) q K).mul_right _))
              (by simpa only [he] using hv)
      exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
        (Q'.eqv_trans _ _ _ hp (peel n q K upper r hr js ht.2 hit
          (fun k hk => hd k (List.mem_cons_of_mem j hk))))

private theorem rearrange (n : Nat) (q : Q') (K i : Nat) (ids : List Nat) (r : RatPoly) :
    RatPolyCoeffEqv (polyMul (quarticProduct n q K i ids) r)
      (polyMul (productHeat n q K ids) (polyMul (pairQuartic i (n+i) q K) r)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
    (.mul (.var 2) (.mul (.mul (.var 0) (.var 1)) (.var 3))) (by decide)
    (fun
      | 0 => polyMul (defect (scalarAt i (n+i))) (defect (scalarAt i (n+i)))
      | 1 => heatAt i (n+i) q K
      | 2 => productHeat n q K ids
      | _ => r)

theorem quarticProduct_upper_marginal (n : Nat) (q : Q') (K i : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (hK2 : 2 ≤ K) (f : RatPoly) (hf : SupportedQuaternionBlocks n f) :
    H (n+n) (polyMul (quarticProduct n q K i ids) (liftBoundary n f)) ≈ zeroCoeff q*H n f := by
  let r := polyMul (pairQuartic i (n+i) q K) (liftBoundary n f)
  have hr := supported_polyMul (pair_supported (show i < n+n by omega) (show n+i < n+n by omega) q K) (lift_supported hf n)
  have hd (j : Nat) (hj : j ∈ ids) : HasQuaternionBlockDegree j 0 r :=
    (pair_independent j i (n+i) (by intro he; subst j; exact hnot hj) (by have := hids j hj; omega) q K).mul
      (independent_has_degree_zero (lift_lower_independent n f j (hids j hj)))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (rearrange n q K i ids _))
    (Q'.eqv_trans _ _ _ (peel n q K false r hr ids hn hids hd)
      (Q'.eqv_trans _ _ _ (pair_quartic_vacuum n i (n+i) (by omega) (by omega) (by omega) q K hK2 _
        (lift_supported hf n) (independent_has_degree_zero (lift_lower_independent n f i hi)))
        (Q'.mul_eqv_congr_left _ _ _ (haar_liftBoundary n n f))))

theorem quarticProduct_lower_marginal (n : Nat) (q : Q') (K i : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (hK2 : 2 ≤ K) (f : RatPoly) (hf : SupportedQuaternionBlocks n f) :
    H (n+n) (polyMul (quarticProduct n q K i ids) f) ≈ zeroCoeff q*H n f := by
  let r := polyMul (pairQuartic i (n+i) q K) f
  have hr := supported_polyMul (pair_supported (show i < n+n by omega) (show n+i < n+n by omega) q K) (support_lower hf)
  have hd (j : Nat) (hj : j ∈ ids) : HasQuaternionBlockDegree (n+j) 0 r :=
    (pair_independent (n+j) i (n+i) (by have := hids j hj; omega)
      (by
        intro he
        have he' : j = i := by omega
        exact hnot (he' ▸ hj)) q K).mul
      (independent_has_degree_zero (supported_upper_independent hf j))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (rearrange n q K i ids f))
    (Q'.eqv_trans _ _ _ (peel n q K true r hr ids hn hids hd)
      (Q'.eqv_trans _ _ _ (haar_of_coeff ((pair_symm i (n+i) q K).mul_right f))
        (Q'.eqv_trans _ _ _ (pair_quartic_vacuum n (n+i) i (by omega) (by omega) (by omega) q K hK2 f
          (support_lower hf) (independent_has_degree_zero (supported_upper_independent hf i)))
          (Q'.mul_eqv_congr_left _ _ _ (quaternionHaar_extend_supported_endpoint (by omega) f hf)))))

private theorem signed_young {n : Nat} (W a : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (HW : Certificate (n+n) W) (d : Q')
    (hl : weightedPair (n+n) W a a ≈ d*H n (polyMul a a))
    (hu : weightedPair (n+n) W (liftBoundary n a) (liftBoundary n a) ≈ d*H n (polyMul a a)) :
    weightedPair (n+n) W a (liftBoundary n a) ≤ d*H n (polyMul a a) := by
  let b := liftBoundary n a
  have hneg (p : RatPoly) : H (n+n) (polyNeg p) ≈ -(H (n+n) p) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (QuaternionHaarAngularCarrier.neg_smul p))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ (-1) p)
        (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0)) (by decide) (fun _ => H (n+n) p)))
  have hexp : H (n+n) (polyMul (polyMul (jump n a) (jump n a)) W) ≈
      weightedPair (n+n) W a a+(-(weightedPair (n+n) W a b)+
        (-(weightedPair (n+n) W a b)+weightedPair (n+n) W b b)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1)))) (.var 2))
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.add (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))
          (.add (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2))) (.mul (.mul (.var 1) (.var 1)) (.var 2)))))
      (by decide) (fun | 0 => a | 1 => b | _ => W)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) (Q'.add_eqv_congr' (hneg _)
          (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) (Q'.add_eqv_congr' (hneg _) (Q'.eqv_refl _)))))))
  have hp := HW.square_insertion_nonnegative (jump n a) (jump_supported ha)
  have he := Q'.eqv_trans _ _ _ hexp (Q'.add_eqv_congr' hl
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _ hu)))
  have halg : d*H n (polyMul a a)+(-(weightedPair (n+n) W a b)+
      (-(weightedPair (n+n) W a b)+d*H n (polyMul a a))) ≈
      2*(d*H n (polyMul a a)-weightedPair (n+n) W a b) :=
    poly_identity_of_normal_eq (.add (.var 0) (.add (.neg (.var 1)) (.add (.neg (.var 1)) (.var 0))))
      (.mul (.const 2) (.add (.var 0) (.neg (.var 1)))) (by decide)
      (fun | 0 => d*H n (polyMul a a) | _ => weightedPair (n+n) W a b)
  exact Q'.le_of_sub_nonneg (Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv 2))
      (Q'.le_trans' _ _ _ hp (Q'.le_of_eqv (Q'.eqv_trans _ _ _ he halg)))) (by decide))

/-- Arbitrary signed ENTIRE endpoint, with all original selected factors retained. -/
theorem quarticProduct_signed_schur (n : Nat) {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K i : Nat) (ids : List Nat) (hK : headCutoff q ≤ K) (hK2 : 2 ≤ K)
    (hn : ids.Nodup) (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (a : RatPoly) (ha : SupportedQuaternionBlocks n a) :
    weightedPair (n+n) (quarticProduct n q K i ids) a (liftBoundary n a) ≤ zeroCoeff q*H n (polyMul a a) := by
  apply signed_young _ a ha (quarticProduct_certificate n hq0 hq1 K i ids hK hi hids) (zeroCoeff q)
  · exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (quarticProduct_lower_marginal n q K i ids hn hi hnot hids hK2 _ (supported_polyMul ha ha))
  · unfold weightedPair
    rw [← lift_product]
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (quarticProduct_upper_marginal n q K i ids hn hi hnot hids hK2 _ (supported_polyMul ha ha))

theorem quarticProduct_signed_budget (n : Nat) {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K i : Nat) (ids : List Nat) (hK : headCutoff q ≤ K) (hK2 : 2 ≤ K)
    (hn : ids.Nodup) (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (a : RatPoly) (ha : SupportedQuaternionBlocks n a) :
    weightedPair (n+n) (quarticProduct n q K i ids) a (liftBoundary n a) ≤
      (60*RingNormaliser.qpow (1-q) 2)*H n (polyMul a a) :=
  Q'.le_trans' _ _ _ (quarticProduct_signed_schur n hq0 hq1 K i ids hK hK2 hn hi hnot hids a ha)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (zeroCoeff_le_sixty (Q'.le_of_lt hq0) (Q'.le_of_lt hq1))
      (Certificate.square a ha).haar_nonnegative)

/-- The whole original source/test square remains the literal raw moment. -/
theorem source_quarticProduct_signed_budget (n : Nat) {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K i : Nat) (ids : List Nat) (hK : headCutoff q ≤ K) (hK2 : 2 ≤ K)
    (hn : ids.Nodup) (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (source f : RatPoly) (hs : SupportedQuaternionBlocks n source) (hf : SupportedQuaternionBlocks n f) :
    weightedPair (n+n) (quarticProduct n q K i ids) (polyMul source f) (liftBoundary n (polyMul source f)) ≤
      (60*RingNormaliser.qpow (1-q) 2)*rawSourceMoment n source (polyMul f f) :=
  Q'.le_trans' _ _ _ (quarticProduct_signed_budget n hq0 hq1 K i ids hK hK2 hn hi hnot hids _ (supported_polyMul hs hf))
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_four_swap source f source f))))

#print axioms quarticProduct
#print axioms quarticProduct_supported
#print axioms quarticProduct_certificate
#print axioms quarticProduct_upper_marginal
#print axioms quarticProduct_lower_marginal
#print axioms quarticProduct_signed_schur
#print axioms quarticProduct_signed_budget
#print axioms source_quarticProduct_signed_budget

end YMGap.Continuum.SU2QuaternionProductHeatQuarticSchur
