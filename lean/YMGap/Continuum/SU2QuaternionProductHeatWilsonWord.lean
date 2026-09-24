/-
# Exact fundamental transmission for arbitrary distinct-link Wilson words

The original selected product heat sends a fundamental ordered word to
w^(3*perimeter) times itself. Each selected lower coordinate occurs exactly
once; all remaining heat factors and every supported final test are retained.
The quaternion prefix is lifted to the upper slice during the induction,
not discarded or commuted. This is NOT an eigenidentity for the interacting
transfer P(V*f), nor a relative energy or continuum theorem.
-/

import YMGap.Continuum.SU2QuaternionProductHeatPlaquette
import YMGap.Continuum.SU2QuaternionProductHeatConstant

namespace YMGap.Continuum.SU2QuaternionProductHeatWilsonWord

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

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul

/-- Original right-associated word, with an explicit block lookup. -/
def wordAt (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link) : PolyQuaternion :=
  wordWith (fun e => orientedCoordinateQuaternion (block e) e.reverse) es

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

/-- A block absent from the literal word has degree zero in all four
coordinates. This also supplies independence from the padded slice fringe. -/
theorem word_independent (i : Nat) (block : OrientedBF4Link → Nat) :
    ∀ es, (∀ e, e ∈ es → i ≠ block e) → HasPolyQuaternionBlockDegree i 0 (wordAt block es)
  | [], _ => ⟨hasQuaternionBlockDegree_one i, hasQuaternionBlockDegree_zero i 0,
      hasQuaternionBlockDegree_zero i 0, hasQuaternionBlockDegree_zero i 0⟩
  | e::es, h => by
      have hl := orientedCoordinateQuaternion_blockDegree (block e) i e.reverse
      rw [if_neg (h e List.mem_cons_self)] at hl
      exact hl.mul (word_independent i block es (fun f hf => h f (List.mem_cons_of_mem e hf)))

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

/-- An arbitrary supported prefix stays on the upper slice during removal.
All unselected factors are integrated by their exact original marginal. -/
theorem pairing_with_prefix (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (p : PolyQuaternion) (hp : QuaternionSupported n p)
    (g : RatPoly) (hg : SupportedQuaternionBlocks n g) :
    quaternionHaar (n+n) (polyMul (productHeat n w K ids)
      (polyMul (liftQuaternion n p ⋄ wordAt block es).scalar (liftBoundary n g))) ≈
      qpow w (3*es.length) * quaternionHaar n (polyMul g (p ⋄ wordAt block es).scalar) := by
  induction es generalizing ids p with
  | nil =>
      have hc := haar_of_coeff (blocks := n+n)
        (((PolyQuaternionCoeffEqv.mul_one (liftQuaternion n p)).scalar.mul_right
          (liftBoundary n g)).mul_left (productHeat n w K ids))
      have hm := productHeat_upper_marginal n w K ids hnd hids
        (polyMul p.scalar g) (supported_polyMul hp.scalar hg)
      rw [lift_product] at hm
      have ht := haar_of_coeff (blocks := n)
        ((RatPolyCoeffEqv.mul_comm p.scalar g).trans
          ((PolyQuaternionCoeffEqv.mul_one p).scalar.symm.mul_left g))
      exact Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ hm
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
      have htail : ∀ f, f ∈ es → block f ∈ rest := by
        intro f hf
        have hm := List.mem_cons.mp (hperm.mem_iff.mp (hselected f (List.mem_cons_of_mem e hf)))
        exact hm.elim (fun he => False.elim (hmap.1 (List.mem_map.mpr ⟨f,hf,he⟩))) id
      have hs : QuaternionSupported (n+n) (wordAt block es) :=
        word_supported (n+n) block es
          (fun f hf => Nat.lt_of_lt_of_le (hrest _ (htail f hf)) (Nat.le_add_right n n))
      have hd : HasPolyQuaternionBlockDegree i 0 (wordAt block es) :=
        word_independent i block es
          (fun f hf he => hmap.1 (List.mem_map.mpr ⟨f,hf,he.symm⟩))
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
      have hprop := Propagates.recode (RatPolyCoeffEqv.refl _) hout step.scalar
      have hremove := remove_selected n w K i rest hi hnrest.1 hrest hprop g hg
      have hchange := haar_of_coeff (blocks := n+n)
        ((polynomialProduct_perm (fun j => heatAt j (n+j) w K) hperm).mul_right
          (polyMul (liftQuaternion n p ⋄ wordAt block (e::es)).scalar (liftBoundary n g)))
      have hrec := ih rest hnrest.2 hrest hmap.2 htail (p ⋄ c) hp'
      have hfinal := haar_of_coeff (blocks := n)
        ((PolyQuaternionCoeffEqv.mul_assoc p c (wordAt block es)).scalar.mul_left g)
      exact Q'.eqv_trans _ _ _ hchange
        (Q'.eqv_trans _ _ _ hremove
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hrec)
            (Q'.eqv_trans _ _ _ (rate_step w _ es.length)
              (Q'.mul_eqv_congr_left _ _ _ hfinal))))

/-- Scalar transmission in the original supported-Haar quotient. -/
theorem productMap_word_scalar (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids) :
    SupportedHaarEqv n (productMap n w K ids (wordAt block es).scalar)
      (polySmul (qpow w (3*es.length)) (wordAt block es).scalar) := by
  intro g hg
  have hw2 := word_supported (n+n) block es
    (fun e he => Nat.lt_of_lt_of_le (hids _ (hselected e he)) (Nat.le_add_right n n))
  have hu := ((liftQuaternion_one (n+n) n).mul
      (PaddedQuaternionCoeffEqv.refl (n+n) (wordAt block es))).trans
    (PaddedQuaternionCoeffEqv.of_coeff (PolyQuaternionCoeffEqv.one_mul _))
  have hweighted := PaddedPolynomialCoeffEqv.haar_insert (blocks := n+n)
    (p := (liftQuaternion n PolyQuaternion.one ⋄ wordAt block es).scalar)
    (q := (wordAt block es).scalar) hu.scalar
    ((lifted_supported (one_supported n)).mul hw2).scalar hw2.scalar
    (polyMul (productHeat n w K ids) (liftBoundary n g))
    (supported_polyMul (productHeat_supported n w K ids hids) (lift_supported hg n))
  have swap (f : RatPoly) : RatPolyCoeffEqv
      (polyMul (productHeat n w K ids) (polyMul f (liftBoundary n g)))
      (polyMul (polyMul (productHeat n w K ids) (liftBoundary n g)) f) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => productHeat n w K ids | 1 => f | _ => liftBoundary n g)
  have hleft := Q'.eqv_trans _ _ _ (haar_of_coeff (swap _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hweighted) (haar_of_coeff (swap _).symm))
  have hp := pairing_with_prefix n w K hK block es ids hnd hids hword hselected
    PolyQuaternion.one (one_supported n) g hg
  have hright := haar_of_coeff (blocks := n)
    ((PolyQuaternionCoeffEqv.one_mul (wordAt block es)).scalar.mul_left g)
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K ids _ g)
    (Q'.eqv_trans _ _ _ hleft (Q'.eqv_trans _ _ _ hp
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hright)
        (Q'.eqv_symm (quaternionHaar_polyMul_smul_right n _ g _)))))

/-- The fundamental character has the same exact kinetic multiplier. The
arbitrary final supported test may contain the full interacting source. -/
theorem productMap_fundamental_word (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids) :
    let f := characterPolynomial (wordAt block es).scalar 1
    SupportedHaarEqv n (productMap n w K ids f)
      (polySmul (qpow w (3*es.length)) f) := by
  dsimp only
  intro g hg
  have hs := productMap_word_scalar n w K hK block es ids hnd hids hword hselected
  have hl := productMap_smul n w K ids 2 (wordAt block es).scalar
  have hh := hs.smul 2 g hg
  have hr : RatPolyCoeffEqv (polySmul 2 (polySmul (qpow w (3*es.length)) (wordAt block es).scalar))
      (polySmul (qpow w (3*es.length)) (polySmul 2 (wordAt block es).scalar)) := by
    intro weight
    exact Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight 2 _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (ratWeightedSum_smul weight _ _))
        (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq (.mul (.const 2) (.mul (.var 0) (.var 1)))
            (.mul (.var 0) (.mul (.const 2) (.var 1))) (by decide)
            (fun | 0 => qpow w (3*es.length) | _ => ratWeightedSum weight (wordAt block es).scalar))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (ratWeightedSum_smul weight 2 _)))
            (Q'.eqv_symm (ratWeightedSum_smul weight _ _)))))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (hl.mul_left g))
    (Q'.eqv_trans _ _ _ hh (haar_of_coeff (hr.mul_left g)))

#print axioms wordAt
#print axioms word_independent
#print axioms pairing_with_prefix
#print axioms productMap_word_scalar
#print axioms productMap_fundamental_word

end YMGap.Continuum.SU2QuaternionProductHeatWilsonWord
