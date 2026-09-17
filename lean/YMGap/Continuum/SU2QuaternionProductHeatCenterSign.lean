/-
# Center signs commute with the original product heat map

The same signs act on matching lower/upper quaternion blocks. Each relative
heat factor is unchanged, and exact partial Haar integration commutes with
the retained signs. These are coefficient identities for the original finite
polynomial map, including coordinates absent from the kinetic factor list.
No spatial potential, physical odd sector, or spectral gap is assumed here.
-/

import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.SU2QuaternionCoordinateConjugation

namespace YMGap.Continuum.SU2QuaternionProductHeatCenterSign

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (exponentAt_clearQuaternionBlock_self)
open YMGap.Continuum.SU2QuaternionCoordinateConjugation (signSelectedPolynomial_var)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)

local infix:50 " ≈ " => Q'.eqv

/-- Simultaneously negate all four coordinates in every selected block. -/
def blockSign (blocks : Nat) (selected : Nat → Bool) (p : RatPoly) : RatPoly :=
  signSelectedPolynomial (4*blocks) (fun k => selected (k/4)) p

/-- The SAME selector on lower and matching upper blocks. -/
def pairedSelector (n : Nat) (selected : Nat → Bool) (i : Nat) : Bool :=
  if i < n then selected i else selected (i-n)

/-- Negate selected lower blocks only, on the unchanged two-slice carrier. -/
def lowerSign (n : Nat) (selected : Nat → Bool) (p : RatPoly) : RatPoly :=
  blockSign (n+n) (fun i => if i<n then selected i else false) p

private theorem parity_succ (n : Nat) (s : Nat → Bool) (m : List Nat) :
    selectedExponentParity (n+1) s m =
      if s n then xor (selectedExponentParity n s m) (decide (exponentAt m n % 2 = 1))
      else selectedExponentParity n s m := by
  simp only [selectedExponentParity, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

private theorem parity_congr (n : Nat) (s t : Nat → Bool) (m : List Nat)
    (hst : ∀ k, k < n → s k = t k) :
    selectedExponentParity n s m = selectedExponentParity n t m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [parity_succ, parity_succ, hst n (Nat.lt_succ_self n),
      ih (fun k hk => hst k (by omega))]

private theorem sign_selector_congr (n : Nat) (s t : Nat → Bool)
    (hst : ∀ k, k < n → s k = t k) (p : RatPoly) :
    signSelectedPolynomial n s p = signSelectedPolynomial n t p := by
  apply List.map_congr_left
  intro term _
  simp only [signSelectedTerm, parity_congr n s t term.1 hst]

private theorem parity_nil (n : Nat) (s : Nat → Bool) :
    selectedExponentParity n s [] = false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [parity_succ, ih]; simp [exponentAt]

theorem blockSign_one (blocks : Nat) (selected : Nat → Bool) :
    blockSign blocks selected polyOne = polyOne := by
  simp only [blockSign, signSelectedPolynomial, polyOne, List.map_cons, List.map_nil,
    signSelectedTerm, parity_nil, Bool.false_eq_true, ↓reduceIte]

theorem blockSign_supported {blocks : Nat} (selected : Nat → Bool) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (blockSign blocks selected p) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact hp source hs

private theorem exponent_zero {m : List Nat} {i : Nat} (hi : m.length ≤ i) : exponentAt m i = 0 := by
  induction m generalizing i with
  | nil => simp [exponentAt]
  | cons a rest ih =>
    cases i with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hi)
    | succ i => exact ih (Nat.le_of_succ_le_succ hi)

private theorem parity_extend (n extra : Nat) (s : Nat → Bool) (m : List Nat)
    (hm : m.length ≤ n) : selectedExponentParity (n+extra) s m = selectedExponentParity n s m := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    rw [show n+(extra+1) = (n+extra)+1 by omega, parity_succ, ih,
      exponent_zero (by omega : m.length ≤ n+extra)]
    simp

private theorem sign_restrict (n : Nat) (s t : Nat → Bool)
    (hst : ∀ i, i<n → t i = s i) {f : RatPoly} (hf : SupportedQuaternionBlocks n f) :
    blockSign (n+n) t f = blockSign n s f := by
  apply List.map_congr_left
  intro term ht
  have hp : selectedExponentParity (4*(n+n)) (fun k => t (k/4)) term.1 =
      selectedExponentParity (4*n) (fun k => s (k/4)) term.1 := by
    rw [show 4*(n+n) = 4*n+4*n by omega, parity_extend (4*n) (4*n) _ term.1 (hf term ht)]
    exact parity_congr _ _ _ _ (fun k hk => hst (k/4) (by omega))
  simp only [signSelectedTerm, hp]

theorem lowerSign_lower (n : Nat) (s : Nat → Bool) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) : lowerSign n s f = blockSign n s f :=
  sign_restrict n s _ (fun i hi => by rw [if_pos hi]) hf

private theorem parity_even (count : Nat) (s : Nat → Bool) (m : List Nat)
    (he : ∀ k, k<count → s k=true → exponentAt m k % 2=0) :
    selectedExponentParity count s m = false := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [parity_succ, ih (fun k hk => he k (by omega))]
    by_cases hs : s count=true
    · have hz := he count (Nat.lt_succ_self count) hs
      have hne : exponentAt m count % 2 ≠ 1 := by omega
      simp only [hs, ↓reduceIte, hne, decide_false, Bool.false_xor]
    · rw [if_neg hs]

private theorem sign_fixed_of_even (count : Nat) (s : Nat → Bool) : ∀ p : RatPoly,
    (∀ term, term∈p → ∀ k, k<count → s k=true → exponentAt term.1 k % 2=0) →
    signSelectedPolynomial count s p = p
  | [], _ => rfl
  | term::rest, he => by
    have ht : signSelectedTerm count s term = term := by
      simp only [signSelectedTerm, parity_even count s term.1 (he term List.mem_cons_self),
        Bool.false_eq_true, ↓reduceIte]
    change signSelectedTerm count s term :: signSelectedPolynomial count s rest = term::rest
    rw [ht, sign_fixed_of_even count s rest (fun t ht => he t (List.mem_cons_of_mem term ht))]

/-- Every upper/spectator polynomial is fixed exactly, without a support guard. -/
theorem lowerSign_lift (n : Nat) (s : Nat → Bool) (f : RatPoly) :
    lowerSign n s (liftBoundary n f) = liftBoundary n f := by
  apply sign_fixed_of_even
  intro term ht k _ hs
  have hi : k/4<n := by
    by_cases hi : k/4<n
    · exact hi
    · simp only [if_neg hi, Bool.false_eq_true] at hs
  have hz := exponentAt_clearQuaternionBlock_self term.1 (k/4) (k%4) (by omega)
  rw [(lift_lower_independent n f (k/4) hi) term ht,
    show 4*(k/4)+k%4=k by omega] at hz
  rw [hz]

private theorem even_four_parity (s : Nat → Bool) (m : List Nat)
    (h : exponentAt m 0 % 2 = 0 ∧ exponentAt m 1 % 2 = 0 ∧
      exponentAt m 2 % 2 = 0 ∧ exponentAt m 3 % 2 = 0) :
    selectedExponentParity 4 s m = false := by
  apply parity_even
  intro k hk _
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

private theorem parity_drop_four (count : Nat) (s : Nat → Bool) (m : List Nat)
    (h : exponentAt m 0 % 2 = 0 ∧ exponentAt m 1 % 2 = 0 ∧
      exponentAt m 2 % 2 = 0 ∧ exponentAt m 3 % 2 = 0) :
    selectedExponentParity (4+count) s m =
      selectedExponentParity count (fun k => s (4+k)) (m.drop 4) := by
  induction count with
  | zero => exact even_four_parity s m h
  | succ count ih =>
    rw [show 4+(count+1) = (4+count)+1 by omega, parity_succ, parity_succ,
      ih, exponentAt_drop]

private theorem single_coeff (m : List Nat) {a b : Q'} (h : a ≈ b) :
    RatPolyCoeffEqv [(m,a)] [(m,b)] := by
  intro weight
  change a*weight m+0 ≈ b*weight m+0
  exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ h) (Q'.eqv_refl 0)

private theorem head_sign (tail : Nat) (s : Nat → Bool) : ∀ p : RatPoly,
    RatPolyCoeffEqv (partialHaarHead (signSelectedPolynomial (4*(tail+1)) s p))
      (signSelectedPolynomial (4*tail) (fun k => s (4+k)) (partialHaarHead p))
  | [] => .refl _
  | term::rest => by
    have ht : RatPolyCoeffEqv
        [partialHaarHeadTerm (signSelectedTerm (4*(tail+1)) s term)]
        [signSelectedTerm (4*tail) (fun k => s (4+k)) (partialHaarHeadTerm term)] := by
      apply single_coeff
      change (if selectedExponentParity (4*(tail+1)) s term.1 then -term.2 else term.2)*
          headQuaternionMoment term.1 ≈
        (if selectedExponentParity (4*tail) (fun k => s (4+k)) (term.1.drop 4)
          then -(term.2*headQuaternionMoment term.1) else term.2*headQuaternionMoment term.1)
      by_cases he : exponentAt term.1 0 % 2 = 0 ∧ exponentAt term.1 1 % 2 = 0 ∧
          exponentAt term.1 2 % 2 = 0 ∧ exponentAt term.1 3 % 2 = 0
      · rw [show 4*(tail+1) = 4+4*tail by omega, parity_drop_four (4*tail) s term.1 he]
        split
        · exact Q'.neg_mul_eqv _ _
        · exact Q'.eqv_refl _
      · have hz : headQuaternionMoment term.1 = 0 := by unfold headQuaternionMoment sphereMoment4; rw [dif_neg he]
        rw [hz]
        refine Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _) ?_
        split
        · exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_zero_eqv _))
            (by decide : -(0 : Q') ≈ 0))
        · exact Q'.eqv_symm (Q'.mul_zero_eqv _)
    exact ht.add (head_sign tail s rest)

/-- Arbitrary coordinate signs commute with integrating head quaternion blocks;
the first-block odd moments vanish exactly, with all tail coefficients retained. -/
theorem partialHaarHeads_sign (tail : Nat) : ∀ (heads : Nat) (s : Nat → Bool) (p : RatPoly),
    RatPolyCoeffEqv (partialHaarHeads heads (signSelectedPolynomial (4*(tail+heads)) s p))
      (signSelectedPolynomial (4*tail) (fun k => s (4*heads+k)) (partialHaarHeads heads p))
  | 0, s, p => by
    simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add, partialHaarHeads]
    exact .refl _
  | heads+1, s, p => by
    have h := partialHaarHeads_congr heads (head_sign (tail+heads) s p)
    have ih := partialHaarHeads_sign tail heads (fun k => s (4+k)) (partialHaarHead p)
    have he : (fun k => s (4+(4*heads+k))) = (fun k => s (4*(heads+1)+k)) :=
      funext (fun k => congrArg s (by omega))
    rw [he] at ih
    exact h.trans ih

private theorem paired_tail (n : Nat) (s : Nat → Bool) (k : Nat) :
    pairedSelector n s ((4*n+k)/4) = s (k/4) := by
  unfold pairedSelector
  rw [if_neg (by omega : ¬ (4*n+k)/4<n)]
  exact congrArg s (by omega)

theorem kernelMap_centerSign {n : Nat} (s : Nat → Bool) {W f : RatPoly}
    (hW : RatPolyCoeffEqv (blockSign (n+n) (pairedSelector n s) W) W)
    (hf : SupportedQuaternionBlocks n f) :
    RatPolyCoeffEqv (blockSign n s (kernelMap n W f))
      (kernelMap n W (blockSign n s f)) := by
  have h := partialHaarHeads_sign n n (fun k => pairedSelector n s (k/4)) (polyMul W f)
  have he := sign_selector_congr (4*n)
    (fun k => pairedSelector n s ((4*n+k)/4)) (fun k => s (k/4))
    (fun k _ => paired_tail n s k) (partialHaarHeads n (polyMul W f))
  rw [he] at h
  have hm := signSelectedPolynomial_mul_coeffEqv (4*(n+n))
    (fun k => pairedSelector n s (k/4)) W f
  have hl := sign_restrict n s (pairedSelector n s)
    (fun i hi => by unfold pairedSelector; rw [if_pos hi]) hf
  change RatPolyCoeffEqv _ (polyMul (blockSign (n+n) (pairedSelector n s) W)
    (blockSign (n+n) (pairedSelector n s) f)) at hm
  rw [hl] at hm
  exact h.symm.trans (partialHaarHeads_congr n (hm.trans (hW.mul (.refl _))))

private def dotPolynomial (a b : Nat) : RatPoly :=
  polyAdd (polyMul (polyVar (4*a)) (polyVar (4*b)))
    (polyAdd (polyMul (polyVar (4*a+1)) (polyVar (4*b+1)))
      (polyAdd (polyMul (polyVar (4*a+2)) (polyVar (4*b+2)))
        (polyMul (polyVar (4*a+3)) (polyVar (4*b+3)))))

private theorem scalarAt_dot (a b : Nat) : RatPolyCoeffEqv (scalarAt a b) (dotPolynomial a b) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 1))
      (.neg (.add (.mul (.var 2) (.neg (.var 3)))
        (.add (.mul (.var 4) (.neg (.var 5))) (.mul (.var 6) (.neg (.var 7)))))))
    (.add (.mul (.var 0) (.var 1))
      (.add (.mul (.var 2) (.var 3))
        (.add (.mul (.var 4) (.var 5)) (.mul (.var 6) (.var 7)))))
    (by decide) (fun
      | 0 => polyVar (4*a) | 1 => polyVar (4*b)
      | 2 => polyVar (4*a+1) | 3 => polyVar (4*b+1)
      | 4 => polyVar (4*a+2) | 5 => polyVar (4*b+2)
      | 6 => polyVar (4*a+3) | _ => polyVar (4*b+3))

private theorem sign_variable (blocks : Nat) (s : Nat → Bool)
    (i c : Nat) (hi : i < blocks) (hc : c < 4) :
    blockSign blocks s (polyVar (4*i+c)) =
      if s i then polyNeg (polyVar (4*i+c)) else polyVar (4*i+c) := by
  unfold blockSign
  rw [signSelectedPolynomial_var _ _ _ (by omega), show (4*i+c)/4=i by omega]

private theorem sign_dot_term (blocks : Nat) (s : Nat → Bool) (a b c : Nat)
    (ha : a < blocks) (hb : b < blocks) (hc : c < 4) (hs : s a = s b) :
    RatPolyCoeffEqv (blockSign blocks s (polyMul (polyVar (4*a+c)) (polyVar (4*b+c))))
      (polyMul (polyVar (4*a+c)) (polyVar (4*b+c))) := by
  have h := signSelectedPolynomial_mul_coeffEqv (4*blocks) (fun k => s (k/4))
    (polyVar (4*a+c)) (polyVar (4*b+c))
  change RatPolyCoeffEqv _ (polyMul (blockSign blocks s (polyVar (4*a+c)))
    (blockSign blocks s (polyVar (4*b+c)))) at h
  rw [sign_variable blocks s a c ha hc, sign_variable blocks s b c hb hc, hs] at h
  cases hbit : s b with
  | false => simpa only [hbit, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    simp only [hbit, ↓reduceIte] at h
    exact h.trans (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.neg (.var 0)) (.neg (.var 1))) (.mul (.var 0) (.var 1))
      (by decide) (fun | 0 => polyVar (4*a+c) | _ => polyVar (4*b+c)))

theorem scalarAt_centerSign (blocks : Nat) (s : Nat → Bool) (a b : Nat)
    (ha : a < blocks) (hb : b < blocks) (hs : s a = s b) :
    RatPolyCoeffEqv (blockSign blocks s (scalarAt a b)) (scalarAt a b) := by
  have hdot : RatPolyCoeffEqv (blockSign blocks s (dotPolynomial a b)) (dotPolynomial a b) := by
    unfold dotPolynomial blockSign
    rw [signSelectedPolynomial_add, signSelectedPolynomial_add, signSelectedPolynomial_add]
    exact (sign_dot_term blocks s a b 0 ha hb (by decide) hs).add
      ((sign_dot_term blocks s a b 1 ha hb (by decide) hs).add
        ((sign_dot_term blocks s a b 2 ha hb (by decide) hs).add
          (sign_dot_term blocks s a b 3 ha hb (by decide) hs)))
  exact (signSelectedPolynomial_coeffEqv _ _ (scalarAt_dot a b)).trans
    (hdot.trans (scalarAt_dot a b).symm)

private theorem character_fixed (blocks : Nat) (s : Nat → Bool) (p : RatPoly)
    (hp : RatPolyCoeffEqv (blockSign blocks s p) p) : ∀ spin,
    RatPolyCoeffEqv (blockSign blocks s (characterPolynomial p spin)) (characterPolynomial p spin)
  | 0 => by rw [characterPolynomial, blockSign_one]; exact .refl _
  | 1 => (signSelectedPolynomial_smul_coeffEqv _ _ 2 p).trans (hp.smul 2)
  | spin+2 => by
    change RatPolyCoeffEqv
      (signSelectedPolynomial (4*blocks) (fun k => s (k/4))
        (polyAdd (polyMul (polySmul 2 p) (characterPolynomial p (spin+1)))
          (polySmul (-1) (characterPolynomial p spin)))) _
    rw [signSelectedPolynomial_add]
    exact ((signSelectedPolynomial_mul_coeffEqv _ _ _ _).trans
      (((signSelectedPolynomial_smul_coeffEqv _ _ 2 p).trans (hp.smul 2)).mul
        (character_fixed blocks s p hp (spin+1)))).add
      ((signSelectedPolynomial_smul_coeffEqv _ _ (-1) _).trans
        ((character_fixed blocks s p hp spin).smul (-1)))

private theorem sum_fixed {A : Type} (blocks : Nat) (s : Nat → Bool) (f : A → RatPoly) :
    ∀ ids : List A, (∀ i, i ∈ ids → RatPolyCoeffEqv (blockSign blocks s (f i)) (f i)) →
      RatPolyCoeffEqv (blockSign blocks s (finitePolySum f ids)) (finitePolySum f ids)
  | [], _ => .refl _
  | i::ids, hi => by
    change RatPolyCoeffEqv (signSelectedPolynomial _ _ (polyAdd (f i) (finitePolySum f ids))) _
    rw [signSelectedPolynomial_add]
    exact (hi i List.mem_cons_self).add
      (sum_fixed blocks s f ids (fun j hj => hi j (List.mem_cons_of_mem i hj)))

/-- Any equal endpoint signs fix the complete relative heat prefix. -/
theorem heatAt_centerSign (blocks : Nat) (s : Nat → Bool) (a b : Nat)
    (ha : a < blocks) (hb : b < blocks) (hs : s a = s b) (w : Q') (K : Nat) :
    RatPolyCoeffEqv (blockSign blocks s (heatAt a b w K)) (heatAt a b w K) :=
  sum_fixed blocks s _ _ (fun spin _ =>
    (signSelectedPolynomial_smul_coeffEqv _ _ _ _).trans
      ((character_fixed blocks s _ (scalarAt_centerSign blocks s a b ha hb hs) spin).smul _))

/-- The selector may act on either side, provided each retained heat pair
has equal endpoint signs. No nodup or positivity hypothesis is needed. -/
theorem productHeat_centerSign_of_pairs (n : Nat) (s : Nat → Bool) (w : Q') (K : Nat) :
    ∀ ids : List Nat, (∀ i, i ∈ ids → i < n) →
      (∀ i, i ∈ ids → s i = s (n+i)) →
      RatPolyCoeffEqv (blockSign (n+n) s (productHeat n w K ids)) (productHeat n w K ids)
  | [], _, _ => by change RatPolyCoeffEqv (blockSign (n+n) s polyOne) polyOne; rw [blockSign_one]; exact .refl _
  | i::ids, hi, hs =>
    (signSelectedPolynomial_mul_coeffEqv _ _ _ _).trans
      ((heatAt_centerSign (n+n) s i (n+i)
        (by have := hi i List.mem_cons_self; omega)
        (by have := hi i List.mem_cons_self; omega) (hs i List.mem_cons_self) w K).mul
        (productHeat_centerSign_of_pairs n s w K ids
          (fun j hj => hi j (List.mem_cons_of_mem i hj))
          (fun j hj => hs j (List.mem_cons_of_mem i hj))))

theorem productHeat_pairedSign (n : Nat) (s : Nat → Bool) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n) :
    RatPolyCoeffEqv (blockSign (n+n) (pairedSelector n s) (productHeat n w K ids))
      (productHeat n w K ids) :=
  productHeat_centerSign_of_pairs n _ w K ids hids (fun i hi => by
    unfold pairedSelector
    rw [if_pos (hids i hi), if_neg (by omega : ¬ n+i<n)]
    congr 1
    omega)

/-- A lower-only sign fixes a kernel whose retained factors all have unselected
lower endpoints. In particular this applies after the selected star is erased. -/
theorem productHeat_lowerSign (n : Nat) (s : Nat → Bool) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (hs : ∀ i, i ∈ ids → s i = false) :
    RatPolyCoeffEqv
      (blockSign (n+n) (fun i => if i<n then s i else false) (productHeat n w K ids))
      (productHeat n w K ids) :=
  productHeat_centerSign_of_pairs n _ w K ids hids (fun i hi => by
    rw [if_pos (hids i hi), if_neg (by omega : ¬ n+i<n), hs i hi])

/-- Exact equivariance of the original finite product map; absent coordinates
remain Haar projections rather than being removed from the carrier. -/
theorem productMap_centerSign (n : Nat) (s : Nat → Bool) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) :
    RatPolyCoeffEqv (blockSign n s (productMap n w K ids f))
      (productMap n w K ids (blockSign n s f)) :=
  kernelMap_centerSign s (productHeat_pairedSign n s w K ids hids) hf

end YMGap.Continuum.SU2QuaternionProductHeatCenterSign

#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.blockSign
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.pairedSelector
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.lowerSign
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.blockSign_one
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.blockSign_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.lowerSign_lower
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.lowerSign_lift
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.partialHaarHeads_sign
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.kernelMap_centerSign
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.scalarAt_centerSign
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.heatAt_centerSign
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.productHeat_centerSign_of_pairs
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.productHeat_pairedSign
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.productHeat_lowerSign
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCenterSign.productMap_centerSign
