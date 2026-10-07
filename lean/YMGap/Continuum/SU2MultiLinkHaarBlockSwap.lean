/-
# Block-permutation invariance of `quaternionHaar` / `multiLinkHaar`

(YM Group Realizer, J04 task 3b.)  `blockSwapPoly k` exchanges quaternion
blocks `k` and `k+1` (variables `4k..4k+3` ↔ `4k+4..4k+7`) in every monomial.
For `k + 2 ≤ n` it leaves `quaternionHaar n` invariant (`haar_blockSwap`);
iterating gives invariance under any finite word of adjacent swaps
(`haar_blockSwaps`), i.e. under every block permutation reachable that way.

Conjugating the Prover's head-link shear invariance by such a word gives
left/right shear invariance of `multiLinkHaar n` for the link that the word
moves to the head, translated by the block it moves to position 1
(`multiLinkHaar_conj_shear_invariant`).  Since adjacent swaps generate all
permutations of `Fin n`, every ordered pair of distinct links is reachable.

OPEN (stated honestly): a lemma identifying `blockSwaps ks.reverse ∘ T ∘
blockSwaps ks` with the substitution `u_i ↦ u_j·u_i` written directly on the
`i`-th block (pointwise on evaluations) is not proved here; the invariance
statement is about the conjugated operator.
-/

import YMGap.Continuum.SU2MultiLinkHaarFactorization
import YMGap.Continuum.SU2MultiLinkHaarInvariance

namespace YMGap.Continuum.SU2MultiLinkHaarBlockSwap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs
open YMGap.Continuum.SU2MultiLinkHaarFactorization

/-- Index map exchanging blocks `k` and `k+1`. -/
def sw (k i : Nat) : Nat :=
  if i < 4 * k then i else if i < 4 * k + 4 then i + 4 else if i < 4 * k + 8 then i - 4 else i

theorem sw_lo (k i : Nat) (h : i < 4 * k) : sw k i = i := by
  unfold sw; rw [if_pos h]
theorem sw_a (k i : Nat) (h1 : 4 * k ≤ i) (h2 : i < 4 * k + 4) : sw k i = i + 4 := by
  unfold sw; rw [if_neg (by omega), if_pos h2]
theorem sw_b (k i : Nat) (h1 : 4 * k + 4 ≤ i) (h2 : i < 4 * k + 8) : sw k i = i - 4 := by
  unfold sw; rw [if_neg (by omega), if_neg (by omega), if_pos h2]
theorem sw_hi (k i : Nat) (h : 4 * k + 8 ≤ i) : sw k i = i := by
  unfold sw; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Monomial with blocks `k`, `k+1` exchanged. -/
def blockSwapMono (k : Nat) (m : List Nat) : List Nat :=
  (List.range (m.length + 4 * k + 8)).map fun i => exponentAt m (sw k i)

private theorem exponentAt_map_range (L : Nat) (f : Nat → Nat) (i : Nat) (h : i < L) :
    exponentAt ((List.range L).map f) i = f i := by
  unfold exponentAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

private theorem exponentAt_map_range_ge (L : Nat) (f : Nat → Nat) (i : Nat) (h : L ≤ i) :
    exponentAt ((List.range L).map f) i = 0 :=
  exponentAt_of_length_le _ _ (by rw [List.length_map, List.length_range]; exact h)

theorem exponentAt_blockSwapMono (k : Nat) (m : List Nat) (i : Nat) :
    exponentAt (blockSwapMono k m) i = exponentAt m (sw k i) := by
  unfold blockSwapMono
  rcases Nat.lt_or_ge i (m.length + 4 * k + 8) with h | h
  · exact exponentAt_map_range _ _ _ h
  · rw [exponentAt_map_range_ge _ _ _ h, sw_hi k i (by omega),
      exponentAt_of_length_le m i (by omega)]

private theorem drop_exp (A : Nat) (M : List Nat) (i : Nat) :
    exponentAt (M.drop A) i = exponentAt M (A + i) := exponentAt_drop A M i

/-- Three-way split of a prefix at blocks `k`, `k+1`. -/
private theorem prefix_split3 (k r : Nat) (M : List Nat) :
    (quaternionHaarPrefix (k + (1 + (1 + r))) M).eqv
      (quaternionHaarPrefix k M * (quaternionHaarPrefix 1 (M.drop (4 * k)) *
        (quaternionHaarPrefix 1 ((M.drop (4 * k)).drop 4) *
          quaternionHaarPrefix r (((M.drop (4 * k)).drop 4).drop 4)))) := by
  refine Q'.eqv_trans _ _ _ (prefix_split k (1 + (1 + r)) M) ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _ (prefix_split 1 (1 + r) _) ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  exact prefix_split 1 r _

private theorem allZero_congr (l l' : List Nat) (h : ∀ i, exponentAt l i = exponentAt l' i) :
    allZero l = allZero l' := by
  cases h1 : allZero l <;> cases h2 : allZero l'
  · rfl
  · exact absurd ((allZero_iff l).mpr (fun i => (h i).trans (((allZero_iff l').mp h2) i))) (by rw [h1]; exact Bool.noConfusion)
  · exact absurd ((allZero_iff l').mpr (fun i => (h i).symm.trans (((allZero_iff l).mp h1) i))) (by rw [h2]; exact Bool.noConfusion)
  · rfl

private theorem swap_mid (a b c d : Q') : (a * (b * (c * d))).eqv (a * (c * (b * d))) := by
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv b c)) ?_
  exact Q'.mul_assoc_eqv _ _ _

theorem mono_blockSwap (n k : Nat) (hk : k + 2 ≤ n) (m : List Nat) :
    (quaternionHaarMono n (blockSwapMono k m)).eqv (quaternionHaarMono n m) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = k + (1 + (1 + r)) := ⟨n - (k + 2), by omega⟩
  have e := exponentAt_blockSwapMono k m
  unfold quaternionHaarMono
  rw [allZero_congr ((blockSwapMono k m).drop (4 * (k + (1 + (1 + r)))))
      (m.drop (4 * (k + (1 + (1 + r))))) (fun i => by
        rw [drop_exp, drop_exp, e, sw_hi k _ (by omega)])]
  cases allZero (m.drop (4 * (k + (1 + (1 + r)))))
  · exact Q'.eqv_refl _
  · show (quaternionHaarPrefix _ _).eqv (quaternionHaarPrefix _ _)
    refine Q'.eqv_trans _ _ _ (prefix_split3 k r _) ?_
    refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (prefix_split3 k r m))
    rw [prefix_congr k (blockSwapMono k m) m (fun i hi => by rw [e, sw_lo k i hi]),
      prefix_congr 1 (((blockSwapMono k m).drop (4 * k)).drop 4) (m.drop (4 * k))
        (fun i hi => by rw [drop_exp, drop_exp, drop_exp, e, sw_b k _ (by omega) (by omega)]; congr 1; omega),
      prefix_congr 1 ((blockSwapMono k m).drop (4 * k)) ((m.drop (4 * k)).drop 4)
        (fun i hi => by rw [drop_exp, drop_exp, drop_exp, e, sw_a k _ (by omega) (by omega)]; congr 1; omega),
      prefix_congr r ((((blockSwapMono k m).drop (4 * k)).drop 4).drop 4)
        (((m.drop (4 * k)).drop 4).drop 4)
        (fun i hi => by
          rw [drop_exp, drop_exp, drop_exp, drop_exp, drop_exp, drop_exp, e, sw_hi k _ (by omega)])]
    exact swap_mid _ _ _ _

/-- Polynomial with blocks `k`, `k+1` exchanged. -/
def blockSwapPoly (k : Nat) (p : RatPoly) : RatPoly := p.map fun t => (blockSwapMono k t.1, t.2)

theorem haar_blockSwap (n k : Nat) (hk : k + 2 ≤ n) :
    ∀ p : RatPoly, (quaternionHaar n (blockSwapPoly k p)).eqv (quaternionHaar n p)
  | [] => Q'.eqv_refl _
  | t :: rest =>
      Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (mono_blockSwap n k hk t.1))
        (haar_blockSwap n k hk rest)

/-- A word of adjacent swaps, applied left to right. -/
def blockSwaps : List Nat → RatPoly → RatPoly
  | [], p => p
  | k :: ks, p => blockSwaps ks (blockSwapPoly k p)

theorem haar_blockSwaps (n : Nat) :
    ∀ ks : List Nat, (∀ k ∈ ks, k + 2 ≤ n) →
      ∀ p : RatPoly, (quaternionHaar n (blockSwaps ks p)).eqv (quaternionHaar n p)
  | [], _, _ => Q'.eqv_refl _
  | k :: ks, h, p =>
      Q'.eqv_trans _ _ _
        (haar_blockSwaps n ks (fun j hj => h j (List.mem_cons_of_mem k hj)) _)
        (haar_blockSwap n k (h k List.mem_cons_self) p)

/-- Head shear conjugated by a swap word: translate the link moved to the head. -/
def conjShear (right : Bool) (ks : List Nat) (p : RatPoly) : RatPoly :=
  blockSwaps ks.reverse
    (translatedHeadPolynomial
      (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion)
      (blockSwaps ks p))

theorem multiLinkHaar_conj_shear_invariant (blocks : Nat) (hb : 0 < blocks) (right : Bool)
    (ks : List Nat) (hks : ∀ k ∈ ks, k + 2 ≤ blocks + 1) (p : RatPoly) :
    ((multiLinkHaar (blocks + 1)).h (conjShear right ks p)).eqv
      ((multiLinkHaar (blocks + 1)).h p) := by
  show (quaternionHaar (blocks + 1) (conjShear right ks p)).eqv (quaternionHaar (blocks + 1) p)
  unfold conjShear
  refine Q'.eqv_trans _ _ _
    (haar_blockSwaps _ ks.reverse (fun k hk => hks k (List.mem_reverse.mp hk)) _) ?_
  refine Q'.eqv_trans _ _ _
    (YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation.translatedHeadPolynomial_haar
      right blocks hb _) ?_
  exact haar_blockSwaps _ ks hks p

end YMGap.Continuum.SU2MultiLinkHaarBlockSwap
