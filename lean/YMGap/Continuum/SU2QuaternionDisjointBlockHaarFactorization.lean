/-
# Product Haar factorization for disjoint quaternion-block dependence

The finite S^3 moment formula factors across blocks. If at each block one
of two monomials is independent, its local product moment is multiplicative.
Finite polynomial linearity lifts this to signed polynomials on the SAME
declared carrier. No probabilistic independence axiom is used.
-/

import YMGap.Continuum.SU2QuaternionBlockLocality

namespace YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem qfour (a b c d : Q') : (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

private theorem product_mul (p q : Nat → Q') : ∀ xs : List Nat,
    listQProduct p xs * listQProduct q xs ≈ listQProduct (fun b => p b * q b) xs
  | [] => Q'.mul_one_eqv 1
  | b :: xs => Q'.eqv_trans _ _ _ (qfour (p b) (listQProduct p xs) (q b) (listQProduct q xs))
      (qmul (Q'.eqv_refl _) (product_mul p q xs))

private theorem mono_bound {blocks : Nat} {p q : List Nat}
    (hp : p.length ≤ 4 * blocks) (hq : q.length ≤ 4 * blocks) :
    (monoMul p q).length ≤ 4 * blocks := by
  have sp : SupportedQuaternionBlocks blocks [(p, (1 : Q'))] := by
    intro t ht
    have he := List.mem_singleton.mp ht
    subst t
    exact hp
  have sq : SupportedQuaternionBlocks blocks [(q, (1 : Q'))] := by
    intro t ht
    have he := List.mem_singleton.mp ht
    subst t
    exact hq
  exact supported_polyMul sp sq (monoMul p q, (1 : Q') * 1) List.mem_cons_self

theorem blockMoment_zero {m : List Nat} {block : Nat} (h : BlockZero m block) :
    quaternionBlockMoment m block ≈ 1 := by
  unfold quaternionBlockMoment
  rw [show exponentAt m (4 * block) = 0 from h 0 (by omega),
    h 1 (by omega), h 2 (by omega), h 3 (by omega)]
  exact sphereMoment4_one

theorem blockMoment_product (p q : List Nat) (block : Nat)
    (h : BlockZero p block ∨ BlockZero q block) :
    quaternionBlockMoment (monoMul p q) block ≈
      quaternionBlockMoment p block * quaternionBlockMoment q block := by
  rcases h with hp | hq
  · have hz := blockMoment_zero hp
    have he : quaternionBlockMoment (monoMul p q) block = quaternionBlockMoment q block := by
      unfold quaternionBlockMoment
      simp only [exponentAt_monoMul, show exponentAt p (4 * block) = 0 from hp 0 (by omega),
        hp 1 (by omega), hp 2 (by omega), hp 3 (by omega), Nat.zero_add]
    rw [he]
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hz) (Q'.one_mul_eqv _))
  · have hz := blockMoment_zero hq
    have he : quaternionBlockMoment (monoMul p q) block = quaternionBlockMoment p block := by
      unfold quaternionBlockMoment
      simp only [exponentAt_monoMul, show exponentAt q (4 * block) = 0 from hq 0 (by omega),
        hq 1 (by omega), hq 2 (by omega), hq 3 (by omega), Nat.add_zero]
    rw [he]
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_one_eqv _))

private theorem mono_product_form {blocks : Nat} {m : List Nat} (hm : m.length ≤ 4 * blocks) :
    quaternionHaarMono blocks m ≈ listQProduct (quaternionBlockMoment m) (quaternionBlockOrder blocks) := by
  unfold quaternionHaarMono
  rw [List.drop_eq_nil_of_le hm]
  exact quaternionHaarPrefix_eq_block_product blocks m

theorem haarMono_product {blocks : Nat} {p q : List Nat}
    (hp : p.length ≤ 4 * blocks) (hq : q.length ≤ 4 * blocks)
    (hd : ∀ block, block < blocks → BlockZero p block ∨ BlockZero q block) :
    quaternionHaarMono blocks (monoMul p q) ≈ quaternionHaarMono blocks p * quaternionHaarMono blocks q := by
  refine Q'.eqv_trans _ _ _ (mono_product_form (mono_bound hp hq)) ?_
  refine Q'.eqv_trans _ _ _ (listQProduct_congr_eqv _ _ _
    (fun block hb => blockMoment_product p q block (hd block ((mem_quaternionBlockOrder_iff _ _).mp hb)))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (product_mul (quaternionBlockMoment p) (quaternionBlockMoment q) _)) ?_
  exact qmul (Q'.eqv_symm (mono_product_form hp)) (Q'.eqv_symm (mono_product_form hq))

/-- Every monomial pair uses disjoint quaternion blocks. This explicitly
names the block-level condition; mere distinct coordinate indices do not suffice. -/
def BlockDisjoint (blocks : Nat) (p q : RatPoly) : Prop :=
  ∀ s, s ∈ p → ∀ t, t ∈ q → ∀ block, block < blocks → BlockZero s.1 block ∨ BlockZero t.1 block

private theorem row_factor (blocks : Nat) (s : RatTerm) : ∀ q : RatPoly,
    (∀ t, t ∈ q → quaternionHaarMono blocks (monoMul s.1 t.1) ≈
      quaternionHaarMono blocks s.1 * quaternionHaarMono blocks t.1) →
    quaternionHaar blocks (q.map (fun t => (monoMul s.1 t.1, s.2 * t.2))) ≈
      (s.2 * quaternionHaarMono blocks s.1) * quaternionHaar blocks q
  | [], _ => Q'.eqv_symm (Q'.mul_zero_eqv _)
  | t :: q, h => by
      change (s.2 * t.2) * quaternionHaarMono blocks (monoMul s.1 t.1) +
        quaternionHaar blocks (q.map _) ≈
        (s.2 * quaternionHaarMono blocks s.1) * (t.2 * quaternionHaarMono blocks t.1 + quaternionHaar blocks q)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (h t List.mem_cons_self))
          (qfour s.2 t.2 _ _))
        (row_factor blocks s q (fun u hu => h u (List.mem_cons_of_mem t hu)))) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _)

private theorem polynomial_factor (blocks : Nat) : ∀ p q : RatPoly,
    (∀ s, s ∈ p → ∀ t, t ∈ q → quaternionHaarMono blocks (monoMul s.1 t.1) ≈
      quaternionHaarMono blocks s.1 * quaternionHaarMono blocks t.1) →
    quaternionHaar blocks (polyMul p q) ≈ quaternionHaar blocks p * quaternionHaar blocks q
  | [], q, _ => Q'.eqv_symm (Q'.zero_mul_eqv _)
  | s :: p, q, h => by
      change quaternionHaar blocks ((q.map _) ++ polyMul p q) ≈
        (s.2 * quaternionHaarMono blocks s.1 + quaternionHaar blocks p) * quaternionHaar blocks q
      refine Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (row_factor blocks s q (h s List.mem_cons_self))
        (polynomial_factor blocks p q (fun t ht => h t (List.mem_cons_of_mem s ht)))) ?_
      exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)

/-- Exact finite-product Haar factorization, with signed coefficients and
explicit support on the original carrier. No positivity premise appears. -/
theorem haar_product {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (hd : BlockDisjoint blocks p q) :
    quaternionHaar blocks (polyMul p q) ≈ quaternionHaar blocks p * quaternionHaar blocks q :=
  polynomial_factor blocks p q (fun s hs t ht => haarMono_product (hp s hs) (hq t ht) (hd s hs t ht))

end YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization

#print axioms YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization.blockMoment_zero
#print axioms YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization.blockMoment_product
#print axioms YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization.haarMono_product
#print axioms YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization.BlockDisjoint
#print axioms YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization.haar_product
