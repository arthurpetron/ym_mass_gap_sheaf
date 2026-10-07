/-
# Torus RP, commit 1: the abstract half-split reflection-positivity core

The setting is `SU(2)^(a+a)`. Blocks `0..a-1` are the positive half; block `a+i` is the reflection of block `i`.
The reflection Θ acts on polynomials as the block translation `sh := shiftPoly a`. (The temporal links crossing
Θ are gauge-fixed to `1`, and orientation conjugation is absorbed into the identification; see
`docs/J04-TORUS-RP-SCOPE-2026-10-07.md`.)

* `sh_mul`: `sh (p·q) = sh p · sh q` (literal list equality).
* `kern L = Σ_{(c,A)∈L} c · A · sh A`: a **reflection-positive kernel**. `RPK a W` holds when `W` is
  Haar-PE to such a sum with every `c ≥ 0` and every `A` on the positive half.
* `rpk_pos`: `RPK a W → 0 ≤ ∫_{a+a} F · sh F · W` for every positive-half `F`. The proof uses `haar_factor`,
  which turns each term into `c · (∫ F A)²`.
* Closure: `rpk_one`, `rpk_append` (sums), `rpk_smul` (scalars `≥ 0`), `rpk_mul` (products).
* `rp_full`: `W ≡ W₊ · sh W₊ · W_c` with `W_c ∈ RPK` gives `0 ≤ ∫ sh F · F · W`.
-/

import YMGap.Continuum.SU2HaarAlgebra
import YMGap.Continuum.SU2MultiLinkHaarFactorization

namespace YMGap.Continuum.SU2TorusRPCore

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarAlgebra (PE pe_refl pe_symm pe_trans pe_haar pe_mulL pe_mulR pe_append pe_comm
  pe_assoc pe_const sm)
open YMGap.Continuum.SU2MultiLinkHaarFactorization (shiftPoly haar_factor)

/-! ## Shift and support -/

theorem monoMul_rep : ∀ (k : Nat) (m1 m2 : List Nat),
    monoMul (List.replicate k 0 ++ m1) (List.replicate k 0 ++ m2) = List.replicate k 0 ++ monoMul m1 m2
  | 0, _, _ => rfl
  | k + 1, m1, m2 => by
    show (0 + 0) :: monoMul (List.replicate k 0 ++ m1) (List.replicate k 0 ++ m2) = _
    rw [monoMul_rep k]; rfl

theorem sh_mul (a : Nat) (p q : RatPoly) :
    shiftPoly a (polyMul p q) = polyMul (shiftPoly a p) (shiftPoly a q) := by
  simp only [shiftPoly, polyMul, List.map_flatMap, List.flatMap_map, List.map_map]
  congr 1; funext s; congr 1; funext t
  simp [monoMul_rep]

theorem length_monoMul : ∀ m1 m2 : List Nat, (monoMul m1 m2).length = max m1.length m2.length
  | [], m2 => by simp [monoMul]
  | _ :: _, [] => by simp [monoMul]
  | x :: xs, y :: ys => by
    show (monoMul xs ys).length + 1 = _
    rw [length_monoMul xs ys]; simp [Nat.succ_max_succ]

/-- Supported on the positive half (the first `a` blocks). -/
def Sup (a : Nat) (p : RatPoly) : Prop := ∀ s, s ∈ p → s.1.length ≤ 4 * a

theorem sup_mul {a : Nat} {p q : RatPoly} (hp : Sup a p) (hq : Sup a q) : Sup a (polyMul p q) := by
  intro s hs
  simp only [polyMul, List.mem_flatMap, List.mem_map] at hs
  obtain ⟨x, hx, y, hy, rfl⟩ := hs
  show (monoMul x.1 y.1).length ≤ _
  rw [length_monoMul]; exact Nat.max_le.mpr ⟨hp x hx, hq y hy⟩

theorem sup_one (a : Nat) : Sup a polyOne := fun s hs => by
  simp [polyOne] at hs; subst hs; simp

/-! ## PE helpers -/

section
variable (n : Nat)

theorem pe_swap4 (X Y Z W : RatPoly) :
    PE n (polyMul (polyMul X Y) (polyMul Z W)) (polyMul (polyMul X Z) (polyMul Y W)) :=
  pe_trans n (pe_assoc n X Y _) (pe_trans n (pe_mulL n X (pe_symm n (pe_assoc n Y Z W)))
    (pe_trans n (pe_mulL n X (pe_mulR n W (pe_comm n Y Z)))
      (pe_trans n (pe_mulL n X (pe_assoc n Z Y W)) (pe_symm n (pe_assoc n X Z _)))))

theorem pe_flatMap {β : Type} (f g : β → RatPoly) : ∀ l : List β, (∀ x ∈ l, PE n (f x) (g x)) →
    PE n (l.flatMap f) (l.flatMap g)
  | [], _ => pe_refl n _
  | x :: l, h => by
    simp only [List.flatMap_cons]
    exact pe_append n (h x (List.mem_cons_self ..)) (pe_flatMap f g l fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem mul_flatMapL {β : Type} (f : β → RatPoly) (l : List β) (Y : RatPoly) :
    polyMul (l.flatMap f) Y = l.flatMap fun x => polyMul (f x) Y := by
  simp only [polyMul, List.flatMap_assoc]

theorem pe_mul_flatMapR {β : Type} (X : RatPoly) (f : β → RatPoly) (l : List β) :
    PE n (polyMul X (l.flatMap f)) (l.flatMap fun x => polyMul X (f x)) := by
  refine pe_trans n (pe_comm n _ _) ?_
  rw [mul_flatMapL]
  exact pe_flatMap n _ _ l fun x _ => pe_comm n _ _

theorem haar_flatMap {β : Type} (f : β → RatPoly) : ∀ l : List β,
    (quaternionHaar n (l.flatMap f)).eqv (sm (fun x => quaternionHaar n (f x)) l)
  | [] => Q'.eqv_refl _
  | x :: l => by
    simp only [List.flatMap_cons]
    exact Q'.eqv_trans _ _ _ (YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_append n _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_flatMap f l))

theorem haar_const (c : Q') (X : RatPoly) :
    (quaternionHaar n (polyMul (polyConst c) X)).eqv (c * quaternionHaar n X) := by
  have e : polyMul (polyConst c) X = polySmul c X := by
    simp [polyMul, polyConst, polySmul, monoMul]
  rw [e]; exact YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polySmul n c X

theorem sm_nonneg {β : Type} (f : β → Q') : ∀ l : List β, (∀ x ∈ l, (0 : Q') ≤ f x) → (0 : Q') ≤ sm f l
  | [], _ => Q'.le_refl' 0
  | x :: l, h => Q'.zero_le_add _ _ (h x (List.mem_cons_self ..))
      (sm_nonneg f l fun y hy => h y (List.mem_cons_of_mem _ hy))

end

/-! ## Kernels -/

/-- One kernel term `c · A · Θ(A)`. -/
def term (a : Nat) (x : Q' × RatPoly) : RatPoly :=
  polyMul (polyConst x.1) (polyMul x.2 (shiftPoly a x.2))

def kern (a : Nat) (L : List (Q' × RatPoly)) : RatPoly := L.flatMap (term a)

def Good (a : Nat) (L : List (Q' × RatPoly)) : Prop := ∀ x ∈ L, (0 : Q') ≤ x.1 ∧ Sup a x.2

/-- Reflection-positive kernel on `SU(2)^(a+a)`. -/
def RPK (a : Nat) (W : RatPoly) : Prop := ∃ L, Good a L ∧ PE (a + a) W (kern a L)

theorem term_pos (a : Nat) (F : RatPoly) (hF : Sup a F) (x : Q' × RatPoly) (hx : (0 : Q') ≤ x.1 ∧ Sup a x.2) :
    (0 : Q') ≤ quaternionHaar (a + a) (polyMul (polyMul F (shiftPoly a F)) (term a x)) := by
  let n := a + a
  let G := polyMul F x.2
  have h1 : PE n (polyMul (polyMul F (shiftPoly a F)) (term a x))
      (polyMul (polyConst x.1) (polyMul G (shiftPoly a G))) := by
    refine pe_trans n (pe_comm n _ _) (pe_trans n (pe_assoc n _ _ _) (pe_mulL n _ ?_))
    refine pe_trans n (pe_comm n _ _) (pe_trans n (pe_swap4 n _ _ _ _) ?_)
    rw [sh_mul]; exact pe_refl n _
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (Q'.eqv_symm (pe_haar n h1)))
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (Q'.eqv_symm (haar_const n _ _)))
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (Q'.eqv_symm
    (Q'.mul_eqv_congr_left _ _ _ (haar_factor a a G (sup_mul hF hx.2) G))))
  exact Q'.mul_nonneg _ _ hx.1 (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _)

/-- **Abstract reflection positivity.** -/
theorem rpk_pos {a : Nat} {W : RatPoly} (hW : RPK a W) (F : RatPoly) (hF : Sup a F) :
    (0 : Q') ≤ quaternionHaar (a + a) (polyMul (polyMul F (shiftPoly a F)) W) := by
  obtain ⟨L, hL, hPE⟩ := hW
  let n := a + a
  have h1 := pe_haar n (pe_trans n (pe_mulL n (polyMul F (shiftPoly a F)) hPE) (pe_mul_flatMapR n _ (term a) L))
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (Q'.eqv_symm h1))
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (Q'.eqv_symm (haar_flatMap n _ L)))
  exact sm_nonneg _ L fun x hx => term_pos a F hF x (hL x hx)

/-! ## Closure -/

theorem rpk_congr {a : Nat} {W W' : RatPoly} (h : PE (a + a) W W') (hW : RPK a W') : RPK a W := by
  obtain ⟨L, hL, hP⟩ := hW; exact ⟨L, hL, pe_trans _ h hP⟩

open YMGap.Continuum.SU2MultiLinkHaarFactorization (exponentAt_drop prefix_congr allZero_iff
  exponentAt_replicate_append) in
theorem mono_congr (n : Nat) {m m' : List Nat} (h : ∀ i, exponentAt m i = exponentAt m' i) :
    quaternionHaarMono n m = quaternionHaarMono n m' := by
  unfold quaternionHaarMono
  have hz : allZero (m.drop (4 * n)) = allZero (m'.drop (4 * n)) := by
    apply Bool.eq_iff_iff.mpr
    rw [allZero_iff, allZero_iff]
    simp only [exponentAt_drop, h]
  rw [hz, prefix_congr n m m' (fun i _ => h i)]

theorem pe_zeros (n k : Nat) : PE n [(List.replicate k 0, (1 : Q'))] polyOne := fun m => by
  show ((1 : Q') * quaternionHaarMono n (monoMul m (List.replicate k 0)) + 0).eqv
    ((1 : Q') * quaternionHaarMono n (monoMul m []) + 0)
  rw [mono_congr n (m := monoMul m (List.replicate k 0)) (m' := monoMul m []) (fun i => by
    rw [YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.exponentAt_monoMul,
      YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.exponentAt_monoMul]
    rw [show List.replicate k 0 = List.replicate k 0 ++ [] by simp,
      YMGap.Continuum.SU2MultiLinkHaarFactorization.exponentAt_replicate_append]
    split <;> simp [exponentAt])]
  exact Q'.eqv_refl _

theorem rpk_one (a : Nat) : RPK a polyOne := by
  refine ⟨[(1, polyOne)], fun x hx => ?_, ?_⟩
  · simp at hx; subst hx; exact ⟨by decide, sup_one a⟩
  · show PE _ polyOne (term a (1, polyOne) ++ [])
    rw [List.append_nil]
    refine pe_symm _ (pe_trans _ (pe_const _ 1 (Q'.eqv_refl 1) _) ?_)
    refine pe_trans _ (pe_const _ 1 (Q'.eqv_refl 1) _) ?_
    show PE _ [(List.replicate (4 * a) 0 ++ [], (1 : Q'))] polyOne
    rw [List.append_nil]; exact pe_zeros _ (4 * a)

theorem rpk_append {a : Nat} {W V : RatPoly} (hW : RPK a W) (hV : RPK a V) : RPK a (W ++ V) := by
  obtain ⟨L, hL, hP⟩ := hW; obtain ⟨M, hM, hQ⟩ := hV
  refine ⟨L ++ M, fun x hx => ?_, ?_⟩
  · rcases List.mem_append.mp hx with h | h
    · exact hL x h
    · exact hM x h
  · rw [kern, List.flatMap_append]; exact pe_append _ hP hQ

theorem const_mul (c d : Q') : polyMul (polyConst c) (polyConst d) = polyConst (c * d) := rfl

theorem rpk_smul {a : Nat} {W : RatPoly} (d : Q') (hd : (0 : Q') ≤ d) (hW : RPK a W) :
    RPK a (polyMul (polyConst d) W) := by
  obtain ⟨L, hL, hP⟩ := hW
  refine ⟨L.map fun x => (d * x.1, x.2), fun x hx => ?_, ?_⟩
  · simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨Q'.mul_nonneg _ _ hd (hL y hy).1, (hL y hy).2⟩
  · refine pe_trans _ (pe_mulL _ _ hP) (pe_trans _ (pe_mul_flatMapR _ _ _ L) ?_)
    rw [kern, List.flatMap_map]
    refine pe_flatMap _ _ _ L fun x _ => ?_
    exact pe_trans _ (pe_symm _ (pe_assoc _ _ _ _)) (by rw [const_mul]; exact pe_refl _ _)

theorem term_mul (a : Nat) (x y : Q' × RatPoly) :
    PE (a + a) (polyMul (term a x) (term a y)) (term a (x.1 * y.1, polyMul x.2 y.2)) := by
  refine pe_trans _ (pe_swap4 _ _ _ _ _) ?_
  rw [const_mul]
  refine pe_mulL _ _ (pe_trans _ (pe_swap4 _ _ _ _ _) ?_)
  rw [sh_mul]; exact pe_refl _ _

theorem rpk_mul {a : Nat} {W V : RatPoly} (hW : RPK a W) (hV : RPK a V) : RPK a (polyMul W V) := by
  obtain ⟨L, hL, hP⟩ := hW; obtain ⟨M, hM, hQ⟩ := hV
  refine ⟨L.flatMap fun x => M.map fun y => (x.1 * y.1, polyMul x.2 y.2), fun z hz => ?_, ?_⟩
  · simp only [List.mem_flatMap, List.mem_map] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    exact ⟨Q'.mul_nonneg _ _ (hL x hx).1 (hM y hy).1, sup_mul (hL x hx).2 (hM y hy).2⟩
  · refine pe_trans _ (pe_mulR _ _ hP) (pe_trans _ (pe_mulL _ _ hQ) ?_)
    rw [kern, mul_flatMapL]; simp only [kern, List.flatMap_assoc]
    refine pe_flatMap _ _ _ L fun x _ => pe_trans _ (pe_mul_flatMapR _ _ _ M) ?_
    rw [List.flatMap_map]
    exact pe_flatMap _ _ _ M fun y _ => by
      have := term_mul a x y
      simpa [List.flatMap_cons, List.flatMap_nil] using pe_trans _ this (pe_refl _ _)

/-- **Full abstract RP**: the positive-half weight is absorbed into `F`, and the crossing weight is an RPK. -/
theorem rp_full {a : Nat} (F Wp Wc W : RatPoly) (hF : Sup a F) (hWp : Sup a Wp) (hWc : RPK a Wc)
    (hW : PE (a + a) W (polyMul (polyMul Wp (shiftPoly a Wp)) Wc)) :
    (0 : Q') ≤ quaternionHaar (a + a) (polyMul (polyMul (shiftPoly a F) F) W) := by
  let n := a + a
  have h : PE n (polyMul (polyMul (shiftPoly a F) F) W)
      (polyMul (polyMul (polyMul F Wp) (shiftPoly a (polyMul F Wp))) Wc) := by
    refine pe_trans n (pe_mulR n _ (pe_comm n _ _)) (pe_trans n (pe_mulL n _ hW) ?_)
    refine pe_trans n (pe_symm n (pe_assoc n _ _ _)) (pe_mulR n _ ?_)
    rw [sh_mul]; exact pe_swap4 n _ _ _ _
  exact Q'.le_trans' _ _ _ (rpk_pos hWc _ (sup_mul hF hWp)) (Q'.le_of_eqv (Q'.eqv_symm (pe_haar n h)))

end YMGap.Continuum.SU2TorusRPCore

#print axioms YMGap.Continuum.SU2TorusRPCore.rpk_pos
#print axioms YMGap.Continuum.SU2TorusRPCore.rpk_mul
#print axioms YMGap.Continuum.SU2TorusRPCore.rp_full
