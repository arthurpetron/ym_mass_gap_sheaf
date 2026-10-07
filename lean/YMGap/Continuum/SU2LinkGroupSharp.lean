/-
# Sharper link-KP grouping constant: `(3/2)^24` instead of `(5/3)^24`

ADDITIVE (no edits to the Prover's files). In `Z4PolymerKP.z4_hgroup` the per-plaquette piece
`Π_{x ∋ q}(1 + η^{|x|})` is bounded by `1 + 2Σ ≤ 5/3`, using `Σ = Σ_{x∋q} η^{|x|} ≤ 1/3` (the 625ⁿ animal
count times `η = 1/2500`). Here the exp-free inequality `Π(1+δ_i)·(1 − Σδ_i) ≤ 1` gives
`Π ≤ 1/(1 − Σ) ≤ 3/2`. The grouping constant drops from `(5/3)^24 ≈ 2.1·10⁵` to `(3/2)^24 ≈ 1.7·10⁴`.

* `prod_inv`      : `Π(1+δ)·(1 + −Σδ) ≤ 1` for `δ ≥ 0`.
* `piece_le`      : `Σδ ≤ 1/3 → Π(1+δ) ≤ 3/2`.
* `z4_hgroup_sharp`, `hgroupL_sharp` : the Prover's grouping bounds with `three2 = 3/2` in place of `five3`.
-/

import YMGap.Continuum.SU2LinkGasBox

namespace YMGap.Continuum.SU2LinkGroupSharp

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SignedPolymerKP (le_of_eqv_add)
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.Z4PolymerKP
open YMGap.Continuum.BddLatticeAnimal (BddLattice)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

def three2 : Q' := Q'.mkPos 3 2 (by decide)

section
variable {α : Type} (δ : α → Q') (hδ : ∀ x, (0 : Q') ≤ δ x)

include hδ in
theorem prod_inv : ∀ l : List α, prodm (fun x => 1 + δ x) l * (1 + -(sumd δ l)) ≤ 1
  | [] => show (1 : Q') * (1 + -0) ≤ 1 by decide
  | x :: l => by
    let P := prodm (fun x => 1 + δ x) l
    let S := sumd δ l
    have hP : (0 : Q') ≤ P := prodm_nonneg (fun x => 1 + δ x)
      (fun y => Q'.add_le_self_of_nonneg _ _ (hδ y)) l
    have hS : (0 : Q') ≤ S := sumd_nonneg δ hδ l
    have hX : (0 : Q') ≤ P * (δ x * δ x + δ x * S) :=
      Q'.mul_nonneg _ _ hP (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (hδ x) (hδ x)) (Q'.mul_nonneg _ _ (hδ x) hS))
    show (1 + δ x) * P * (1 + -(δ x + S)) ≤ 1
    let V := PolyExpr.var
    refine Q'.le_trans' _ _ _ (le_of_eqv_add (S := P * (δ x * δ x + δ x * S)) ?_ hX) (prod_inv l)
    exact poly_identity_of_normal_eq (V 0 * (.const 1 + -V 2))
      ((.const 1 + V 1) * V 0 * (.const 1 + -(V 1 + V 2)) + V 0 * (V 1 * V 1 + V 1 * V 2)) (by decide)
      (fun | 0 => P | 1 => δ x | _ => S)

include hδ in
theorem piece_le (l : List α) (h : sumd δ l ≤ third) : prodm (fun x => 1 + δ x) l ≤ three2 := by
  let P := prodm (fun x => 1 + δ x) l
  have hP : (0 : Q') ≤ P := prodm_nonneg (fun x => 1 + δ x)
    (fun y => Q'.add_le_self_of_nonneg _ _ (hδ y)) l
  let t : Q' := Q'.mkPos 2 3 (by decide)
  have ht : t ≤ 1 + -(sumd δ l) :=
    Q'.le_trans' _ _ _ (by decide : t ≤ 1 + -third) (Q'.add_le_add_left _ _ _ (Q'.neg_le_neg h))
  have h1 : P * t ≤ 1 :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ ht hP) (prod_inv δ hδ l)
  have e : P.eqv (P * t * three2) := by
    let V := PolyExpr.var
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv P)) (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (by decide : (1 : Q').eqv (t * three2))) ?_)
    exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) (V 0 * V 1 * V 2) (by decide)
      (fun | 0 => P | 1 => t | _ => three2)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e) ?_
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ h1 (by decide))
    (Q'.le_of_eqv (Q'.one_mul_eqv _))
end

variable {BL : BddLattice}

/-- **Sharper `hgroup`** (`3/2` per covering plaquette). -/
theorem z4_hgroup_sharp (hD : BL.D = 24) (d : PL BL) (B : Z4BoxGas BL) (a : Poly BL) :
    prodm (fun x => 1 + etaZ ^ sz x) (B.polys.filter (shareB a)) ≤ three2 ^ sz a := by
  let L := B.polys.filter (shareB a)
  have hf : ∀ x : Poly BL, (1 : Q') ≤ 1 + etaZ ^ sz x :=
    fun x => Q'.add_le_self_of_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)
  have hasg : ∀ x, x ∈ L → asg a d x ∈ a := fun x hx => (asg_spec a d x (mem_filter' _ hx).2).2
  refine Q'.le_trans' _ _ _ (group_le _ hf (asg a d) a L hasg) ?_
  have hpiece : ∀ q, prodm (fun x => 1 + etaZ ^ sz x)
      (L.filter (fun x => decide (asg a d x = q))) ≤ three2 := fun q => by
    let Lq := L.filter (fun x => decide (asg a d x = q))
    have hmemB : ∀ X, X ∈ Lq → X ∈ B.polys ∧ q ∈ X := fun X hX => by
      have h1 := mem_filter' _ hX
      have h2 := mem_filter' _ h1.1
      have hq : asg a d X = q := by simpa using h1.2
      exact ⟨h2.1, hq ▸ (asg_spec a d X h2.2).1⟩
    have hS : sumd δ Lq ≤ geoS B.N :=
      class_sum hD q B.N Lq (pairwise_filter _ _ (pairwise_filter _ _ B.distinct))
        (fun X hX => ⟨rfl, (hmemB X hX).2, B.nodup X (hmemB X hX).1, B.conn X (hmemB X hX).1⟩)
        (fun X hX => B.size_ok X (hmemB X hX).1)
    exact piece_le δ δ_nonneg Lq (Q'.le_trans' _ _ _ hS (geom_quarter B.N))
  have h32 : (1 : Q') ≤ three2 := by decide
  refine Q'.le_trans' _ _ _ (prodm_mono_pt _ (fun _ => three2)
    (fun q => prodm_nonneg _ hf _) hpiece a) ?_
  rw [pow_const_prodm]
  have hlen : a.length ≤ sz a := by
    cases a with
    | nil => exact Nat.zero_le _
    | cons _ _ => exact Nat.le_refl _
  exact YMGap.Continuum.SignedPolymerKP.pow_mono_exp h32 hlen

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.Z4TorusPolymerKP
open YMGap.Continuum.PolymerDecayZ4 (prodm_sub_le)
open YMGap.Continuum.SU2PolymerIdentity (incL gas)
open YMGap.Continuum.SU2LinkGasGeometry
open YMGap.Continuum.SU2LinkGasBox

/-- **Sharper link grouping bound**: `(3/2)^{24|a|}`. -/
theorem hgroupL_sharp (N : Nat) (P : List Z4Plaq) (hP : P.Nodup)
    (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N) (d0 : Z4Plaq) (a : List Z4Plaq) :
    prodm (fun x => 1 + etaZ ^ sz (BL := torusChain N) x) ((gas N P).filter (incL N a)) ≤
      three2 ^ (24 * sz (BL := torusChain N) a) := by
  have hf : ∀ x : List Z4Plaq, (1 : Q') ≤ 1 + etaZ ^ sz (BL := torusChain N) x :=
    fun x => Q'.add_le_self_of_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)
  refine Q'.le_trans' _ _ _ (prodm_sub_le _ hf _ ((gas N P).filter (shareB (BL := torusChain N) (nbA N a)))
    ((gas_nodup N P hP).sublist List.filter_sublist) fun x hx => ?_) ?_
  · obtain ⟨hxg, hxi⟩ := List.mem_filter.mp hx
    obtain ⟨p, hp, q, hq, e⟩ := (incL_iff N a x).mp hxi
    have hqb := hbox q ((gas_inv N P hP x hxg).2.2 q hq)
    refine List.mem_filter.mpr ⟨hxg, (shareB_iff _ _).mpr ⟨q, ?_, hq⟩⟩
    exact List.mem_flatMap.mpr ⟨p, hp, mem_nb N hqb e⟩
  · exact Q'.le_trans' _ _ _ (z4_hgroup_sharp rfl d0 (linkBox N P hP hbox) (nbA N a))
      (pow_mono_exp (by decide) (sz_nbA N a))

end YMGap.Continuum.SU2LinkGroupSharp

#print axioms YMGap.Continuum.SU2LinkGroupSharp.prod_inv
#print axioms YMGap.Continuum.SU2LinkGroupSharp.z4_hgroup_sharp
#print axioms YMGap.Continuum.SU2LinkGroupSharp.hgroupL_sharp
