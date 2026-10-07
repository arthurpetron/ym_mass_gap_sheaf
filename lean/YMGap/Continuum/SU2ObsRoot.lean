/-
# R1 commit 13: the (1+χ)(c₀+f) factorisation and the one-root decomposition

ADDITIVE.  **Labels:** strong coupling, heat-kernel (spin-truncated), not Wilson.  Also true for
U(1), so not gap evidence.  The Wilson counterpart of the polymer decay is Realizer's
`SU2WilsonLinkDecay`.  An observable decay for Wilson needs the same insertion over T_K's split,
which is left for later.

* `obs_factor`: `(1 + χ_r)(c₀ + f_r) ≅ c₀ + (f_r + χ_r + χ_r f_r)` as RatPolys, using c₀ ≈ 1
  (this is the c₀χ ≅ χ identification).
* `ZObs_factor`: `ZObs S ≈ ∫ Π_{r∈P} [r∈S ? (1+χ_r)(c₀+f_r) : (c₀+f_r)]`.  So
  ZObs S / polyPartition is the genuine Gibbs expectation ⟨Π_{r∈S}(1+χ_r)⟩ of the heat-kernel
  measure.  This makes the commit-12 expectation exact, not docs-only.
* `root_split`: for a block B of pairwise-incompatible polymers,
  Ξ(G) ≈ Ξ(G∖B) + Σ_{a∈B} z_a Ξ((G∖B) ∩ cpt a).
* `one_point_root`: `ZObs[p] − Z ≈ Σ_{a∈gas, p∈a} (z^p_a − z_a)·Ξ(z; rest ∩ cpt a)`, where
  rest = the gas polymers avoiding p.
-/

import YMGap.Continuum.SU2ObsInsertion

namespace YMGap.Continuum.SU2ObsRoot

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics (RatPolyCoeffEqv.mul_one)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarL1Activity (prodPoly fPoly)
open YMGap.Continuum.SU2ClusterExplore (W Lk adj)
open YMGap.Continuum.SU2HaarAlgebra (sm sm_congr)
open YMGap.Continuum.SignedPolymerKP (Xi cpt)
open YMGap.Continuum.PolymerChainDecay (Xi_perm)
open YMGap.Continuum.SU2PolymerIdentity (incL gas Xi_block)
open YMGap.Continuum.SU2LinkGasGeometry (incL_iff adj_iff incL_symm)
open YMGap.Continuum.SU2LinkKP (Xi_congr)
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (coeffW coeffW_zero_eqv)
open YMGap.Continuum.SU2ObsInsertion

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

/-! ## 1. The factorisation (c₀χ ≅ χ) -/

theorem smul_near_one {c : Q'} (hc : c.eqv 1) (p : RatPoly) : RatPolyCoeffEqv (polySmul c p) p :=
  fun weight => Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight c p)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hc) (Q'.one_mul_eqv _))

theorem const_mul (c : Q') (p : RatPoly) : RatPolyCoeffEqv (polyMul (polyConst c) p) (polySmul c p) := by
  intro weight
  unfold polyMul polyConst
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact Q'.eqv_refl _

variable (w : Q') (M : Nat) (links : List Z4Link) (N : Nat)

abbrev c0 : Q' := coeffW w 0 * 1
theorem c0_eqv : (c0 w).eqv 1 := Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (coeffW_zero_eqv w)

abbrev fP (r : Z4Plaq) : RatPoly := fPoly w links N r M

/-- **c₀χ ≅ χ identification (PROVED):** `(1+χ_r)(c₀+f_r) ≅ c₀ + ((f_r + χ_r) + χ_r f_r)`. -/
theorem obs_factor (r : Z4Plaq) :
    RatPolyCoeffEqv (polyMul (polyAdd polyOne (chi links N r)) (polyAdd (polyConst (c0 w)) (fP w M links N r)))
      (polyAdd (polyConst (c0 w)) (polyAdd (polyAdd (fP w M links N r) (chi links N r))
        (polyMul (chi links N r) (fP w M links N r)))) := by
  let X := polyAdd (polyConst (c0 w)) (fP w M links N r)
  let χ := chi links N r
  let f := fP w M links N r
  -- (1+χ)X ≅ X·1 + X·χ ≅ X + χX
  have h1 : RatPolyCoeffEqv (polyMul (polyAdd polyOne χ) X) (polyAdd X (polyMul χ X)) :=
    (RatPolyCoeffEqv.mul_comm _ _).trans ((RatPolyCoeffEqv.mul_add_right X polyOne χ).trans
      (RatPolyCoeffEqv.add (RatPolyCoeffEqv.mul_one X) (RatPolyCoeffEqv.mul_comm X χ)))
  -- χX ≅ χc₀ + χf ≅ χ + χf
  have h2 : RatPolyCoeffEqv (polyMul χ X) (polyAdd χ (polyMul χ f)) :=
    (RatPolyCoeffEqv.mul_add_right χ _ _).trans (RatPolyCoeffEqv.add
      ((RatPolyCoeffEqv.mul_comm _ _).trans ((const_mul _ χ).trans (smul_near_one (c0_eqv w) χ)))
      (RatPolyCoeffEqv.refl _))
  refine h1.trans ((RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl X) h2).trans ?_)
  refine (RatPolyCoeffEqv.add_assoc _ _ _).trans (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _) ?_)
  exact (RatPolyCoeffEqv.add_assoc _ _ _).symm

/-- The genuine observable-weighted integrand factor. -/
def obsW (S : List Z4Plaq) (r : Z4Plaq) : RatPoly :=
  if r ∈ S then polyMul (polyAdd polyOne (chi links N r)) (polyAdd (polyConst (c0 w)) (fP w M links N r))
  else polyAdd (polyConst (c0 w)) (fP w M links N r)

theorem obsW_eqv (S : List Z4Plaq) (r : Z4Plaq) :
    RatPolyCoeffEqv (obsW w M links N S r) (W (gObs w M links N S) (c0 w) r) := by
  unfold obsW
  show RatPolyCoeffEqv _ (polyAdd (polyConst (c0 w)) (gObs w M links N S r))
  unfold gObs
  split
  · exact obs_factor w M links N r
  · exact RatPolyCoeffEqv.refl _

theorem prod_congr (F G : Z4Plaq → RatPoly) (h : ∀ r, RatPolyCoeffEqv (F r) (G r)) :
    ∀ P : List Z4Plaq, RatPolyCoeffEqv (prodPoly F P) (prodPoly G P)
  | [] => RatPolyCoeffEqv.refl _
  | r :: P => RatPolyCoeffEqv.mul (h r) (prod_congr F G h P)

/-- **`ZObs S` is the genuine observable-weighted heat-kernel integral (PROVED).** -/
theorem ZObs_factor (P S : List Z4Plaq) :
    (ZObs w M links N P S).eqv (quaternionHaar links.length (prodPoly (obsW w M links N S) P)) :=
  Q'.eqv_symm (YMGap.Continuum.SU2CharacterHaarBound.haar_coeff
    (prod_congr _ _ (obsW_eqv w M links N S) P) _)

/-! ## 2. One-root decomposition -/

theorem sm_sub {β : Type} (f g : β → Q') : ∀ l : List β,
    (sm f l + -(sm g l)).eqv (sm (fun a => f a + -g a) l)
  | [] => by
    show ((0 : Q') + -0).eqv 0
    decide
  | a :: l => by
    refine Q'.eqv_trans _ _ _ ?_ (Q'.add_eqv_congr' (Q'.eqv_refl _) (sm_sub f g l))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 + V 1 + -(V 2 + V 3)) (V 0 + -V 2 + (V 1 + -V 3)) (by decide)
      (fun | 0 => f a | 1 => sm f l | 2 => g a | _ => sm g l)

theorem root_split (z : List Z4Plaq → Q') (B : List Z4Plaq → Bool) (G : List (List Z4Plaq))
    (hB : ∀ a, a ∈ G → B a = true → ∀ b, b ∈ G → B b = true → incL N a b = true) :
    (Xi z (incL N) G).eqv (Xi z (incL N) (G.filter (fun x => !B x)) +
      sm (fun a => z a * Xi z (incL N) ((G.filter (fun x => !B x)).filter (cpt (incL N) a)))
        (G.filter B)) := by
  refine Q'.eqv_trans _ _ _ (Xi_perm z (incL N) (incL_symm N) (List.filter_append_perm B G).symm) ?_
  exact Xi_block N z _ _ fun a ha b hb =>
    hB a (List.mem_filter.mp ha).1 (List.mem_filter.mp ha).2 b (List.mem_filter.mp hb).1
      (List.mem_filter.mp hb).2

theorem adj_self (p : Z4Plaq) : adj N p p = true :=
  (adj_iff N p p).mpr ⟨_, List.mem_cons_self, List.mem_cons_self⟩

theorem inc_of_mem {p : Z4Plaq} {a b : List Z4Plaq} (ha : p ∈ a) (hb : p ∈ b) : incL N a b = true :=
  (incL_iff N a b).mpr ⟨p, ha, p, hb, adj_self N p⟩

abbrev hasP (p : Z4Plaq) (a : List Z4Plaq) : Bool := decide (p ∈ a)

/-- **One-point root formula (PROVED).**  `Zp = ZObs[p] − Z` is a sum over the gas polymers
through p, with weight (z^p_a − z_a) times Ξ of the compatible polymers that avoid p. -/
theorem one_point_root (P : List Z4Plaq) (hL : ∀ r ∈ P, Lk links N r) (p : Z4Plaq) :
    let G := gas N P
    let R := G.filter (fun x => !hasP p x)
    (ZObs w M links N P [p] + -ZObs w M links N P []).eqv
      (sm (fun a => (zObs w M links N [p] a + -zObs w M links N [] a) *
        Xi (zObs w M links N []) (incL N) (R.filter (cpt (incL N) a))) (G.filter (hasP p))) := by
  intro G R
  have hB : ∀ a, a ∈ G → hasP p a = true → ∀ b, b ∈ G → hasP p b = true → incL N a b = true :=
    fun a _ ha b _ hb => inc_of_mem N (of_decide_eq_true ha) (of_decide_eq_true hb)
  have avoid : ∀ x, x ∈ R → ∀ r, r ∈ x → r ∉ [p] := fun x hx r hr hrp => by
    have h := (List.mem_filter.mp hx).2
    rw [List.mem_singleton.mp hrp] at hr
    simp only [hasP, decide_eq_true hr] at h
    exact absurd h (by decide)
  have congr : ∀ L : List (List Z4Plaq), (∀ x, x ∈ L → x ∈ R) →
      Xi (zObs w M links N [p]) (incL N) L = Xi (zObs w M links N []) (incL N) L := fun L hL =>
    Xi_congr _ _ _ L.length L (Nat.le_refl _) fun a ha => zObs_off w M links N [p] a (avoid a (hL a ha))
  have e1 := Q'.eqv_trans _ _ _ (ZObs_eq_Xi w M links N P [p] hL)
    (root_split N (zObs w M links N [p]) (hasP p) G hB)
  have e0 := Q'.eqv_trans _ _ _ (ZObs_eq_Xi w M links N P [] hL)
    (root_split N (zObs w M links N []) (hasP p) G hB)
  rw [congr R (fun _ h => h)] at e1
  have e1' : (ZObs w M links N P [p]).eqv (Xi (zObs w M links N []) (incL N) R +
      sm (fun a => zObs w M links N [p] a * Xi (zObs w M links N []) (incL N) (R.filter (cpt (incL N) a)))
        (G.filter (hasP p))) := by
    refine Q'.eqv_trans _ _ _ e1 (Q'.add_eqv_congr' (Q'.eqv_refl _) (sm_congr _ fun a _ => ?_))
    rw [congr _ (fun x hx => (List.mem_filter.mp hx).1)]
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' e1' (Q'.neg_eqv_congr _ _ e0)) ?_
  let X := fun a => Xi (zObs w M links N []) (incL N) (R.filter (cpt (incL N) a))
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_trans _ _ _
    (sm_sub (fun a => zObs w M links N [p] a * X a) (fun a => zObs w M links N [] a * X a) _)
    (sm_congr _ fun a _ => ?_))
  · let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 + V 1 + -(V 0 + V 2)) (V 1 + -V 2) (by decide)
      (fun | 0 => Xi (zObs w M links N []) (incL N) R | 1 => sm _ (G.filter (hasP p)) | _ => sm _ (G.filter (hasP p)))
  · let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * V 2 + -(V 1 * V 2)) ((V 0 + -V 1) * V 2) (by decide)
      (fun | 0 => zObs w M links N [p] a | 1 => zObs w M links N [] a
           | _ => Xi (zObs w M links N []) (incL N) (R.filter (cpt (incL N) a)))

end YMGap.Continuum.SU2ObsRoot
