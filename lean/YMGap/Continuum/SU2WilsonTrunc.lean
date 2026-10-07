/-
# R1 commit 23: Wilson truncated χ₁ correlator decay at β_S, ratio form, uniform in K

ADDITIVE.  **Labels:** strong coupling (β_S = 1/(2·10¹²)); Wilson action (Taylor-truncated at K,
uniform in K, N and P); also true for U(1), not gap evidence.  Realizer's Wilson files are
imported, not edited.  This is an instance of the generic `SU2TruncGeneric.trunc_gen`.

* `obs_split`: `(1+χ_r)·T_K(r) ≅ c₀·(1 + gWo_r)` on S, and `T_K(r) ≅ c₀(1+F_r)` off S.
* `ZW_eq`: `ZW P S := ∫ Π_{r∈P} obsTK S r ≈ c₀^{|P|} · Ξ(zW S)`.
* `wilson_trunc_ratio`: `|Zpq/Z − (Zp/Z)(Zq/Z)| ≤ Cw · λ^{ld(q,p)}`, where `Z_S = ZW P S`,
  `Cw = Cg D1 D2 K5` (with Dw = 2·10¹²+3) and λ = 6/7.  The left side is the covariance of
  `1+χ_p` and `1+χ_q`, which equals the covariance of `χ_p` and `χ_q`.
-/

import YMGap.Continuum.SU2TruncGeneric
import YMGap.Continuum.SU2WilsonObsActivity
import YMGap.Continuum.SU2RemovalDecay

namespace YMGap.Continuum.SU2WilsonTrunc

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SignedPolymerKP (Xi cpt)
open YMGap.Continuum.PolymerChainDecay (Good)
open YMGap.Continuum.PolymerLatticeDecay (lam)
open YMGap.Continuum.SU2CharacterHaarBound (haar_coeff)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2ClusterExplore (W Lk)
open YMGap.Continuum.SU2PolymerIdentity (incL gas polymer_identity)
open YMGap.Continuum.SU2WilsonPolymerIdentity (TK FW c0 c0_ge T_split)
open YMGap.Continuum.SU2ObsRoot (smul_near_one const_mul prod_congr)
open YMGap.Continuum.SU2WilsonObsActivity
open YMGap.Continuum.SU2LinkDecaySharpInst (epsS betaS sharp_pass zn_abs_S)
open YMGap.Continuum.Z4PlaqMetric (torusMetric)
open YMGap.Continuum.SU2LinkKP (S)
open YMGap.Continuum.SU2TruncGeneric (Cg trunc_gen)
open YMGap.Continuum.SizeWeightedPolymerKP (sumd)
open YMGap.Continuum.SU2ObsActivity (mu)
open YMGap.Continuum.SU2LinkKPSharp (ML)
open YMGap.Continuum.SU2LinkGroupSharp (three2)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

local infix:50 " ≅ " => RatPolyCoeffEqv

variable (links : List Z4Link) (N : Nat) (K : Nat)

/-! ## Observable integrand and its polymer form -/

def obsTK (S : List Z4Plaq) (r : Z4Plaq) : RatPoly :=
  if r ∈ S then polyMul (polyAdd polyOne (chi links N r)) (TK links N betaS K r) else TK links N betaS K r

theorem factor1 (χ F : RatPoly) :
    polyMul (polyAdd polyOne χ) (polyAdd (polyConst 1) F) ≅ polyAdd (polyConst 1) (polyAdd (polyAdd F χ) (polyMul χ F)) := by
  let X := polyAdd (polyConst 1) F
  have h1 : polyMul (polyAdd polyOne χ) X ≅ polyAdd X (polyMul χ X) :=
    (RatPolyCoeffEqv.mul_comm _ _).trans ((RatPolyCoeffEqv.mul_add_right X polyOne χ).trans
      (RatPolyCoeffEqv.add (RatPolyCoeffEqv.mul_one X) (RatPolyCoeffEqv.mul_comm X χ)))
  have h2 : polyMul χ X ≅ polyAdd χ (polyMul χ F) :=
    (RatPolyCoeffEqv.mul_add_right χ _ _).trans (RatPolyCoeffEqv.add
      ((RatPolyCoeffEqv.mul_comm _ _).trans ((const_mul _ χ).trans (smul_near_one (Q'.eqv_refl 1) χ)))
      (RatPolyCoeffEqv.refl _))
  refine h1.trans ((RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl X) h2).trans ?_)
  refine (RatPolyCoeffEqv.add_assoc _ _ _).trans (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _) ?_)
  exact (RatPolyCoeffEqv.add_assoc _ _ _).symm

theorem obs_split (S : List Z4Plaq) (r : Z4Plaq) :
    obsTK links N K S r ≅ polySmul (c0 betaS K) (W (gWo links N betaS K S) 1 r) := by
  have hT := T_split links N K (β := betaS) (by decide) r
  unfold obsTK
  by_cases h : r ∈ S
  · rw [if_pos h]
    refine (RatPolyCoeffEqv.mul_left _ hT).trans ((RatPolyCoeffEqv.polyMul_smul_right _ _ _).trans
      (RatPolyCoeffEqv.smul _ ?_))
    show _ ≅ polyAdd (polyConst 1) (gWo links N betaS K S r)
    unfold gWo; rw [if_pos h]
    exact factor1 _ _
  · rw [if_neg h]
    show _ ≅ polySmul _ (polyAdd (polyConst 1) (gWo links N betaS K S r))
    unfold gWo; rw [if_neg h]
    exact hT

theorem prodS (S : List Z4Plaq) : ∀ P : List Z4Plaq,
    prodPoly (obsTK links N K S) P ≅ polySmul (c0 betaS K ^ P.length) (prodPoly (W (gWo links N betaS K S) 1) P)
  | [] => (RatPolyCoeffEqv.one_smul _).symm
  | p :: ps => (RatPolyCoeffEqv.mul (obs_split links N K S p) (prodS S ps)).trans
      ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
        ((RatPolyCoeffEqv.smul _ (RatPolyCoeffEqv.polyMul_smul_right _ _ _)).trans
          (RatPolyCoeffEqv.smul_assoc _ _ _)))

/-- The genuine observable-weighted Wilson integral `∫ Π_{r∈P} [(1+χ_r)]_{r∈S} T_K(r)`. -/
def ZW (P S : List Z4Plaq) : Q' := quaternionHaar links.length (prodPoly (obsTK links N K S) P)

theorem ZW_eq (P S : List Z4Plaq) (hL : ∀ p ∈ P, Lk links N p) :
    (ZW links N K P S).eqv (c0 betaS K ^ P.length * Xi (zW links N betaS K S) (incL N) (gas N P)) :=
  Q'.eqv_trans _ _ _ (haar_coeff (prodS links N K S P) _)
    (Q'.eqv_trans _ _ _ (YMGap.Continuum.SU2PolymerActivityBound.haar_smul _ _ _) (Q'.mul_eqv_congr_left _ _ _
      (polymer_identity N links.length links (gWo links N betaS K S) 1 (Q'.eqv_refl 1)
        (fun p => gWo_free links N betaS K S p) P.length P (Nat.le_refl _) hL)))

/-! ## Agreement -/

theorem prod_agree (S S' : List Z4Plaq) : ∀ γ : List Z4Plaq, (∀ r, r ∈ γ → (r ∈ S ↔ r ∈ S')) →
    prodPoly (gWo links N betaS K S) γ = prodPoly (gWo links N betaS K S') γ
  | [], _ => rfl
  | r :: γ, h => by
    show polyMul _ _ = polyMul _ _
    have e : gWo links N betaS K S r = gWo links N betaS K S' r := by
      unfold gWo
      by_cases hr : r ∈ S
      · rw [if_pos hr, if_pos ((h r List.mem_cons_self).mp hr)]
      · rw [if_neg hr, if_neg (fun h' => hr ((h r List.mem_cons_self).mpr h'))]
    rw [e, prod_agree S S' γ (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem zW_agree (S S' γ : List Z4Plaq) (h : ∀ r, r ∈ γ → (r ∈ S ↔ r ∈ S')) :
    zW links N betaS K S γ = zW links N betaS K S' γ := by
  unfold zW; rw [prod_agree links N K S S' γ h]

/-! ## Constants -/

def Dw : Q' := Q'.ofNat 2000000000003
def D1 : Q' := Dw ^ 1 + Dw ^ 0
def D2 : Q' := Dw ^ 2 + Dw ^ 1 + (Dw ^ 1 + Dw ^ 0)
def K5 : Q' := YMGap.Continuum.Z4PolymerKP.five3 ^ 24
/-- `Cw = 2·D1²·K5² + D2·K5` (≈ 3.6·10³⁵ with D1 ≈ 2·10¹², K5 = (5/3)^24 ≈ 2.1·10⁵). -/
def Cw : Q' := Cg D1 D2 K5

theorem pw (c : Q') (s : Nat) : (epsS ^ s * mu ^ s * c ^ (24 * s)).eqv
    ((epsS * mu * c ^ 24) ^ s) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (YMGap.Continuum.SU2LinkKPSharp.pow_mul_eqv c 24 s))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (YMGap.Continuum.Z4PolymerKP.mul_pow' _ _ s))
      (YMGap.Continuum.Z4PolymerKP.mul_pow' _ _ s))

variable (P : List Z4Plaq) (hP : P.Nodup) (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N)
  (hL : ∀ r ∈ P, Lk links N r)

local notation "zz" => zW links N betaS K

include hP hL in
theorem lkc (x : List Z4Plaq) (hx : x ∈ gas N P) :
    ∀ r ∈ x, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N r := fun r hr =>
  YMGap.Continuum.SU2LinkDecayHeat.lk_cover links N r
    (hL r ((YMGap.Continuum.SU2LinkGasBox.gas_inv N P hP x hx).2.2 r hr))

include hP hbox hL in
theorem dif (S1 S2 a : List Z4Plaq) (ha : a ∈ gas N P) :
    Q'.abs (zz S1 a + -zz S2 a) ≤ (Dw ^ S1.length + Dw ^ S2.length) * epsS ^ S N a := by
  have nd := (YMGap.Continuum.SU2LinkGasBox.gas_inv N P hP a ha).2.1
  have hb := fun S' => zW_bound links N betaS K (Dw := Dw) (ε := epsS) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) S' a nd (lkc links N P hP hL a ha)
  rw [YMGap.Continuum.SU2PairKernel.hlen N P hP hbox a ha]
  refine Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.le_trans' _ _ _ (Q'.add_le_add (hb S1)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _)) (hb S2))) (Q'.le_of_eqv ?_))
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0 * V 2 + V 1 * V 2) ((V 0 + V 1) * V 2) (by decide)
    (fun | 0 => Dw ^ S1.length | 1 => Dw ^ S2.length | _ => epsS ^ a.length)

include hP hbox hL in
theorem hz : ∀ x, x ∈ gas N P → Q'.abs (zz [] x) ≤ epsS ^ S N x := fun x hx => by
  show Q'.abs (quaternionHaar _ (prodPoly (gWo links N betaS K []) x)) ≤ _
  rw [gWo_nil, YMGap.Continuum.SU2PairKernel.hlen N P hP hbox x hx]
  exact zn_abs_S links N K x (lkc links N P hP hL x hx)

theorem pw2 (s : Nat) : (epsS ^ s * mu ^ s * three2 ^ (24 * s) * three2 ^ (24 * s)).eqv
    (epsS ^ s * mu ^ s * (three2 * three2) ^ (24 * s)) := by
  let V := PolyExpr.var
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq (V 0 * V 1 * V 2 * V 2) (V 0 * V 1 * (V 2 * V 2))
    (by decide) (fun | 0 => epsS ^ s | 1 => mu ^ s | _ => three2 ^ (24 * s))) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (YMGap.Continuum.Z4PolymerKP.mul_pow' _ _ _)

include hP hbox in
theorem rootK (c : Q') (hc0 : (0 : Q') ≤ epsS * mu * c ^ 24)
    (hc : epsS * mu * c ^ 24 ≤ YMGap.Continuum.SizeWeightedPolymerKP.etaZ) (s : Z4Plaq) :
    sumd (fun a => epsS ^ S N a * mu ^ S N a * c ^ (24 * S N a))
      ((gas N P).filter (YMGap.Continuum.SU2ObsRoot.hasP s)) ≤ K5 :=
  Q'.le_trans' _ _ _ (YMGap.Continuum.PolymerDecayZ4.sumd_mono _ _ (fun a => Q'.le_of_eqv (pw c (S N a))) _)
    (YMGap.Continuum.SU2ObsActivity.root_sum N P hP hbox _ hc0 hc s)

include hP hbox hL in
/-- **Wilson truncated χ₁ correlator decay, ratio form (PROVED; β_S = 1/(2·10¹²); uniform in K, N, P).** -/
theorem wilson_trunc_ratio (p q : Z4Plaq) :
    let Z := ZW links N K P []
    Q'.abs (ZW links N K P [p, q] * Q'.recip Z +
        -((ZW links N K P [p] * Q'.recip Z) * (ZW links N K P [q] * Q'.recip Z))) ≤
      Cw * lam ^ (torusMetric N).ld q p := by
  intro Z
  have hz' := hz links N K P hP hbox hL
  have hG : Good (gas N P) (gas N P) := ⟨YMGap.Continuum.SU2LinkGasBox.gas_nodup N P hP, fun _ h => h⟩
  have henv : ∀ l, Good (gas N P) l → ∀ a, (0 : Q') < Xi (zz []) (incL N) l ∧
      Xi (zz []) (incL N) (l.filter (cpt (incL N) a)) ≤ ML N a * Xi (zz []) (incL N) l := fun l hl a => by
    have h0 := YMGap.Continuum.SU2LinkKPSharp.envL_pos N P hP hbox epsS (by decide) sharp_pass.1 _ hz' l hl
    have h1 := YMGap.Continuum.SU2LinkKPSharp.envL_M N P hP hbox epsS (by decide) sharp_pass.1 _ hz' l a hl
    rw [YMGap.Continuum.SU2LinkKPSharp.Xi_zc N P _ l hl.2] at h0 h1
    rw [YMGap.Continuum.SU2LinkKPSharp.Xi_zc N P _ _ (fun x hx => hl.2 x (List.mem_filter.mp hx).1)] at h1
    exact ⟨h0, h1⟩
  have hM1 : ∀ x, (1 : Q') ≤ ML N x := fun _ =>
    Q'.le_trans' _ _ _ (by decide) (YMGap.Continuum.SU2LinkGasBox.pow_mono_exp (by decide) (Nat.zero_le _))
  have hr1 := rootK N P hP hbox three2 (by decide) (by decide)
  have hr2 : ∀ s : Z4Plaq, sumd (fun a => epsS ^ S N a * mu ^ S N a * ML N a * ML N a)
      ((gas N P).filter (YMGap.Continuum.SU2ObsRoot.hasP s)) ≤ K5 := fun s =>
    Q'.le_trans' _ _ _ (YMGap.Continuum.PolymerDecayZ4.sumd_mono _ _ (fun a => Q'.le_of_eqv (pw2 (S N a))) _)
      (rootK N P hP hbox (three2 * three2) (by decide) (by decide) s)
  have hT := fun y g hy hg R hsep => YMGap.Continuum.SU2RemovalDecay.T_link_decay_sharp N P hP hbox epsS
    (by decide) sharp_pass.2.1 sharp_pass.2.2.1 sharp_pass.2.2.2 sharp_pass.1 _ hz' y g hy hg (gas N P) R hsep hG
  have key := trunc_gen N P hP hbox (zz []) (zz [p]) (zz [q]) (zz [p, q]) p q _ hM1 henv hT epsS D1 D2 K5
    (by decide) (by decide) (by decide) (fun a ha => dif links N K P hP hbox hL [p] [] a ha)
    (fun a ha => dif links N K P hP hbox hL [q] [] a ha) (fun a ha => by
      refine Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.le_trans' _ _ _ (Q'.add_le_add
        (dif links N K P hP hbox hL [p, q] [q] a ha) (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _))
          (dif links N K P hP hbox hL [p] [] a ha))) (Q'.le_of_eqv ?_))
      show Q'.eqv _ ((Dw ^ 2 + Dw ^ 1 + (Dw ^ 1 + Dw ^ 0)) * _)
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq ((V 0 + V 1) * V 4 + (V 2 + V 3) * V 4)
        ((V 0 + V 1 + (V 2 + V 3)) * V 4) (by decide)
        (fun | 0 => Dw ^ 2 | 1 => Dw ^ 1 | 2 => Dw ^ 1 | 3 => Dw ^ 0 | _ => epsS ^ S N a))
    (fun x _ hq => zW_agree links N K _ _ x fun r hr => by
      have : r ≠ q := fun e => hq (e ▸ hr)
      simp [this])
    (fun x _ hq => zW_agree links N K _ _ x fun r hr => by
      have : r ≠ q := fun e => hq (e ▸ hr)
      simp [this])
    hr1 hr2
    (fun x _ hp => ⟨zW_agree links N K _ _ x fun r hr => by
      have : r ≠ p := fun e => hp (e ▸ hr)
      simp [this], zW_agree links N K _ _ x fun r hr => by
      have : r ≠ p := fun e => hp (e ▸ hr)
      simp [this]⟩)
  -- c₀ cancellation
  let c := c0 betaS K ^ P.length
  let X := Xi (zz []) (incL N) (gas N P)
  let Ld := lam ^ (torusMetric N).ld q p
  have hc1 : (1 : Q') ≤ c := Q'.le_trans' _ _ _ (Q'.le_refl' (1 : Q'))
    (YMGap.Continuum.SU2LinkGasBox.pow_mono_exp (c0_ge K (hβ := by decide)) (Nat.zero_le _))
  have hc0 : (0 : Q') ≤ c := Q'.le_trans' _ _ _ (by decide) hc1
  have hX := (henv _ hG [p]).1
  have e0 := ZW_eq links N K P [] hL
  have hZ : (0 : Q') < Z := YMGap.Continuum.SU2PolymerActivityBound.pos_of_pos_le hX
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))) (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hc1 (Q'.le_of_lt hX)) (Q'.ge_of_eqv e0)))
  refine YMGap.Continuum.SU2TruncRatio.ratio_of hZ ?_
  have cg := fun {a b d e : Q'} (h1 : (ZW links N K P [p, q]).eqv (c * a)) (h2 : Z.eqv (c * b))
      (h3 : (ZW links N K P [p]).eqv (c * d)) (h4 : (ZW links N K P [q]).eqv (c * e)) =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h1)
      (Q'.mul_eqv_congr_left _ _ _ h2))) (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h3) (Q'.mul_eqv_congr_left _ _ _ h4))))
  have E := cg (ZW_eq links N K P [p, q] hL) e0 (ZW_eq links N K P [p] hL) (ZW_eq links N K P [q] hL)
  let V := PolyExpr.var
  let D := Xi (zz [p, q]) (incL N) (gas N P) * X + -(Xi (zz [p]) (incL N) (gas N P) * Xi (zz [q]) (incL N) (gas N P))
  have E2 : (ZW links N K P [p, q] * Z + -(ZW links N K P [p] * ZW links N K P [q])).eqv ((c * c) * D) :=
    Q'.eqv_trans _ _ _ E (poly_identity_of_normal_eq (V 0 * V 1 * (V 0 * V 2) + -(V 0 * V 3 * (V 0 * V 4)))
      (V 0 * V 0 * (V 1 * V 2 + -(V 3 * V 4))) (by decide)
      (fun | 0 => c | 1 => Xi (zz [p, q]) (incL N) (gas N P) | 2 => X | 3 => Xi (zz [p]) (incL N) (gas N P)
           | _ => Xi (zz [q]) (incL N) (gas N P)))
  have hcc : (0 : Q') ≤ c * c := Q'.mul_nonneg _ _ hc0 hc0
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr E2)) (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) ?_)
  rw [ExpNeg.abs_of_nonneg hcc]
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ key hcc) (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ e0) (Q'.mul_eqv_congr_left _ _ _ e0))))
  exact poly_identity_of_normal_eq (V 0 * V 0 * (V 1 * (V 2 * (V 3 * V 3)))) (V 2 * V 1 * (V 0 * V 3 * (V 0 * V 3)))
    (by decide) (fun | 0 => c | 1 => Ld | 2 => Cw | _ => X)

end YMGap.Continuum.SU2WilsonTrunc
