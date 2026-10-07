/-
# R1 commit 12: observable insertion as modified polymer activities (cross-multiplied form)

ADDITIVE.  **Regime:** strong coupling, heat-kernel (spin-truncated), not Wilson.  Also true for
U(1), so not gap evidence.

**Expectation used.**  χ_r := `plaqCharacter links N r 1`, the fundamental trace of the plaquette
holonomy.  For a list S of observable plaquettes in P, the observable-weighted partition is
`ZObs S = ∫ Π_{r∈P} (c₀ + g^S_r)`, with c₀ = `coeffW w 0 * 1` ≈ 1 and
`g^S_r = f_r + χ_r + χ_r·f_r` for r ∈ S (otherwise `g^S_r = f_r`).
Since c₀ ≈ 1, this is ∫ Π_{r∈S}(1+χ_r) Π_{r∈P}(c₀+f_r), up to replacing c₀χ_r by χ_r.
`ZObs [] = polyPartition`.  Write
  `Zp := ZObs[p] − Z` and `Zpq := ZObs[p,q] − ZObs[p] − ZObs[q] + Z`.
Then ⟨χ_p⟩ = Zp/Z and ⟨χ_pχ_q⟩ = Zpq/Z, and the truncated correlator is (Zpq·Z − Zp·Zq)/Z².

* `ZObs_nil`: `ZObs [] = polyPartition`.
* `ZObs_eq_Xi`: `ZObs S ≈ Ξ(z^S; gas N P)`, on the SAME gas and incompatibility, with
  `z^S γ = ∫ Π_{r∈γ} g^S_r`.
* `zObs_off`: z^S γ = z γ when γ avoids S.  Only polymers that touch S change.
* `trunc_eq_Xi`: `Zpq·Z − Zp·Zq ≈ Ξ(z^{pq})Ξ(z) − Ξ(z^p)Ξ(z^q)` (cross-multiplied, no reciprocals).
* `l1_gObs`: `‖g^S_r‖₁ ≤ c + 513 + 513c` whenever `‖f_r‖₁ ≤ c`.
-/

import YMGap.Continuum.SU2LinkDecayHeat

namespace YMGap.Continuum.SU2ObsInsertion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarDisjointSupport
open YMGap.Continuum.SU2HaarL1Activity (prodPoly fPoly l1 l1_add_le l1_mul l1_nonneg char_l1 word_l1)
open YMGap.Continuum.SU2PlaqSupport
open YMGap.Continuum.SU2ClusterExplore (W Lk)
open YMGap.Continuum.SignedPolymerKP (Xi)
open YMGap.Continuum.SU2PolymerIdentity (incL gas polymer_identity integrand_eq)
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (polyPartition coeffW coeffW_zero_eqv plaqCharacter)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

variable (w : Q') (M : Nat) (links : List Z4Link) (N : Nat)

/-- χ₁ of the plaquette holonomy. -/
abbrev chi (r : Z4Plaq) : RatPoly := plaqCharacter links N r 1

/-- Observable-modified plaquette factor. -/
def gObs (S : List Z4Plaq) (r : Z4Plaq) : RatPoly :=
  if r ∈ S then polyAdd (polyAdd (fPoly w links N r M) (chi links N r))
    (polyMul (chi links N r) (fPoly w links N r M))
  else fPoly w links N r M

theorem gObs_free (S : List Z4Plaq) (r : Z4Plaq) : FreeOff (idxB links N r) false (gObs w M links N S r) := by
  unfold gObs
  split
  · exact free_add _ _ (free_add _ _ (fPoly_free w links N r M) (plaq_free links N r 1))
      (free_mul _ _ (plaq_free links N r 1) (fPoly_free w links N r M))
  · exact fPoly_free w links N r M

/-- The observable-weighted partition `∫ Π_{r∈P} (c₀ + g^S_r)`. -/
def ZObs (P S : List Z4Plaq) : Q' :=
  quaternionHaar links.length (prodPoly (W (gObs w M links N S) (coeffW w 0 * 1)) P)

/-- The observable-modified activity `z^S γ = ∫ Π_{r∈γ} g^S_r`. -/
def zObs (S : List Z4Plaq) (γ : List Z4Plaq) : Q' :=
  quaternionHaar links.length (prodPoly (gObs w M links N S) γ)

theorem gObs_nil : gObs w M links N [] = fun r => fPoly w links N r M :=
  funext fun r => by unfold gObs; rw [if_neg List.not_mem_nil]

theorem ZObs_nil (P : List Z4Plaq) : ZObs w M links N P [] = polyPartition w M links N P := by
  show _ = quaternionHaar links.length (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.torusIntegrand w M links N P)
  rw [integrand_eq, ZObs, gObs_nil]

theorem ZObs_eq_Xi (P S : List Z4Plaq) (hL : ∀ p ∈ P, Lk links N p) :
    (ZObs w M links N P S).eqv (Xi (zObs w M links N S) (incL N) (gas N P)) :=
  polymer_identity N links.length links _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (coeffW_zero_eqv w))
    (gObs_free w M links N S) P.length P (Nat.le_refl _) hL

theorem prod_off (S : List Z4Plaq) : ∀ γ : List Z4Plaq, (∀ r, r ∈ γ → r ∉ S) →
    prodPoly (gObs w M links N S) γ = prodPoly (fun p => fPoly w links N p M) γ
  | [], _ => rfl
  | r :: γ, h => by
    show polyMul _ _ = polyMul _ _
    rw [prod_off S γ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    unfold gObs; rw [if_neg (h r List.mem_cons_self)]

theorem zObs_off (S γ : List Z4Plaq) (h : ∀ r, r ∈ γ → r ∉ S) :
    zObs w M links N S γ = zObs w M links N [] γ := by
  unfold zObs; rw [prod_off w M links N S γ h, prod_off w M links N [] γ (fun _ _ => List.not_mem_nil)]

/-- Cross-multiplied truncation identity (pure algebra). -/
theorem trunc_alg (Z Za Zb Zab : Q') :
    ((Zab + -Za + -Zb + Z) * Z + -((Za + -Z) * (Zb + -Z))).eqv (Zab * Z + -(Za * Zb)) := by
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq ((V 3 + -V 1 + -V 2 + V 0) * V 0 + -((V 1 + -V 0) * (V 2 + -V 0)))
    (V 3 * V 0 + -(V 1 * V 2)) (by decide) (fun | 0 => Z | 1 => Za | 2 => Zb | _ => Zab)

/-- **Truncated correlator in polymer form (PROVED).**  With `Z = ZObs []`, `Zp = ZObs[p] − Z`,
`Zq = ZObs[q] − Z` and `Zpq = ZObs[p,q] − ZObs[p] − ZObs[q] + Z`:
`Zpq·Z − Zp·Zq ≈ Ξ(z^{pq})Ξ(z) − Ξ(z^p)Ξ(z^q)`, all over `gas N P`. -/
theorem trunc_eq_Xi (P : List Z4Plaq) (hL : ∀ r ∈ P, Lk links N r) (p q : Z4Plaq) :
    let Z := ZObs w M links N P []
    let Zp := ZObs w M links N P [p] + -Z
    let Zq := ZObs w M links N P [q] + -Z
    let Zpq := ZObs w M links N P [p, q] + -ZObs w M links N P [p] + -ZObs w M links N P [q] + Z
    (Zpq * Z + -(Zp * Zq)).eqv
      (Xi (zObs w M links N [p, q]) (incL N) (gas N P) * Xi (zObs w M links N []) (incL N) (gas N P) +
        -(Xi (zObs w M links N [p]) (incL N) (gas N P) * Xi (zObs w M links N [q]) (incL N) (gas N P))) := by
  intro Z Zp Zq Zpq
  refine Q'.eqv_trans _ _ _ (trunc_alg _ _ _ _) ?_
  have e := fun S => ZObs_eq_Xi w M links N P S hL
  exact Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (e _))
      (Q'.mul_eqv_congr_left _ _ _ (e _)))
    (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (e _))
      (Q'.mul_eqv_congr_left _ _ _ (e _))))

abbrev B513 : Q' := 2 * Q'.ofNat 256 + 1

theorem l1_chi (r : Z4Plaq) : l1 (chi links N r) ≤ B513 := by
  have h := (char_l1 _ _ (by decide) (word_l1 links N r) 0).2
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_one_eqv _))

/-- Activity input for an observable plaquette: `‖g^S_r‖₁ ≤ c + 513 + 513c`. -/
theorem l1_gObs (S : List Z4Plaq) (r : Z4Plaq) (c : Q') (hf : l1 (fPoly w links N r M) ≤ c) :
    l1 (gObs w M links N S r) ≤ c + B513 + B513 * c := by
  have hc : (0 : Q') ≤ c := Q'.le_trans' _ _ _ (l1_nonneg _) hf
  unfold gObs
  split
  · refine Q'.le_trans' _ _ _ (l1_add_le _ _) (Q'.add_le_add (Q'.le_trans' _ _ _ (l1_add_le _ _)
      (Q'.add_le_add hf (l1_chi links N r))) ?_)
    exact Q'.le_trans' _ _ _ (l1_mul _ _) (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
      (l1_chi links N r) (l1_nonneg _)) (Q'.mul_le_mul_of_nonneg_left _ _ _ hf (by decide : (0 : Q') ≤ B513)))
  · refine Q'.le_trans' _ _ _ hf (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg c B513 (by decide)) ?_)
    exact Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg B513 c (by decide) hc)

end YMGap.Continuum.SU2ObsInsertion
