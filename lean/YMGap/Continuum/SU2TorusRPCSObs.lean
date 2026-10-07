/-
# Torus RP (f5): RP Cauchy–Schwarz for link observables (truncated T_K weight, fixed K)

`torus_cs_obs`: for observables `e, e'` on positive links,
`rpB F G · rpB F G ≤ rpB F F · rpB G G` where `F = eval e` and `G = eval e'`. This is the cross-multiplied rational
shape of `SU2LogConvexGap.LogConvex`. Proof: `torus_rp` at `s·e + t·e'` for every integer `s, t`, then the
bilinear expansion (`SU2TorusRPBil`), symmetry (`rpB_symm`) and `cs_q`. No reals, no Classical.
-/

import YMGap.Continuum.SU2TorusRPBil

namespace YMGap.Continuum.SU2TorusRPCSObs

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPChoosePC (Pt)
open YMGap.Continuum.SU2TorusRPObs (Obs eval OnLinks)
open YMGap.Continuum.SU2TorusRPCSShape (rpB)
open YMGap.Continuum.SU2TorusRPCSRat (quad)

/-- `s·e + t·e'` as an observable. -/
def comb (e e' : Obs) (s t : Int) : Obs :=
  .add (.mul (.const (Q'.ofInt s)) e) (.mul (.const (Q'.ofInt t)) e')

theorem one_num : (1 : Q').num = 1 := rfl
theorem one_den : ((1 : Q').den : Int) = 1 := rfl

/-- The polarization identity in `Q'` (cross-multiplied, checked over `Int`). -/
theorem alg (a b c : Q') (s t : Int) :
    ((Q'.ofInt s * 1) * ((Q'.ofInt s * 1) * a + (Q'.ofInt t * 1) * b) +
      (Q'.ofInt t * 1) * ((Q'.ofInt s * 1) * b + (Q'.ofInt t * 1) * c)).eqv (quad a b c s t) := by
  have e : ∀ x : Int, (Q'.ofInt x).num = x := fun _ => rfl
  unfold quad
  show Q'.num _ * ((Q'.den _ : Nat) : Int) = Q'.num _ * ((Q'.den _ : Nat) : Int)
  simp only [Q'.add_num_cast, Q'.mul_num_cast, Q'.add_den_cast, Q'.mul_den_cast,
    YMGap.Continuum.SU2TorusRPCSRat.ofInt_den, e, one_num, one_den]
  simp only [Int.mul_add, Int.add_mul, Int.mul_one, Int.one_mul]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

variable {M : Nat} (hM : 1 ≤ M) {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat)

include hβ in
theorem torus_cs_obs (e e' : Obs) (he : OnLinks (· ∈ Pt M) e) (he' : OnLinks (· ∈ Pt M) e') :
    rpB hM β K (eval (torusLinks (2 * M)) e) (eval (torusLinks (2 * M)) e') *
        rpB hM β K (eval (torusLinks (2 * M)) e) (eval (torusLinks (2 * M)) e') ≤
      rpB hM β K (eval (torusLinks (2 * M)) e) (eval (torusLinks (2 * M)) e) *
        rpB hM β K (eval (torusLinks (2 * M)) e') (eval (torusLinks (2 * M)) e') := by
  have hP : ∀ ℓ, ℓ ∈ Pt M → ℓ ∈ torusLinks (2 * M) := fun ℓ h =>
    (YMGap.Continuum.SU2TorusRPTorusZ.mem_tl ℓ).2 ((YMGap.Continuum.SU2TorusRPChoosePC.mem_Pt ℓ).1 h).1
  have ht := YMGap.Continuum.SU2TorusRPHW.onLinks_mono hP e he
  have ht' := YMGap.Continuum.SU2TorusRPHW.onLinks_mono hP e' he'
  refine YMGap.Continuum.SU2TorusRPCSRat.cs_q _ _ _ fun s t => ?_
  have hpos := YMGap.Continuum.SU2TorusRPHW.torus_rp hM hβ K (comb e e' s t) ⟨⟨trivial, he⟩, ⟨trivial, he'⟩⟩
  let F := eval (torusLinks (2 * M)) e
  let G := eval (torusLinks (2 * M)) e'
  let σ := Q'.ofInt s * 1
  let τ := Q'.ofInt t * 1
  have hZ : eval (torusLinks (2 * M)) (comb e e' s t) = polyAdd (polySmul σ F) (polySmul τ G) := by
    show polyAdd (polyMul [([], Q'.ofInt s * 1)] F) (polyMul [([], Q'.ofInt t * 1)] G) = _
    rw [YMGap.Continuum.SU2TorusRPBil.cmul_eq, YMGap.Continuum.SU2TorusRPBil.cmul_eq]
  have hpos' : (0 : Q') ≤ rpB hM β K (polyAdd (polySmul σ F) (polySmul τ G)) (polyAdd (polySmul σ F) (polySmul τ G)) := by
    rw [← hZ]; exact hpos
  have hrow : ∀ X, (rpB hM β K X (polyAdd (polySmul σ F) (polySmul τ G))).eqv
      (σ * rpB hM β K X F + τ * rpB hM β K X G) := fun X =>
    Q'.eqv_trans _ _ _ (YMGap.Continuum.SU2TorusRPBil.bil_add_r hM β K _ _ _)
      (Q'.add_eqv_congr' (YMGap.Continuum.SU2TorusRPBil.bil_smul_r hM β K _ _ _)
        (YMGap.Continuum.SU2TorusRPBil.bil_smul_r hM β K _ _ _))
  have hsym := YMGap.Continuum.SU2TorusRPSym.rpB_symm hM β K e' e ht' ht
  have hE : (rpB hM β K (polyAdd (polySmul σ F) (polySmul τ G)) (polyAdd (polySmul σ F) (polySmul τ G))).eqv
      (σ * (σ * rpB hM β K F F + τ * rpB hM β K F G) + τ * (σ * rpB hM β K F G + τ * rpB hM β K G G)) :=
    Q'.eqv_trans _ _ _ (YMGap.Continuum.SU2TorusRPBil.bil_add_l hM β K _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (YMGap.Continuum.SU2TorusRPBil.bil_smul_l hM β K _ _ _)
          (Q'.mul_eqv_congr_left _ _ _ (hrow F)))
        (Q'.eqv_trans _ _ _ (YMGap.Continuum.SU2TorusRPBil.bil_smul_l hM β K _ _ _)
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (hrow G)
            (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hsym) (Q'.eqv_refl _))))))
  exact Q'.le_trans' _ _ _ hpos' (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hE (alg _ _ _ s t)))

end YMGap.Continuum.SU2TorusRPCSObs

#print axioms YMGap.Continuum.SU2TorusRPCSObs.alg
#print axioms YMGap.Continuum.SU2TorusRPCSObs.torus_cs_obs
