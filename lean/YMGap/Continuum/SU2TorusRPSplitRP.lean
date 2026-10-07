/-
# Torus RP (d5c): RP for the split half-layout integrand with the concrete twist

`torus_rp_split`: on `a + a` blocks with a half-shift involution `σ` (`σ k = k + a` for `k < a`), block selector
`Tb`, `Θ X := sign(conjSel Tb)(reindex σ X)`, and crossing factors `G c` whose `Ctw`-twists are RPKs,
  `0 ≤ ∫ (ΘF·F)·((Wp·ΘWp)·Π_cs G)`.
All `rp_conj_assembly` hypotheses are discharged here (Haar invariance and RingSub of `Ctw`, `C_fixes`,
`theta_C_shift`, `above = conjSel ∘ secT`). Crossing factors are supplied by `rpk_C_cross0` / `rpk_C_crossM`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (still: instantiating the layout from the torus geometry and
identifying the actual integrand with this form).
-/

import YMGap.Continuum.SU2TorusRPCrossC

namespace YMGap.Continuum.SU2TorusRPSplitRP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_refl)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2TorusRPHaar (conjSel)
open YMGap.Continuum.SU2TorusRPCore (Sup RPK rpk_one rpk_mul rpk_congr)
open YMGap.Continuum.SU2TorusRPHalfConj (above)
open YMGap.Continuum.SU2TorusRPCrossC (secT Ctw Ctw_ringSub)
open YMGap.Continuum.SU2MultiLinkHaarFactorization (shiftPoly)

theorem above_eq (a : Nat) (T : Nat → Bool) : above (4 * a) (conjSel T) = conjSel (secT a T) := by
  funext i
  unfold above conjSel secT
  by_cases h : a ≤ i / 4
  · rw [decide_eq_true h, decide_eq_true (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_false (by omega)]; rfl

theorem rpk_C_prod {a : Nat} (T : Nat → Bool) {α : Type} (G : α → RatPoly) :
    ∀ cs : List α, (∀ c ∈ cs, RPK a (Ctw a T (G c))) →
      RPK a (Ctw a T (cs.foldr (fun c X => polyMul (G c) X) polyOne))
  | [], _ => rpk_congr (Ctw_ringSub a T).one (rpk_one a)
  | c :: cs, h => rpk_congr ((Ctw_ringSub a T).mul _ _)
      (rpk_mul (h c (List.mem_cons_self ..)) (rpk_C_prod T G cs fun d hd => h d (List.mem_cons_of_mem _ hd)))

theorem torus_rp_split {a : Nat} (σ : QuaternionBlockInvolution (a + a)) (hσ : ∀ k, k < a → σ.map k = k + a)
    (Tb : Nat → Bool) (F Wp : RatPoly) (hF : Sup a F) (hWp : Sup a Wp) {α : Type} (G : α → RatPoly)
    (cs : List α) (hG : ∀ c ∈ cs, RPK a (Ctw a Tb (G c))) :
    (0 : Q') ≤ quaternionHaar (a + a)
      (polyMul (polyMul (signSelectedPolynomial (4 * (a + a)) (conjSel Tb) (reindexQuaternionPolynomial σ F)) F)
        (polyMul (polyMul Wp (signSelectedPolynomial (4 * (a + a)) (conjSel Tb) (reindexQuaternionPolynomial σ Wp)))
          (cs.foldr (fun c X => polyMul (G c) X) polyOne))) := by
  have hab := above_eq a Tb
  have hTh : ∀ X, Sup a X → PE (a + a) (Ctw a Tb (signSelectedPolynomial (4 * (a + a)) (conjSel Tb)
      (reindexQuaternionPolynomial σ X))) (shiftPoly a X) := fun X hX => by
    have h := YMGap.Continuum.SU2TorusRPAssembly.theta_C_shift σ hσ (conjSel Tb) X hX
    rw [hab] at h; exact h
  have hfix : ∀ X, Sup a X → PE (a + a) (Ctw a Tb X) X := fun X hX => by
    have h := YMGap.Continuum.SU2TorusRPAssembly.C_fixes (a := a) (conjSel Tb) X hX
    rw [hab] at h; exact h
  exact YMGap.Continuum.SU2TorusRPAssembly.rp_conj_assembly (Ctw a Tb)
    (fun X => YMGap.Continuum.SU2TorusRPHaar.conj_haar (a + a) (secT a Tb) X) (Ctw_ringSub a Tb)
    F Wp _ _ _ hF hWp (hfix F hF) (hfix Wp hWp) (hTh F hF) (hTh Wp hWp) (rpk_C_prod Tb G cs hG)

end YMGap.Continuum.SU2TorusRPSplitRP

#print axioms YMGap.Continuum.SU2TorusRPSplitRP.torus_rp_split
