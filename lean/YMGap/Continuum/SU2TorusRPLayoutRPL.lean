/-
# Torus RP (d9p): layout RP on exactly the `|L|` link blocks

`torus_rp_layL`: `torus_rp_lay` with the Haar functional on `|L| = 2|P| + |C|` blocks (the link blocks of the layout),
the `|C|` fresh split blocks dropped by `haar_drop`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPLayoutRP
import YMGap.Continuum.SU2TorusRPTrim

namespace YMGap.Continuum.SU2TorusRPLayoutRPL

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPCore (Sup)
open YMGap.Continuum.SU2TorusRPHaar (conjSel)
open YMGap.Continuum.SU2TorusRPGeom (reflLink linkSide plaqSide Side)
open YMGap.Continuum.SU2TorusRPLayoutT (layT)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)
open YMGap.Continuum.SU2TorusRPHalfSwap (halfSwap)

/-- No variable at coordinates `≥ 4k`. -/
def Van (k : Nat) (p : RatPoly) : Prop := ∀ t ∈ p, ∀ i, 4 * k ≤ i → exponentAt t.1 i = 0

theorem van_sup {k : Nat} {p : RatPoly} (h : Sup k p) : Van k p := fun t ht i hi =>
  YMGap.Continuum.SU2MultiLinkHaarFactorization.exponentAt_of_length_le _ _ (Nat.le_trans (h t ht) hi)

theorem van_mul {k : Nat} {p q : RatPoly} (hp : Van k p) (hq : Van k q) : Van k (polyMul p q) := by
  intro t ht i hi
  simp only [polyMul, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨s, hs, u, hu, rfl⟩ := ht
  show exponentAt (monoMul s.1 u.1) i = 0
  rw [YMGap.Continuum.SU2TorusRPFixPoly.emm, hp s hs i hi, hq u hu i hi]

theorem van_theta (P C : List Z4Link) (S : Nat → Bool) (F : RatPoly) (hF : Sup P.length F) :
    Van (P.length + C.length + P.length)
      (signSelectedPolynomial (4 * ((P.length + C.length) + (P.length + C.length))) S
        (reindexQuaternionPolynomial (halfSwap (P.length + C.length)) F)) := by
  intro t ht i hi
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  show exponentAt (reindexQuaternionExponents (halfSwap (P.length + C.length)) w.1) i = 0
  rcases Nat.lt_or_ge i (4 * ((P.length + C.length) + (P.length + C.length))) with hil | hil
  · rw [exponentAt_reindexQuaternionExponents _ _ hil]
    apply YMGap.Continuum.SU2MultiLinkHaarFactorization.exponentAt_of_length_le
    refine Nat.le_trans (hF w hw) ?_
    show 4 * P.length ≤ 4 * YMGap.Continuum.SU2TorusRPHalfSwap.hsMap (P.length + C.length) (i / 4) + i % 4
    unfold YMGap.Continuum.SU2TorusRPHalfSwap.hsMap
    have hq : P.length + C.length + P.length ≤ i / 4 :=
      (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mpr (by rw [Nat.mul_comm]; exact hi)
    rcases Nat.lt_or_ge (i / 4) (P.length + C.length) with h | h
    · exact absurd hq (Nat.not_le.mpr (Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)))
    · rw [if_neg (Nat.not_lt.mpr h)]
      have hq2 : i / 4 < (P.length + C.length) + (P.length + C.length) :=
        (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mpr (by rw [Nat.mul_comm]; exact hil)
      rw [if_pos hq2]
      refine Nat.le_trans (Nat.mul_le_mul_left 4 ?_) (Nat.le_add_right _ _)
      exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hq)
  · exact YMGap.Continuum.SU2MultiLinkHaarFactorization.exponentAt_of_length_le _ _
      (by rw [reindexQuaternionExponents_length]; exact hil)

theorem haar_drop' (N k e : Nat) (hN : N = k + e) (p : RatPoly) (h : Van k p) :
    (quaternionHaar N p).eqv (quaternionHaar k p) := by
  subst hN; exact YMGap.Continuum.SU2TorusRPTrim.haar_drop k e p h

theorem torus_rp_layL {M : Nat} (hM : 1 ≤ M) (P C : List Z4Link) (hnd : (P ++ C ++ P.map (reflLink M)).Nodup)
    (hC : C.Nodup) (hCne : C ≠ [])
    (hCcov : ∀ ℓ : Z4Link, InBox (2 * M) ℓ.1 → linkSide M ℓ = .cross → ℓ ∈ C)
    (hPcov : ∀ ℓ : Z4Link, InBox (2 * M) ℓ.1 → linkSide M ℓ = .pos → ℓ ∈ P)
    (hPbox : ∀ x ∈ P, InBox (2 * M) x.1)
    {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (ps pos cross : List Z4Plaq)
    (hperm : ps.Perm (pos ++ pos.map (mir M) ++ cross))
    (hposP : ∀ p ∈ pos, InBox (2 * M) p.1 ∧ plaqSide M p = .pos)
    (hcross : ∀ q ∈ cross, InBox (2 * M) q.1 ∧ plaqSide M q = .cross)
    (hpsbox : ∀ p ∈ ps, InBox (2 * M) p.1)
    (F : RatPoly) (hF : Sup P.length F) :
    (0 : Q') ≤ quaternionHaar (P.length + C.length + P.length)
      (polyMul (polyMul (signSelectedPolynomial (4 * ((P.length + C.length) + (P.length + C.length)))
          (conjSel (layT (P ++ C ++ P.map (reflLink M))))
          (reindexQuaternionPolynomial (halfSwap (P.length + C.length)) F)) F)
        (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (P ++ C ++ P.map (reflLink M)) (2 * M) β K) ps)) := by
  have h := YMGap.Continuum.SU2TorusRPLayoutRP.torus_rp_lay hM P C hnd hC hCne hCcov hPcov hPbox hβ K ps pos cross
    hperm hposP hcross hpsbox F hF
  refine Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_drop' _ _ C.length (by omega) _ ?_))
  refine van_mul (van_mul (van_theta P C _ F hF) (van_sup (YMGap.Continuum.SU2TorusRPLayoutSup.sup_mono
    (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hF))) (van_sup ?_)
  refine YMGap.Continuum.SU2TorusRPSupTK.sup_prodTK _ _ β K ps fun p hp => ?_
  rw [YMGap.Continuum.SU2TorusRPMirGeom.plaqIdx_eq]
  intro b hb
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hb
  have hm := YMGap.Continuum.SU2TorusRPLayoutBounds.mem_lay hM P C hCcov hPcov ℓ
    (YMGap.Continuum.SU2TorusRPLayoutFactor.plaqLinks_box (by omega) p (hpsbox p hp) ℓ hℓ)
  have hl := YMGap.Continuum.SU2TorusRPLayout.idxOf_lt ℓ _ hm
  simp only [List.length_append, List.length_map] at hl
  exact hl

end YMGap.Continuum.SU2TorusRPLayoutRPL

#print axioms YMGap.Continuum.SU2TorusRPLayoutRPL.van_mul
#print axioms YMGap.Continuum.SU2TorusRPLayoutRPL.van_theta
#print axioms YMGap.Continuum.SU2TorusRPLayoutRPL.torus_rp_layL
