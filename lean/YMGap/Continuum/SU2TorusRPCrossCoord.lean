/-
# Torus RP (d5a): crossing kernels in link coordinates

* `shQ_cv`: `shQ a (U_b) = U_{b+a}` exactly (the half shift on coordinates).
* `supQ_cv/mul/conj`: positive-half support for coordinate words.
* `rpk_cross0_cv`, `rpk_crossM_cv`: with blocks `s₁, p, s₂ < a` and partners at `+a`, the C-twisted split
  crossing plaquette weights at the cuts `t = 0` and `t = M` are RPKs.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPCrossM

namespace YMGap.Continuum.SU2TorusRPCrossCoord

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.RingNormaliser (varMono)
open PolyQuaternion (mul conj)
open YMGap.Continuum.SU2TorusRPKernel (shQ SupQ)
open YMGap.Continuum.SU2TorusRPCore (RPK Sup sup_mul)
open YMGap.Continuum.SU2WilsonCharacterPower (wilsonPoly)
open YMGap.Continuum.SU2WilsonActivity (wilsonA)

local notation "cv" => PolyQuaternion.coordinateVariable

theorem sh_var (a i : Nat) : YMGap.Continuum.SU2MultiLinkHaarFactorization.shiftPoly a (polyVar i) =
    polyVar (4 * a + i) := by
  simp only [YMGap.Continuum.SU2MultiLinkHaarFactorization.shiftPoly, polyVar, varMono, List.map_cons,
    List.map_nil, ← List.append_assoc, List.replicate_append_replicate]

theorem shQ_cv (a b : Nat) : shQ a (cv b) = cv (b + a) := by
  unfold shQ PolyQuaternion.coordinateVariable
  rw [sh_var, sh_var, sh_var, sh_var]
  have e : ∀ c, 4 * a + (4 * b + c) = 4 * (b + a) + c := fun c => by omega
  rw [e 1, e 2, e 3, show 4 * a + 4 * b = 4 * (b + a) by omega]

theorem sup_add {a : Nat} {p q : RatPoly} (hp : Sup a p) (hq : Sup a q) : Sup a (polyAdd p q) := fun s hs => by
  rcases List.mem_append.mp hs with h | h
  · exact hp s h
  · exact hq s h

theorem sup_neg {a : Nat} {p : RatPoly} (hp : Sup a p) : Sup a (polyNeg p) := fun s hs => by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact hp t ht

theorem sup_var {a i : Nat} (h : i < 4 * a) : Sup a (polyVar i) := fun s hs => by
  simp only [polyVar, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  show (List.replicate i 0 ++ [1]).length ≤ 4 * a
  rw [List.length_append, List.length_replicate]; exact h

theorem supQ_cv {a b : Nat} (h : b < a) : SupQ a (cv b) :=
  ⟨sup_var (by omega), sup_var (by omega), sup_var (by omega), sup_var (by omega)⟩

theorem supQ_mul {a : Nat} {q r : PolyQuaternion} (hq : SupQ a q) (hr : SupQ a r) : SupQ a (mul q r) := by
  obtain ⟨q0, q1, q2, q3⟩ := hq; obtain ⟨r0, r1, r2, r3⟩ := hr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [PolyQuaternion.mul] <;>
    repeat (first | apply sup_add | apply sup_neg | apply sup_mul | assumption)

theorem supQ_conj {a : Nat} {q : PolyQuaternion} (hq : SupQ a q) : SupQ a (conj q) :=
  ⟨hq.1, sup_neg hq.2.1, sup_neg hq.2.2.1, sup_neg hq.2.2.2⟩

/-- Cut `t = 0` crossing plaquette (left split, C-twisted), coordinates. -/
theorem rpk_cross0_cv {a : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (s1 p s2 : Nat)
    (h1 : s1 < a) (hp : p < a) (h2 : s2 < a) :
    RPK a (wilsonPoly
      (mul (mul (mul (conj (cv (s1 + a))) (cv s1)) (cv p))
        (mul (conj (mul (conj (cv (s2 + a))) (cv s2))) (conj (cv (p + a))))).scalar (wilsonA β) K) := by
  have h := YMGap.Continuum.SU2TorusRPCrossSplit.rpk_cross_split (a := a) hβ K (cv s1) (cv p) (cv s2)
    (supQ_mul (supQ_mul (supQ_cv h1) (supQ_cv hp)) (supQ_conj (supQ_cv h2)))
  rwa [shQ_cv, shQ_cv, shQ_cv] at h

/-- Cut `t = M` crossing plaquette (right split, C-twisted), coordinates. -/
theorem rpk_crossM_cv {a : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (s1 p s2 : Nat)
    (h1 : s1 < a) (hp : p < a) (h2 : s2 < a) :
    RPK a (wilsonPoly
      (mul (mul (mul (cv s1) (conj (cv (s1 + a)))) (cv (p + a)))
        (mul (conj (mul (cv s2) (conj (cv (s2 + a))))) (conj (cv p)))).scalar (wilsonA β) K) := by
  have h := YMGap.Continuum.SU2TorusRPCrossM.rpk_cross_M (a := a) hβ K (cv s1) (cv p) (cv s2)
    (supQ_mul (supQ_mul (supQ_conj (supQ_cv h2)) (supQ_conj (supQ_cv hp))) (supQ_cv h1))
  rwa [shQ_cv, shQ_cv, shQ_cv] at h

end YMGap.Continuum.SU2TorusRPCrossCoord

#print axioms YMGap.Continuum.SU2TorusRPCrossCoord.shQ_cv
#print axioms YMGap.Continuum.SU2TorusRPCrossCoord.rpk_cross0_cv
#print axioms YMGap.Continuum.SU2TorusRPCrossCoord.rpk_crossM_cv
