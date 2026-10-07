/-
# Transfer matrix (2c): partial Haar integration over trailing blocks (Fubini)

ADDITIVE.  **Labels:** algebra only, valid for every coupling; also true for U(1), not gap evidence.

`tailInt a b P` integrates out the last `b` quaternion blocks of `P`.  Each monomial `m` becomes
`take(4a) m` with coefficient `c · ∫_b drop(4a) m`.  The result is a polynomial in the first `a`
blocks.  This is the operation `∫ dV` in the slice kernel `T(U,U') = A(U) ∫dV B(U,V,U')`.

* `mono_split`: `∫_{a+b} m ≈ ∫_a take(4a) m · ∫_b drop(4a) m`.  This is `mono_factor` plus
  `mono_congr`; no support hypothesis is needed.
* `fubini`: `∫_{a+b} P ≈ ∫_a (tailInt a b P)`.
* `tailInt_sup`: `tailInt a b P` is supported on `a` blocks.
-/

import YMGap.Continuum.SU2TorusRPCore

namespace YMGap.Continuum.SU2TailHaar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2MultiLinkHaarFactorization (mono_factor exponentAt_drop exponentAt_replicate_append
  exponentAt_of_length_le)
open YMGap.Continuum.SU2TorusRPCore (Sup mono_congr)

/-- Integrate out the trailing `b` blocks. -/
def tailInt (a b : Nat) (P : RatPoly) : RatPoly :=
  P.map fun t => (t.1.take (4 * a), t.2 * quaternionHaarMono b (t.1.drop (4 * a)))

theorem mono_split (a b : Nat) (m : List Nat) :
    (quaternionHaarMono (a + b) m).eqv
      (quaternionHaarMono a (m.take (4 * a)) * quaternionHaarMono b (m.drop (4 * a))) := by
  have e : quaternionHaarMono (a + b) m =
      quaternionHaarMono (a + b) (monoMul (m.take (4 * a)) (List.replicate (4 * a) 0 ++ m.drop (4 * a))) :=
    mono_congr (a + b) fun i => by
      rw [YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.exponentAt_monoMul,
        exponentAt_replicate_append]
      by_cases hi : i < 4 * a
      · rw [if_pos hi]
        have : exponentAt (m.take (4 * a)) i = exponentAt m i := by
          simp only [exponentAt, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi]
        omega
      · rw [if_neg hi, exponentAt_drop, exponentAt_of_length_le (m.take (4 * a)) i
          (by rw [List.length_take]; exact Nat.le_trans (Nat.min_le_left _ _) (by omega)),
          show 4 * a + (i - 4 * a) = i by omega]
        omega
  rw [e]
  exact mono_factor a b _ _ (by rw [List.length_take]; exact Nat.min_le_left _ _)

/-- **Fubini over trailing blocks (PROVED).** -/
theorem fubini (a b : Nat) : ∀ P : RatPoly,
    (quaternionHaar (a + b) P).eqv (quaternionHaar a (tailInt a b P))
  | [] => Q'.eqv_refl _
  | t :: P => by
    show (t.2 * quaternionHaarMono (a + b) t.1 + quaternionHaar (a + b) P).eqv
      (t.2 * quaternionHaarMono b (t.1.drop (4 * a)) * quaternionHaarMono a (t.1.take (4 * a)) +
        quaternionHaar a (tailInt a b P))
    refine Q'.add_eqv_congr' ?_ (fubini a b P)
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (mono_split a b t.1)) ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

theorem tailInt_sup (a b : Nat) (P : RatPoly) : Sup a (tailInt a b P) := fun s hs => by
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hs
  show (t.1.take (4 * a)).length ≤ 4 * a
  rw [List.length_take]; exact Nat.min_le_left _ _

end YMGap.Continuum.SU2TailHaar
