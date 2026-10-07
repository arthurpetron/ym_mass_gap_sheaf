/-
# Torus RP (d9o): dropping Haar blocks on which a polynomial has no variables

`haar_drop`: if no term of `p` has a variable at coordinates `≥ 4k`, then `∫_{k+e} p ≈ ∫_k p` (via the truncation
`trim k p`, `pe_single`, `haar_extend`). This removes the `|C|` fresh blocks of the layout integrand.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPFixPoly
import YMGap.Continuum.SU2TorusRPExtend

namespace YMGap.Continuum.SU2TorusRPTrim

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_refl pe_append pe_haar)

def trim (k : Nat) (p : RatPoly) : RatPoly := p.map fun t => (t.1.take (4 * k), t.2)

theorem exp_take (l : List Nat) (m i : Nat) (h : i < m) : exponentAt (l.take m) i = exponentAt l i := by
  unfold exponentAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem pe_trim (n k : Nat) : ∀ p : RatPoly, (∀ t ∈ p, ∀ i, 4 * k ≤ i → exponentAt t.1 i = 0) →
    PE n p (trim k p)
  | [], _ => pe_refl _ _
  | t :: p, h => by
    show PE n ([t] ++ p) ([(t.1.take (4 * k), t.2)] ++ trim k p)
    refine pe_append n ?_ (pe_trim n k p fun s hs => h s (List.mem_cons_of_mem _ hs))
    refine YMGap.Continuum.SU2TorusRPFixPoly.pe_single n (fun i => ?_) (Q'.eqv_refl _)
    rcases Nat.lt_or_ge i (4 * k) with hi | hi
    · exact (exp_take _ _ _ hi).symm
    · rw [h t (List.mem_cons_self ..) i hi,
        YMGap.Continuum.SU2MultiLinkHaarFactorization.exponentAt_of_length_le _ _
          (Nat.le_trans (List.length_take_le _ _) hi)]

theorem sup_trim (k : Nat) (p : RatPoly) :
    YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks k (trim k p) := fun s hs => by
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hs
  exact List.length_take_le _ _

theorem haar_drop (k e : Nat) (p : RatPoly) (h : ∀ t ∈ p, ∀ i, 4 * k ≤ i → exponentAt t.1 i = 0) :
    (quaternionHaar (k + e) p).eqv (quaternionHaar k p) :=
  Q'.eqv_trans _ _ _ (pe_haar _ (pe_trim _ k p h))
    (Q'.eqv_trans _ _ _ (YMGap.Continuum.SU2TorusRPExtend.haar_extend k e _ (sup_trim k p))
      (Q'.eqv_symm (pe_haar _ (pe_trim _ k p h))))

end YMGap.Continuum.SU2TorusRPTrim

#print axioms YMGap.Continuum.SU2TorusRPTrim.haar_drop
