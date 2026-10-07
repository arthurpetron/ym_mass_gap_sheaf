/-
# Extracting a genuine Wilson observable insertion

`obsTK_extract` pulls the factor `1+chi p` out of the actual finite Wilson
integrand when `p` occurs exactly once in the plaquette list and was not
already selected. Thus two applications extract two distinct physical roots.

This is polynomial algebra in Haar-context equivalence, with no activity or
clustering assumption. Centering, covariance cancellation and invariance of
one-point means remain separate inputs to the torus correlator bridge.
-/

import YMGap.Continuum.SU2WilsonTrunc
import YMGap.Continuum.SU2TorusRPSplitTK

namespace YMGap.Continuum.SU2WilsonObsExtraction

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress (Z4Link Z4Plaq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2HaarAlgebra
  (PE pe_refl pe_trans pe_symm pe_assoc pe_comm pe_mulL pe_mulR)
open YMGap.Continuum.SU2TorusRPSplitTK (prod_congr)
open YMGap.Continuum.SU2WilsonTrunc (obsTK)
open YMGap.Continuum.SU2WilsonObsActivity (chi)

/-- A selected root is inserted once; the remaining factors retain their
original selections. The guards exclude missing or duplicated roots. -/
theorem obsTK_extract (links : List Z4Link) (N K : Nat)
    (P S : List Z4Plaq) (p : Z4Plaq)
    (hP : P.Nodup) (hp : p ∈ P) (hpS : p ∉ S) :
    PE links.length
      (prodPoly (obsTK links N K (p :: S)) P)
      (polyMul (polyAdd polyOne (chi links N p))
        (prodPoly (obsTK links N K S) P)) := by
  induction P with
  | nil => exact absurd hp List.not_mem_nil
  | cons r P ih =>
    have hn := List.nodup_cons.mp hP
    by_cases hr : r = p
    · subst r
      have hrest : PE links.length
          (prodPoly (obsTK links N K (p :: S)) P)
          (prodPoly (obsTK links N K S) P) :=
        prod_congr P fun q hq => by
          have hqp : q ≠ p := fun h => hn.1 (h ▸ hq)
          have he : obsTK links N K (p :: S) q = obsTK links N K S q := by
            unfold obsTK
            simp only [List.mem_cons, hqp, false_or]
          rw [he]
          exact pe_refl _ _
      have hhead : obsTK links N K (p :: S) p =
          polyMul (polyAdd polyOne (chi links N p)) (obsTK links N K S p) := by
        unfold obsTK
        rw [if_pos (List.mem_cons_self ..), if_neg hpS]
      change PE links.length
        (polyMul (obsTK links N K (p :: S) p)
          (prodPoly (obsTK links N K (p :: S)) P))
        (polyMul (polyAdd polyOne (chi links N p))
          (polyMul (obsTK links N K S p) (prodPoly (obsTK links N K S) P)))
      rw [hhead]
      exact pe_trans _ (pe_mulL _ _ hrest) (pe_assoc _ _ _ _)
    · have hpP : p ∈ P := (List.mem_cons.mp hp).resolve_left (fun h => hr h.symm)
      have hhead : obsTK links N K (p :: S) r = obsTK links N K S r := by
        unfold obsTK
        simp only [List.mem_cons, hr, false_or]
      change PE links.length
        (polyMul (obsTK links N K (p :: S) r)
          (prodPoly (obsTK links N K (p :: S)) P))
        (polyMul (polyAdd polyOne (chi links N p))
          (polyMul (obsTK links N K S r) (prodPoly (obsTK links N K S) P)))
      rw [hhead]
      refine pe_trans _ (pe_mulL _ _ (ih hn.2 hpP)) ?_
      refine pe_trans _ (pe_symm _ (pe_assoc _ _ _ _)) ?_
      exact pe_trans _ (pe_mulR _ _ (pe_comm _ _ _)) (pe_assoc _ _ _ _)

end YMGap.Continuum.SU2WilsonObsExtraction

#print axioms YMGap.Continuum.SU2WilsonObsExtraction.obsTK_extract
