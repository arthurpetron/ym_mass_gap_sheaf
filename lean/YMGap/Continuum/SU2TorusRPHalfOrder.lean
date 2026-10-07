/-
# Torus RP assembly (d3b), item 3 step 1: ordering the links as `L ++ f(L)` makes Θ the half shift

For `links = L ++ L.map f` (nodup, closed under the involution `f`), the block involution `linkInv links f` sends
`k ↦ k + |L|` for `k < |L|`. With `SU2TorusRPShiftBridge.reindex_shift`, the reindex half of Θpoly is
`shiftPoly |L|` on polynomials supported in `L`'s blocks (`reindex_eq_shift`).

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (still to do: the crossing links, which are Θ-fixed so not of this form
and must be split first; the pos/neg/cross factorisation; and `hW`).
-/

import YMGap.Continuum.SU2TorusRPShiftBridge

namespace YMGap.Continuum.SU2TorusRPHalfOrder

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2TorusRPThetaPoly (d0 linkInv idxOf_getD getD_mem)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (reindexQuaternionPolynomial)
open YMGap.Continuum.SU2HaarAlgebra (PE)
open YMGap.Continuum.SU2MultiLinkHaarFactorization (shiftPoly)
open YMGap.Continuum.SU2TorusRPCore (Sup)

theorem getD_append_lt : ∀ (L1 L2 : List Z4Link) (k : Nat), k < L1.length → (L1 ++ L2).getD k d0 = L1.getD k d0
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: L1, L2, k + 1, h => getD_append_lt L1 L2 k (Nat.lt_of_succ_lt_succ h)

theorem getD_map (f : Z4Link → Z4Link) : ∀ (L : List Z4Link) (k : Nat), k < L.length →
    (L.map f).getD k d0 = f (L.getD k d0)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: L, k + 1, h => getD_map f L k (Nat.lt_of_succ_lt_succ h)

theorem idxOf_append_nmem (x : Z4Link) : ∀ (L1 L2 : List Z4Link), x ∉ L1 →
    (L1 ++ L2).idxOf x = L1.length + L2.idxOf x
  | [], _, _ => (Nat.zero_add _).symm
  | y :: L1, L2, h => by
    have hne : (y == x) = false := by
      cases hb : (y == x) with
      | false => rfl
      | true => exact absurd (List.mem_cons.mpr (Or.inl (beq_iff_eq.mp hb).symm)) h
    show (y :: (L1 ++ L2)).idxOf x = (L1.length + 1) + L2.idxOf x
    rw [List.idxOf_cons, hne, cond_false, idxOf_append_nmem x L1 L2 (fun hm => h (List.mem_cons_of_mem _ hm))]
    omega

variable (L : List Z4Link) (f : Z4Link → Z4Link) (hnd : (L ++ L.map f).Nodup)
  (hcl : ∀ ℓ ∈ L ++ L.map f, f ℓ ∈ L ++ L.map f) (hinv : ∀ ℓ ∈ L ++ L.map f, f (f ℓ) = ℓ)

theorem half_map (k : Nat) (hk : k < L.length) :
    (linkInv (L ++ L.map f) f hnd hcl hinv).map k = k + L.length := by
  have hlen : k < (L ++ L.map f).length := by simp; omega
  show (if k < (L ++ L.map f).length then _ else _) = _
  rw [if_pos hlen, getD_append_lt L _ k hk]
  have hd := (List.nodup_append.mp hnd)
  have hmem : f (L.getD k d0) ∈ L.map f := List.mem_map_of_mem (getD_mem hk)
  have hnm : f (L.getD k d0) ∉ L := fun h => hd.2.2 _ h _ hmem rfl
  rw [idxOf_append_nmem _ L _ hnm, ← getD_map f L k hk,
    idxOf_getD (L.map f) hd.2.1 k (by simpa using hk)]
  omega

theorem reindex_eq_shift (hlen : (L ++ L.map f).length = L.length + L.length) (X : RatPoly) (hX : Sup L.length X) :
    PE (L.length + L.length) (reindexQuaternionPolynomial (hlen ▸ linkInv (L ++ L.map f) f hnd hcl hinv) X)
      (shiftPoly L.length X) := by
  refine SU2TorusRPShiftBridge.reindex_shift _ (fun k hk => ?_) X hX
  have := half_map L f hnd hcl hinv k hk
  revert this
  generalize linkInv (L ++ L.map f) f hnd hcl hinv = σ
  generalize (L ++ L.map f).length = m at hlen σ ⊢
  subst hlen; intro h; exact h

end YMGap.Continuum.SU2TorusRPHalfOrder

#print axioms YMGap.Continuum.SU2TorusRPHalfOrder.half_map
#print axioms YMGap.Continuum.SU2TorusRPHalfOrder.reindex_eq_shift
