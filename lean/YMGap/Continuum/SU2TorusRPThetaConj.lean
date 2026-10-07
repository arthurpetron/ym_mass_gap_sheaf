/-
# Torus RP assembly (d1b): the conjugation half of Θ on link variables

* `parity_var`: the selected parity of the variable monomial `x_i` is `decide (i < N) && S i`.
* `sign_polyVar`: the sign flip negates `x_i` exactly when `i` is selected.
* `conj_coord`: `signSelectedPolynomial (4n) (conjSel T)` sends block `b < n` to `conj (coord b)` if `T b`, and fixes
  it otherwise (literal equality).
* `theta_linkVar`: with `Θpoly = sign(conjSel T) ∘ reindex(linkInv f)`, `Θpoly (linkVar ℓ)` is QPE to
  `linkVar (f ℓ)`, conjugated when `T` selects the block of `f ℓ`. Take `T` = the temporal blocks: since `reflLink`
  reverses temporal links, this is the polynomial form of Θ on every link.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (the `haar_step` chain and the `Π TK` factorisation remain).
-/

import YMGap.Continuum.SU2TorusRPThetaPoly

namespace YMGap.Continuum.SU2TorusRPThetaConj

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (varMono)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (selectedExponentParity signSelectedPolynomial signSelectedTerm reindexQuaternionPolynomial)
open YMGap.Continuum.SU2TorusRPConj (step foldl_xor parity_eq)
open YMGap.Continuum.SU2TorusRPHaar (conjSel)
open YMGap.Continuum.SU2TorusRPSubst (QPE qsub qpe_trans)
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter (exponentAt_varMono)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar)

theorem fold_var (S : Nat → Bool) (i : Nat) : ∀ l : List Nat, l.Nodup →
    l.foldl (step S (varMono i)) false = (decide (i ∈ l) && S i)
  | [], _ => by simp
  | c :: l, hnd => by
    have hnd' := List.nodup_cons.mp hnd
    simp only [List.foldl_cons]
    rw [foldl_xor, fold_var S i l hnd'.2]
    unfold step
    rw [exponentAt_varMono]
    by_cases hc : c = i
    · subst hc
      have : decide (c ∈ l) = false := decide_eq_false hnd'.1
      rw [this, if_pos rfl, decide_eq_true (List.mem_cons_self ..)]
      cases S c <;> rfl
    · have e1 : decide (i ∈ c :: l) = decide (i ∈ l) := by
        cases h1 : decide (i ∈ l) with
        | false => exact decide_eq_false fun h => (List.mem_cons.mp h).elim (fun h => hc h.symm)
                    (fun h => absurd h (of_decide_eq_false h1))
        | true => exact decide_eq_true (List.mem_cons_of_mem _ (of_decide_eq_true h1))
      rw [e1, if_neg hc]
      cases S c <;> cases decide (i ∈ l) <;> cases S i <;> rfl

theorem nodup_range' : ∀ N : Nat, (List.range N).Nodup
  | 0 => List.nodup_nil
  | N + 1 => by
    rw [List.range_succ]
    exact List.nodup_append.mpr ⟨nodup_range' N, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      fun a ha b hb => by
        have h1 := List.mem_range.mp ha
        rw [List.mem_singleton.mp hb]; exact Nat.ne_of_lt h1⟩

theorem parity_var (N : Nat) (S : Nat → Bool) (i : Nat) :
    selectedExponentParity N S (varMono i) = (decide (i < N) && S i) := by
  rw [parity_eq, fold_var S i _ (nodup_range' N)]
  cases h : decide (i < N)
  · rw [decide_eq_false fun hm => (of_decide_eq_false h) (List.mem_range.mp hm)]
  · rw [decide_eq_true (List.mem_range.mpr (of_decide_eq_true h))]

theorem sign_polyVar (N : Nat) (S : Nat → Bool) (i : Nat) :
    signSelectedPolynomial N S (polyVar i) =
      if (decide (i < N) && S i) then polyNeg (polyVar i) else polyVar i := by
  show [signSelectedTerm N S (varMono i, 1)] = _
  unfold signSelectedTerm; rw [parity_var]
  cases (decide (i < N) && S i) <;> rfl

theorem conj_coord (n : Nat) (T : Nat → Bool) (b : Nat) (hb : b < n) :
    qsub (signSelectedPolynomial (4 * n) (conjSel T)) (PolyQuaternion.coordinateVariable b) =
      if T b then PolyQuaternion.conj (PolyQuaternion.coordinateVariable b)
      else PolyQuaternion.coordinateVariable b := by
  have hc : ∀ c, c < 4 → (decide (4 * b + c < 4 * n) && conjSel T (4 * b + c)) = (T b && (c != 0)) := by
    intro c hc
    rw [decide_eq_true (by omega)]
    unfold conjSel
    rw [show (4 * b + c) / 4 = b by omega, show (4 * b + c) % 4 = c by omega]; rfl
  unfold qsub PolyQuaternion.coordinateVariable
  rw [sign_polyVar, sign_polyVar, sign_polyVar, sign_polyVar,
    show 4 * b = 4 * b + 0 from rfl, hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)]
  cases T b <;> rfl

/-- Θ on link variables: reindex by `linkInv f`, then conjugate the `T`-selected blocks. -/
theorem theta_linkVar (links : List Z4Link) (f : Z4Link → Z4Link) (hnd : links.Nodup)
    (hcl : ∀ ℓ ∈ links, f ℓ ∈ links) (hinv : ∀ ℓ ∈ links, f (f ℓ) = ℓ) (T : Nat → Bool)
    {ℓ : Z4Link} (h : ℓ ∈ links) :
    QPE links.length
      (qsub (fun p => signSelectedPolynomial (4 * links.length) (conjSel T)
        (reindexQuaternionPolynomial (SU2TorusRPThetaPoly.linkInv links f hnd hcl hinv) p)) (linkVar links ℓ))
      (if T (links.idxOf (f ℓ)) then PolyQuaternion.conj (linkVar links (f ℓ)) else linkVar links (f ℓ)) := by
  have hr := SU2TorusRPThetaPoly.reindex_linkVar links f hnd hcl hinv h
  have hb := List.idxOf_lt_length_of_mem (hcl ℓ h)
  have e := conj_coord links.length T _ hb
  unfold linkVar
  rw [← e]
  exact ⟨SU2TorusRPConjCongr.conj_peCongr _ _ _ hr.s, SU2TorusRPConjCongr.conj_peCongr _ _ _ hr.i,
    SU2TorusRPConjCongr.conj_peCongr _ _ _ hr.j, SU2TorusRPConjCongr.conj_peCongr _ _ _ hr.k⟩

end YMGap.Continuum.SU2TorusRPThetaConj

#print axioms YMGap.Continuum.SU2TorusRPThetaConj.parity_var
#print axioms YMGap.Continuum.SU2TorusRPThetaConj.conj_coord
#print axioms YMGap.Continuum.SU2TorusRPThetaConj.theta_linkVar
