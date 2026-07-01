/-
The character *-algebra bridge: the `δ_{mn}·reflWeight` orthonormality of the
Schur-diagonal reflection datum, and the honest named residual for the physical
`E_Λ → cinner` identification.

# What this module delivers (genuine, axiom-clean, no Haar)

The target is the reflection two-site pairing
`E_Λ(θ(χ_m)*·χ_n) = δ_{mn}·e^{−t·C₂(m+1)} = δ_{mn}·reflWeight t ht (m+1)`,
i.e. the diagonal, Schur-orthogonalized OS2 reflection Schwinger form on the
character basis.  Realizing the character basis element `χ_m` as the coordinate
unit vector `basisVec m` (`basisVec m s = if s = m then 1 else 0`), the
Schur-diagonal completed inner product of `WilsonSchurIdentities.charHilbert`
evaluates on the basis to the diagonal:

    `charHilbert.cinner (basisVec m) (basisVec n)
       = if m = n then ⟦ reflWeight t ht (m+1) ⟧ else ⟦ 0 ⟧`     (m,n < N).

This is `charHilbert_cinner_basis_orthogonal`, proved here as a pure finite-sum
collapse: each summand of `Σ_{s<N} reflWeight t ht (s+1)·(basisVec m s · basisVec n s)`
carries the factor `[s=m]·[s=n]`, so the sum collapses to the single `s=m=n`
term (diagonal) or to `0` (off-diagonal).  Same machinery lineage as
`WilsonSchurIdentities.charSchurSelf/charSchurT`; `[propext, Quot.sound]` only.

The **spin shift** `i ↦ i+1` is inherited from `charHilbert` (the excited tower
runs on `vac⊥`, excluding the trivial rep `s=0`), so the target's `μ_m` is
`reflWeight t ht (m+1)`.

# What this does NOT close — the honest residual (AGENTS.md Rule 6)

The identification of `charHilbert.cinner` with the PHYSICAL finite-volume
reflection functional `E_Λ(θ(·)*·)` (whose moments are rational Haar sums, not
the irrational heat-kernel coefficient `e^{−t·C₂}`) is NOT a finite algebraic
repackaging.  Its content is exactly Peter–Weyl / Schur orthogonality over a
genuine double Haar integral
`∫∫ χ_μ(g₊)·χ̄_ν(g₋)·χ_λ(g₊ g₋⁻¹) = δ_{μλ}·δ_{νλ}/d_λ`, composed with
`a_λ = d_λ·e^{−t·C₂(λ)}` — an integral the constructive Q'/CReal stack
deliberately does not build (moments are *defined*, not integrated).  It is
recorded here as the Type-level datum `PhysicalReflectionSchurBridge`, which is
NOT inhabited; `physical_reflection_diagonal_of_bridge` shows that any inhabitant
would deliver the full physical diagonalization by composition with the proved
orthonormality — so the residual is precisely the Haar-Schur bridge, stated, not
hidden.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`, no
`native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.WilsonSchurIdentities
import YMGap.Continuum.ReflectionPositivity
import YMGap.Constructive.CRealExp

open YMGap.Constructive
open YMGap.Continuum.ReflectionPositivity
open YMGap.Continuum.WilsonSchurIdentities

namespace YMGap.Continuum.WilsonCharBridge

/-! ## 1. The character basis as coordinate unit vectors -/

/-- **The character basis element** `χ_m`, realized as the coordinate unit
vector on the spin-coefficient carrier `Nat → Q'`: `basisVec m s = [s = m]`. -/
def basisVec (m : Nat) : Nat → Q' := fun s => if s = m then (1 : Q') else 0

/-- Off the diagonal index `m`, the basis product vanishes: for `s ≠ m`,
`basisVec m s · basisVec n s ≃ 0` (the first factor is `0`). -/
theorem basisVec_prod_offdiag (m n s : Nat) (h : s ≠ m) :
    (basisVec m s * basisVec n s).eqv 0 := by
  unfold basisVec
  rw [if_neg h]
  exact Q'.zero_mul_eqv _

/-- For distinct labels `m ≠ n`, the basis product vanishes at EVERY index `s`:
at most one of `s = m`, `s = n` can hold. -/
theorem basisVec_prod_ne (m n : Nat) (hmn : m ≠ n) (s : Nat) :
    (basisVec m s * basisVec n s).eqv 0 := by
  rcases Nat.decEq s m with hsm | hsm
  · -- s ≠ m: first factor is 0
    unfold basisVec
    rw [if_neg hsm]
    exact Q'.zero_mul_eqv _
  · -- s = m, hence s ≠ n (else m = n): second factor is 0
    have hsn : s ≠ n := by
      intro hh
      exact hmn (by rw [← hsm]; exact hh)
    unfold basisVec
    rw [if_neg hsn]
    exact Q'.mul_zero_eqv _

/-- On the diagonal, `basisVec m m · basisVec m m ≃ 1`. -/
theorem basisVec_diag_eqv_one (m : Nat) : (basisVec m m * basisVec m m).eqv 1 := by
  unfold basisVec
  rw [if_pos (rfl : m = m)]
  exact Q'.one_mul_eqv 1

/-! ## 2. `CReal`-level scalar helpers (all pointwise, limit-free) -/

/-- `add x czero ≃ x` (pointwise `x_n + 0 = x_n`). -/
theorem add_czero_equiv (x : CReal) : CReal.Equiv (CReal.add x CReal.czero) x :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_of_eq' (Q'.add_zero' (x.approx n)))

/-- `add czero x ≃ x` (pointwise `0 + x_n = x_n`). -/
theorem czero_add_equiv (x : CReal) : CReal.Equiv (CReal.add CReal.czero x) x :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_of_eq' (Q'.zero_add' (x.approx n)))

/-- If the rational factor is `≃ 0` then `W·ofQ' q ≃ 0` (pointwise). -/
theorem mul_ofQ'_eqvZero (W : CReal) {q : Q'} (hq : q.eqv 0) :
    CReal.Equiv (CReal.mul W (CReal.ofQ' q)) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (W.approx n) q 0 hq)
      (Q'.mul_zero_eqv (W.approx n)))

/-- If the rational factor is `≃ 1` then `W·ofQ' q ≃ W` (pointwise). -/
theorem mul_ofQ'_eqvSelf (W : CReal) {q : Q'} (hq : q.eqv 1) :
    CReal.Equiv (CReal.mul W (CReal.ofQ' q)) W :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (W.approx n) q 1 hq)
      (Q'.mul_one_eqv (W.approx n)))

/-! ## 3. Finite-sum single-support collapse (`CReal.Equiv`) -/

/-- If every summand is `≃ 0` then the finite `csum` is `≃ 0`. -/
theorem csum_zero_of_all (g : Nat → CReal)
    (hz : ∀ s, CReal.Equiv (g s) CReal.czero) :
    ∀ N, CReal.Equiv (CReal.csum g N) CReal.czero
  | 0 => CReal.Equiv.refl CReal.czero
  | N + 1 =>
      CReal.Equiv.trans
        (CReal.Equiv.trans
          (CReal.add_congr_left (csum_zero_of_all g hz N))
          (CReal.add_congr_right (hz N)))
        (czero_add_equiv CReal.czero)

/-- If every summand strictly below `N` (all indices `< N` differ from `m`, here
enforced by `N ≤ m`) is `≃ 0`, then `csum g N ≃ 0`. -/
theorem csum_zero_below (g : Nat → CReal) (m : Nat)
    (hz : ∀ s, s ≠ m → CReal.Equiv (g s) CReal.czero) :
    ∀ N, N ≤ m → CReal.Equiv (CReal.csum g N) CReal.czero
  | 0, _ => CReal.Equiv.refl CReal.czero
  | N + 1, h => by
      have hNm : N < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self N) h
      have ih := csum_zero_below g m hz N (Nat.le_of_lt hNm)
      have hgN : CReal.Equiv (g N) CReal.czero :=
        hz N (fun heq => Nat.lt_irrefl m (heq ▸ hNm))
      exact CReal.Equiv.trans
        (CReal.Equiv.trans (CReal.add_congr_left ih) (CReal.add_congr_right hgN))
        (czero_add_equiv CReal.czero)

/-- **Single-support collapse.**  If every summand `g s` with `s ≠ m` is `≃ 0`
and `m < N`, then `csum g N ≃ g m`. -/
theorem csum_collapse (g : Nat → CReal) (m : Nat)
    (hz : ∀ s, s ≠ m → CReal.Equiv (g s) CReal.czero) :
    ∀ N, m < N → CReal.Equiv (CReal.csum g N) (g m)
  | 0, h => absurd h (Nat.not_lt_zero m)
  | N + 1, h => by
      rcases Nat.lt_or_ge m N with hlt | hge
      · -- m < N: fold the top term (which is ≃ 0) away, use IH
        have ih := csum_collapse g m hz N hlt
        have hgN : CReal.Equiv (g N) CReal.czero :=
          hz N (fun heq => Nat.lt_irrefl m (heq ▸ hlt))
        exact CReal.Equiv.trans
          (CReal.Equiv.trans (CReal.add_congr_left ih) (CReal.add_congr_right hgN))
          (add_czero_equiv (g m))
      · -- m = N: the tail below N collapses to 0, leaving the top term g N = g m
        have hmN : m = N := Nat.le_antisymm (Nat.lt_succ_iff.mp h) hge
        have hz0 : CReal.Equiv (CReal.csum g N) CReal.czero :=
          csum_zero_below g m hz N (Nat.le_of_eq hmN.symm)
        have hchain : CReal.Equiv (CReal.add (CReal.csum g N) (g N)) (g N) :=
          CReal.Equiv.trans (CReal.add_congr_left hz0) (czero_add_equiv (g N))
        rw [hmN]
        exact hchain

/-! ## 4. The δ_{mn}·reflWeight orthonormality on the Schur-diagonal datum -/

/-- **The character-basis orthonormality of the Schur-diagonal reflection datum.**
`charHilbert.cinner (basisVec m) (basisVec n) = δ_{mn}·⟦reflWeight t ht (m+1)⟧`
(the `s=0` trivial rep is excluded, hence the spin shift `m ↦ m+1`).  Proved by
finite-sum single-support collapse — no Haar integral, `[propext, Quot.sound]`. -/
theorem charHilbert_cinner_basis_orthogonal
    (t : Q') (ht : (0 : Q') ≤ t) (N m n : Nat) (hm : m < N) (hn : n < N) :
    (charHilbert t ht N).cinner (basisVec m) (basisVec n)
      = if m = n then Quotient.mk CReal.crealSetoid (reflWeight t ht (m + 1))
        else Quotient.mk CReal.crealSetoid CReal.czero := by
  have hcinner : (charHilbert t ht N).cinner (basisVec m) (basisVec n)
      = Quotient.mk CReal.crealSetoid
          (CReal.csum (fun s => CReal.mul (reflWeight t ht (s + 1))
            (CReal.ofQ' (basisVec m s * basisVec n s))) N) := rfl
  rw [hcinner]
  rcases Nat.decEq m n with hmn | hmn
  · -- m ≠ n: every summand vanishes
    rw [if_neg hmn]
    refine Quotient.sound ?_
    exact csum_zero_of_all _
      (fun s => mul_ofQ'_eqvZero _ (basisVec_prod_ne m n hmn s)) N
  · -- m = n: collapse to the diagonal term, identify with reflWeight
    rw [if_pos hmn]
    refine Quotient.sound ?_
    subst hmn
    have hcol := csum_collapse
      (fun s => CReal.mul (reflWeight t ht (s + 1))
        (CReal.ofQ' (basisVec m s * basisVec m s)))
      m
      (fun s hs => mul_ofQ'_eqvZero _ (basisVec_prod_offdiag m m s hs)) N hm
    refine CReal.Equiv.trans hcol ?_
    exact mul_ofQ'_eqvSelf (reflWeight t ht (m + 1)) (basisVec_diag_eqv_one m)

/-- **Diagonal specialization.**  `cinner (basisVec m) (basisVec m) =
⟦reflWeight t ht (m+1)⟧` — the `μ_m` normalization of the character basis. -/
theorem charHilbert_cinner_basis_diag
    (t : Q') (ht : (0 : Q') ≤ t) (N m : Nat) (hm : m < N) :
    (charHilbert t ht N).cinner (basisVec m) (basisVec m)
      = Quotient.mk CReal.crealSetoid (reflWeight t ht (m + 1)) := by
  rw [charHilbert_cinner_basis_orthogonal t ht N m m hm hm, if_pos rfl]

/-- **Off-diagonal specialization.**  `cinner (basisVec m) (basisVec n) = ⟦0⟧`
for `m ≠ n` — orthogonality of distinct character basis elements. -/
theorem charHilbert_cinner_basis_offdiag
    (t : Q') (ht : (0 : Q') ≤ t) (N m n : Nat) (hm : m < N) (hn : n < N)
    (hmn : m ≠ n) :
    (charHilbert t ht N).cinner (basisVec m) (basisVec n)
      = Quotient.mk CReal.crealSetoid CReal.czero := by
  rw [charHilbert_cinner_basis_orthogonal t ht N m n hm hn, if_neg hmn]

/-! ## 5. The honest residual: the physical `E_Λ → cinner` Haar-Schur bridge

The physical finite-volume reflection functional's identification with the
Schur-diagonal `charHilbert.cinner` is NOT a finite repackaging; its content is
Peter–Weyl / Schur orthogonality over a genuine double Haar integral, absent from
the constructive stack.  It is recorded as the following Type-level datum, which
is deliberately NOT inhabited here. -/

/-- **The physical reflection / Schur–Haar bridge (named residual, not inhabited).**
An inhabitant packages the physical finite-volume reflection two-site functional
`Rphys m n` on characters, together with the Peter–Weyl/Schur double-Haar
identification of it with the Schur-diagonal `charHilbert.cinner`.  Constructing
such a term requires the double Haar integral
`∫∫ χ_μ(g₊)·χ̄_ν(g₋)·χ_λ(g₊ g₋⁻¹) = δ_{μλ}·δ_{νλ}/d_λ` (composed with
`a_λ = d_λ·e^{−t·C₂(λ)}`) — the honest analytic residual. -/
structure PhysicalReflectionSchurBridge (t : Q') (ht : (0 : Q') ≤ t) (N : Nat) :
    Type where
  /-- The physical finite-volume reflection two-site functional on characters. -/
  Rphys : Nat → Nat → CReal.RC
  /-- Peter–Weyl / Schur double-Haar diagonalization: the physical reflection
  functional equals the Schur-diagonal `charHilbert` inner product on the basis. -/
  diagonalizes : ∀ m n, m < N → n < N →
    Rphys m n = (charHilbert t ht N).cinner (basisVec m) (basisVec n)

/-- **Conditional physical diagonalization.**  ANY inhabitant of the Haar-Schur
bridge yields the full physical `δ_{mn}·reflWeight` diagonalization, by composing
its (unproved) Schur-orthogonality field with the proved basis orthonormality.
The bridge itself remains the sole honest residual. -/
theorem physical_reflection_diagonal_of_bridge
    (t : Q') (ht : (0 : Q') ≤ t) (N : Nat)
    (B : PhysicalReflectionSchurBridge t ht N)
    (m n : Nat) (hm : m < N) (hn : n < N) :
    B.Rphys m n
      = if m = n then Quotient.mk CReal.crealSetoid (reflWeight t ht (m + 1))
        else Quotient.mk CReal.crealSetoid CReal.czero := by
  rw [B.diagonalizes m n hm hn, charHilbert_cinner_basis_orthogonal t ht N m n hm hn]

end YMGap.Continuum.WilsonCharBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonCharBridge.basisVec_prod_offdiag
#print axioms YMGap.Continuum.WilsonCharBridge.basisVec_prod_ne
#print axioms YMGap.Continuum.WilsonCharBridge.basisVec_diag_eqv_one
#print axioms YMGap.Continuum.WilsonCharBridge.csum_zero_of_all
#print axioms YMGap.Continuum.WilsonCharBridge.csum_collapse
#print axioms YMGap.Continuum.WilsonCharBridge.charHilbert_cinner_basis_orthogonal
#print axioms YMGap.Continuum.WilsonCharBridge.charHilbert_cinner_basis_diag
#print axioms YMGap.Continuum.WilsonCharBridge.charHilbert_cinner_basis_offdiag
#print axioms YMGap.Continuum.WilsonCharBridge.physical_reflection_diagonal_of_bridge
