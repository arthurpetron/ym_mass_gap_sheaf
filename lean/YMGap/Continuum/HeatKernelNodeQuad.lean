/-
**Inhabiting the off-diagonal-OS2 residual `NodeQuadrature`** — the heat-kernel
character-product Gram as a literal positive node quadrature, for a genuine
positive-type SU(2) moment measure.

# What this module closes

`HeatKernelGramSOS` reduced off-diagonal OS2 of the rational heat-kernel Gram to
ONE Type-level residual, `NodeQuadrature M`: a finite, nonnegative-weight node
quadrature reproducing the Clebsch–Gordan moment Gram `qGram M` entrywise,

    qGram M a b  ≃  Σ_{k<r} ω_k · U_a(x_k)·U_b(x_k)      (U = SU(2) character).

That module left the residual *uninhabited* (only the conditional theorems
`qGram_gramRep` / `qGram_quadForm_nonneg`).  Here we INHABIT it.

  * `atomicNodeQuadrature` — **the generic constructor.**  ANY finite rational
    atomic measure `μ = Σ_{k<r} ω_k δ_{x_k}` with `ω_k ≥ 0` whose character
    moments `m_s = Σ_k ω_k U_s(x_k)` are all `≥ 0` (the *positive-type* /
    Bochner condition, `hpos`) yields a `NodeQuadrature` for its own moment data
    `atomicMoments`.  The `reproduce` field is proved unconditionally from the
    GENERAL pointwise Clebsch–Gordan fusion `U_a·U_b = Σ_r U_{|a−b|+2r}`
    (`ChebOrthoMatrix.chebU_fusion`) — so the per-entry moment reproduction IS
    the fusion identity summed over the nodes (swap + `const_mul_finSum`).  This
    reduces `NodeQuadrature` to the single sharp residual `hpos` (positive-type),
    everything else discharged.

  * `deltaENodeQuadrature` — **a fully-closed, axiom-clean inhabitation.**  The
    `t = 0` heat kernel `K_0 = δ_e` (Dirac at the identity): one node `x = 1`,
    weight `1`.  Its moments are `m_s = U_s(1) = s + 1 ≥ 0` (`U_at_one`,
    `U_at_one_nonneg`), so `hpos` is DISCHARGED and `deltaENodeQuadrature` is a
    genuine `NodeQuadrature` on real positive-type data.  Consequently
    `deltaE_offdiag_OS2` is the off-diagonal OS2 of the `δ_e` heat-kernel Gram —
    `qGram_quadForm_nonneg` turned from conditional into an INSTANTIATED theorem.

# Honesty / scope (AGENTS.md Rule 6)

This does NOT close off-diagonal OS2 for the genuine `t > 0` heat kernel
`m_s = (s+1)·a^{s(s+2)}`: that moment matrix is full-rank / strictly
positive-definite, so NO finite rational atomic measure reproduces it entrywise
over all `(a,b)` (the classical Gauss–Chebyshev rule needs irrational nodes
`cos(kπ/(r+1))`).  For that the route stays the truncated/limit
`RiemannSOS.MomentIntegralIdentity`.  What is closed here is the residual for the
finite-rank positive-type cases — including the `t = 0` kernel EXACTLY — and the
generic reduction of `NodeQuadrature` to the positive-type condition `hpos`,
whose finite shadow is the proved Bochner positivity
`ReflectionPositivity.heatKernel_nonnegCharCoeffs`.

# Reuse / provenance

The `GramRep` carrier and the Schur/Hadamard SOS rearrangement consumed
downstream are the Mathlib-free constructive transfer of the external 4D-GFF
formalization (Douglas–Hoback–Mei–Nissim, "Formalization of QFT",
arXiv:2603.15770; repository `mrdouglasny/OSforGFF`); the general pointwise
fusion `chebU_fusion` is the repo's own `ChebOrthoMatrix` linearization.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (inherited from the reused `Q'`/`finSum`
algebra, the fusion identity, and `omega`'s `Int` helpers).  No `Classical.*`,
no `sorryAx`, no `native_decide`, no Mathlib.
-/

import YMGap.Continuum.HeatKernelGramSOS
import YMGap.Continuum.ChebOrthoMatrix

namespace YMGap.Continuum.HeatKernelNodeQuad

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.HeatKernelGramSOS

/-! ## 1. The general fusion bridge in the `qGram` shape

The entrywise promoter: the SU(2) character product `U_a·U_b` equals the
Clebsch–Gordan fusion sum `Σ_{r=0}^{min} U_{|a−b|+2r}` — exactly the moment-index
pattern of `qGram`.  This is `ChebOrthoMatrix.chebU_fusion` re-expressed against
`HeatKernelGramSOS.fusionLow` (defeq to `ChebOrthogonality.fusionLow`). -/

/-- **The U-product fusion bridge** `U_a(x)·U_b(x) ≃ Σ_{r<min a b+1} U_{|a−b|+2r}(x)`,
the general Clebsch–Gordan linearization, in the `fusionLow`/`min` shape that
`qGram` consumes.  Reuses the proved general fusion `ChebOrthoMatrix.chebU_fusion`. -/
theorem U_fusion_gram (a b : Nat) (x : Q') :
    (Cheb.U a x * Cheb.U b x).eqv
      (finSum (fun j => Cheb.U (fusionLow a b + 2 * j) x) (min a b + 1)) := by
  have h := ChebOrthoMatrix.chebU_fusion a b x
  unfold ChebOrthogonality.Ufusion at h
  exact h

/-! ## 2. The generic atomic-measure constructor

A finite rational atomic measure `μ = Σ_{k<r} ω_k δ_{x_k}` with `ω_k ≥ 0` has
character moments `m_s = Σ_{k<r} ω_k U_s(x_k)`.  When all moments are `≥ 0`
(positive-type, the field `hpos`), this is a `QMomentData`, and the moment Gram
`qGram` is reproduced entrywise by the node quadrature — proved from the fusion
bridge. -/

/-- The moments `m_s = Σ_{k<r} ω_k U_s(x_k)` of a finite atomic measure, packaged
as `QMomentData`; `hpos` (positive-type) is the sole residual carried in. -/
def atomicMoments (r : Nat) (node weight : Nat → Q')
    (hpos : ∀ s, (0 : Q') ≤ finSum (fun k => weight k * Cheb.U s (node k)) r) :
    QMomentData where
  m := fun s => finSum (fun k => weight k * Cheb.U s (node k)) r
  m_nonneg := hpos

/-- **The generic `NodeQuadrature` inhabitant.**  For any finite atomic measure
with nonnegative weights (`hw`) and nonnegative character moments (`hpos`), the
moment Gram `qGram (atomicMoments …)` is reproduced entrywise by the node
quadrature.  The `reproduce` proof is unconditional: swap the moment/quadrature
sums (`finSum_swap`), pull each weight out (`const_mul_finSum`), and apply the
general pointwise fusion `U_fusion_gram` at each node.  So `NodeQuadrature` is
reduced to the single positive-type residual `hpos`. -/
def atomicNodeQuadrature (r : Nat) (node weight : Nat → Q')
    (hw : ∀ k, (0 : Q') ≤ weight k)
    (hpos : ∀ s, (0 : Q') ≤ finSum (fun k => weight k * Cheb.U s (node k)) r) :
    NodeQuadrature (atomicMoments r node weight hpos) where
  r := r
  node := node
  weight := weight
  weight_nonneg := hw
  reproduce := by
    intro a b
    show (finSum (fun j =>
            finSum (fun k => weight k * Cheb.U (fusionLow a b + 2 * j) (node k)) r)
            (min a b + 1)).eqv
          (finSum (fun k => weight k * (Cheb.U a (node k) * Cheb.U b (node k))) r)
    -- swap the (j over fusion terms) and (k over nodes) sums
    refine Q'.eqv_trans _ _ _
      (finSum_swap
        (fun j k => weight k * Cheb.U (fusionLow a b + 2 * j) (node k)) (min a b + 1) r) ?_
    -- per node `k`, the inner fusion sum collapses to `ω_k · (U_a·U_b)(x_k)`
    refine finSum_eqv_congr _ _ (fun k => ?_) r
    -- Σ_j ω_k·U_{low+2j}(x_k) ≃ ω_k·Σ_j U_{low+2j}(x_k) ≃ ω_k·(U_a·U_b)(x_k)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (const_mul_finSum (fun j => Cheb.U (fusionLow a b + 2 * j) (node k))
          (weight k) (min a b + 1))) ?_
    exact Q'.mul_eqv_congr_left (weight k) _ _ (Q'.eqv_symm (U_fusion_gram a b (node k)))

/-! ## 3. A fully-closed inhabitation: the `t = 0` heat kernel `δ_e`

`K_0 = δ_e` (Dirac at the identity) is the one-node measure at `x = 1` with
weight `1`.  Its character moments are `m_s = U_s(1) = s + 1`, manifestly `≥ 0`,
so `hpos` is discharged outright — a genuine positive-type measure. -/

/-- `U_s(1) = s + 1` and `U_{s+1}(1) = s + 2`, proved simultaneously by the
three-term recurrence (each needed in the other's step). -/
theorem U_at_one_pair (s : Nat) :
    (Cheb.U s 1).eqv (Q'.ofNat (s + 1)) ∧ (Cheb.U (s + 1) 1).eqv (Q'.ofNat (s + 2)) := by
  induction s with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    -- `U_{k+2}(1) = (2·1)·U_{k+1}(1) − U_k(1)`, substitute the IH, then arithmetic.
    show (((2 : Q') * 1) * Cheb.U (k + 1) 1 + (-(Cheb.U k 1))).eqv (Q'.ofNat (k + 3))
    have hc : (((2 : Q') * 1) * Cheb.U (k + 1) 1 + (-(Cheb.U k 1))).eqv
              (((2 : Q') * 1) * Q'.ofNat (k + 2) + (-(Q'.ofNat (k + 1)))) :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left ((2 : Q') * 1) _ _ ih.2))
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ ih.1))
    exact Q'.eqv_trans _ _ _ hc (step_id k)
where
  /-- The closed-form arithmetic step `(2·1)·(k+2) − (k+1) = k+3` over `Q'`. -/
  step_id (k : Nat) :
      (((2 : Q') * 1) * Q'.ofNat (k + 2) + (-(Q'.ofNat (k + 1)))).eqv (Q'.ofNat (k + 3)) := by
    have eA : (((2 : Q') * 1) * Q'.ofNat (k + 2)).eqv (Q'.ofNat (k + 2) + Q'.ofNat (k + 2)) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv 2))
        (Cheb.two_mul_eqv (Q'.ofNat (k + 2)))
    have eB : (Q'.ofNat (k + 2) + Q'.ofNat (k + 2)).eqv (Q'.ofNat (k + 3) + Q'.ofNat (k + 1)) :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.ofNat_add_eqv (k + 2) (k + 2)))
        (Q'.eqv_trans _ _ _
          (Q'.eqv_of_eq (congrArg Q'.ofNat (by omega : (k + 2) + (k + 2) = (k + 3) + (k + 1))))
          (Q'.ofNat_add_eqv (k + 3) (k + 1)))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _ eA eB)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (Q'.ofNat (k + 3)) (Q'.ofNat (k + 1)) (-(Q'.ofNat (k + 1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (Q'.ofNat (k + 1)) (-(Q'.ofNat (k + 1))))
          (Q'.neg_add_self_eqv (Q'.ofNat (k + 1))))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (Q'.ofNat (k + 3)))

/-- `U_s(1) = s + 1`. -/
theorem U_at_one (s : Nat) : (Cheb.U s 1).eqv (Q'.ofNat (s + 1)) := (U_at_one_pair s).1

/-- `0 ≤ ofNat (s+1)` (the numerator `s+1` is nonnegative). -/
theorem ofNat_succ_nonneg (s : Nat) : (0 : Q') ≤ Q'.ofNat (s + 1) := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ ((s + 1 : Nat) : Int)
  omega

/-- **The `δ_e` moment positivity** `U_s(1) = s + 1 ≥ 0` (the positive-type
condition, discharged). -/
theorem U_at_one_nonneg (s : Nat) : (0 : Q') ≤ Cheb.U s 1 :=
  Q'.le_trans' 0 (Q'.ofNat (s + 1)) (Cheb.U s 1)
    (ofNat_succ_nonneg s)
    (Q'.le_of_eqv (Q'.eqv_symm (U_at_one s)))

/-- `hpos` for `δ_e`: the one-node moment `Σ_{k<1} 1·U_s(1) = U_s(1) ≥ 0`. -/
theorem deltaE_hpos (s : Nat) :
    (0 : Q') ≤ finSum (fun _ => (1 : Q') * Cheb.U s 1) 1 := by
  show (0 : Q') ≤ (0 : Q') + (1 : Q') * Cheb.U s 1
  rw [Q'.zero_add']
  have h1 : (0 : Q') ≤ (1 : Q') := by decide
  exact Q'.mul_nonneg (1 : Q') (Cheb.U s 1) h1 (U_at_one_nonneg s)

/-- **The `t = 0` heat-kernel moment data** `m_s = U_s(1) = s + 1` (the `δ_e`
character moments), a genuine positive-type `QMomentData`. -/
def deltaEMoments : QMomentData :=
  atomicMoments 1 (fun _ => 1) (fun _ => 1) deltaE_hpos

/-- **A fully-closed `NodeQuadrature` inhabitant** for the `δ_e` heat kernel:
one node `x = 1`, weight `1`.  No residual remains — `hpos` is the proved
`deltaE_hpos`. -/
def deltaENodeQuadrature : NodeQuadrature deltaEMoments :=
  atomicNodeQuadrature 1 (fun _ => 1) (fun _ => 1)
    (fun _ => by show (0 : Q') ≤ (1 : Q'); decide) deltaE_hpos

/-- **The `δ_e` heat-kernel Gram is a literal `GramRep`** — instantiating the
conditional `qGram_gramRep` on real positive-type data. -/
def deltaE_gramRep : GramRep (qGram deltaEMoments) :=
  qGram_gramRep deltaEMoments deltaENodeQuadrature

/-- **Off-diagonal OS2 of the `δ_e` heat-kernel Gram, INSTANTIATED.**  The full
off-diagonal character-product quadratic form `Σ_{ij} c_i c_j G_{ij}` is `≥ 0`
at every order `N` and every real coefficient vector `c` — `qGram_quadForm_nonneg`
discharged via the inhabited node quadrature, sourced from the positive measure
`δ_e`, not from fusion-channel positivity. -/
theorem deltaE_offdiag_OS2 (c : Nat → Q') (N : Nat) :
    (0 : Q') ≤ gramQuadForm (qGram deltaEMoments) c N :=
  qGram_quadForm_nonneg deltaEMoments deltaENodeQuadrature c N

end YMGap.Continuum.HeatKernelNodeQuad

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HeatKernelNodeQuad.U_fusion_gram
#print axioms YMGap.Continuum.HeatKernelNodeQuad.atomicNodeQuadrature
#print axioms YMGap.Continuum.HeatKernelNodeQuad.U_at_one
#print axioms YMGap.Continuum.HeatKernelNodeQuad.U_at_one_nonneg
#print axioms YMGap.Continuum.HeatKernelNodeQuad.deltaENodeQuadrature
#print axioms YMGap.Continuum.HeatKernelNodeQuad.deltaE_gramRep
#print axioms YMGap.Continuum.HeatKernelNodeQuad.deltaE_offdiag_OS2
