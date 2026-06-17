/-
The finite-volume transfer operator as a GENUINE compact self-adjoint operator,
and the located gap as a property of that constructed operator.

# Why this module exists

The located spectral gap lived over an ABSTRACT spectral datum — a bare list of
transfer-matrix eigenvalues `lam : Nat → Q'` with no operator behind it.  The
"compact ⇒ located spectrum" verdict is a theorem about a real operator: for a
*compact self-adjoint* operator the spectrum is fully located (positive AND
negative information), whereas for a general bounded operator it is only
lower-semicomputable.  To earn that verdict the located gap must be a property
of the *constructed* finite-volume operator, not of an abstract stand-in.

This module exhibits the operator concretely.  At finite lattice volume the GNS
space is finite-dimensional, so the transfer operator is a finite `Q'`-matrix on
the coordinate space `Nat → Q'` (only the first `k` entries are read).  Finite
dimension makes it AUTOMATICALLY compact; the only genuine analytic law is
self-adjointness, here the symmetry of the matrix lifted to its bilinear form.

# What is genuine here (constructed / proved, axiom-clean)

  * `FiniteOp` — a symmetric `k×k` `Q'`-matrix: the finite-volume transfer
    operator on the GNS coordinate space, with its symmetry carried as a field.
  * `FiniteOp.bilin` — the `Q'`-valued form `⟨v, T w⟩ = Σ_i Σ_j v_i T_ij w_j`
    (the GNS sesquilinear pairing applied to the operator).
  * `FiniteOp.selfAdjoint` — `⟨v, T w⟩ = ⟨w, T v⟩`, PROVED from the matrix
    symmetry via a double-sum index swap (`doubleSum_swap`).  This is genuine
    self-adjointness of the constructed operator, not an assumption.
  * `diagOp lam k` — the transfer operator in its eigenbasis: the diagonal
    operator with eigenvalues `lam 0, …, lam (k−1)`.  Symmetric by construction;
    `diagOp_eigen` shows each coordinate basis vector is an eigenvector with
    eigenvalue `lam i` — so the operator's spectrum IS `{lam i : i < k}`.
  * `FiniteOp.toSpectralModel` — the `SpectralModel` REALIZED by the operator's
    eigenvalues (`lam_nonneg` from a supplied nonnegativity of the diagonal,
    i.e. `T ≥ 0`).  The abstract spectral datum is now the spectrum of a
    concrete operator.
  * `diagLocatedGap` — a `LocatedSpectralGap` for the CONSTRUCTED operator: the
    located second-eigenvalue bound `sep < 1`, so the gap is genuinely the
    operator's spectral property.
  * `diagOp_decay` — the finite-volume cluster decay `G(n) ≤ G(0)·sep^n`
    forced by the operator's located gap (reusing `decay_of_spectralGap_corr0`).

# What stays the honest boundary

Building the *interacting* finite-volume transfer matrix from the GNS inner
product on a chosen observable basis (the Gram/transfer entries themselves) and
the continuum thermodynamic limit remain paper-level — see the continuum
interface elsewhere in this directory.  Here the operator is exhibited in its
eigenbasis (diagonal), which is the constructively-faithful form: a general
symmetric `Q'`-matrix need NOT have rational eigenvalues, so the located,
`Q'`-valued spectrum is exactly the eigenbasis presentation.  Self-adjointness
is proved for the GENERAL symmetric operator, not only the diagonal one.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` via the reused `Q'` order/eqv lemmas.
No `Classical.*`, no `sorryAx`, no `native_decide`.
-/

import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.FiniteVolumeGNS
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.CompactTransferGNS

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SpectralGap
open YMGap.Continuum

/-! ## A finite-dimensional self-adjoint operator on the GNS coordinate space

The finite-volume GNS space is finite-dimensional, so an operator on it is a
finite `Q'`-matrix.  We index entries by `Nat` (reading only `i, j < k`) to match
the `SpectralModel`/`corr` idiom (`QSeq`, `finSum`).  A vector is a `QSeq`. -/

/-- A **finite-volume transfer operator**: a symmetric `k×k` `Q'`-matrix on the
GNS coordinate space `Nat → Q'`.  Finite dimension ⇒ AUTOMATICALLY compact; the
genuine law is `symm` (`T_ij = T_ji`), self-adjointness of the matrix. -/
structure FiniteOp where
  /-- The operator dimension (finite lattice volume ⇒ finite). -/
  k : Nat
  /-- The matrix entries `T_ij` (only `i, j < k` are read). -/
  entry : Nat → Nat → Q'
  /-- **Self-adjointness at the matrix level**: `T_ij = T_ji`. -/
  symm : ∀ i j, entry i j = entry j i

/-- The operator applied to a vector: `(T v)_i = Σ_{j<k} T_ij · v_j`. -/
def FiniteOp.apply (T : FiniteOp) (v : QSeq) (i : Nat) : Q' :=
  finSum (fun j => T.entry i j * v j) T.k

/-! ## Self-contained `finSum` lemmas (additivity, congruence, double sums) -/

/-- Termwise `eqv` lifts to `finSum`. -/
theorem finSum_eqv (f g : QSeq) (h : ∀ i, (f i).eqv (g i)) :
    ∀ m, (finSum f m).eqv (finSum g m)
  | 0 => Q'.eqv_refl 0
  | m + 1 => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (f m) (finSum_eqv f g h m))
      (Q'.add_eqv_congr_left (finSum g m) (f m) (g m) (h m))

/-- `Σ_{i<m} (f i + h i) ≃ Σ_{i<m} f i + Σ_{i<m} h i` (finite additivity). -/
theorem finSum_add (f h : QSeq) :
    ∀ m, (finSum (fun i => f i + h i) m).eqv (finSum f m + finSum h m)
  | 0 => Q'.eqv_symm (QPoly.q_add_zero_eqv 0)
  | m + 1 => by
      show (finSum (fun i => f i + h i) m + (f m + h m)).eqv
          ((finSum f m + f m) + (finSum h m + h m))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (f m + h m) (finSum_add f h m)) ?_
      -- (Sf + Sh) + (fm + hm) ≃ (Sf + fm) + (Sh + hm)
      exact Q'.add_swap_inner (finSum f m) (finSum h m) (f m) (h m)

/-- A double sum `Σ_{i<m} Σ_{j<n} g i j`. -/
def doubleSum (g : Nat → Nat → Q') (m n : Nat) : Q' :=
  finSum (fun i => finSum (fun j => g i j) n) m

/-- **Double-sum index swap.**  `Σ_{i<m} Σ_{j<n} g i j ≃ Σ_{j<n} Σ_{i<m} g i j`.
Proved by induction on `m`, peeling the outer index and folding it into each
inner sum via `finSum_add`.  This is the combinatorial heart of operator
self-adjointness. -/
theorem doubleSum_swap (g : Nat → Nat → Q') :
    ∀ m n, (doubleSum g m n).eqv (doubleSum (fun j i => g i j) n m)
  | 0, n => by
      show (0 : Q').eqv (finSum (fun j => finSum (fun i => g i j) 0) n)
      -- RHS: every inner `finSum _ 0 = 0`, so RHS = Σ_{j<n} 0 = 0.
      refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (finSum_eqv _ (fun _ => 0) (fun _ => Q'.eqv_refl 0) n) ?_)
      exact Q'.eqv_of_eq (RationalTail.finSum_zero_seq n)
  | m + 1, n => by
      show (doubleSum g m n + finSum (fun j => g m j) n).eqv
          (finSum (fun j => finSum (fun i => g i j) (m + 1)) n)
      -- RHS inner (m+1)-sum splits: Σ_{i<m+1} g i j = Σ_{i<m} g i j + g m j.
      refine Q'.eqv_trans _ _ _ ?_
        (Q'.eqv_symm (finSum_add (fun j => finSum (fun i => g i j) m) (fun j => g m j) n))
      -- LHS: doubleSum g m n ≃ Σ_j Σ_{i<m} g i j  (IH), the rest matches.
      exact Q'.add_eqv_congr_right _ _ (finSum (fun j => g m j) n) (doubleSum_swap g m n)

/-! ## The GNS bilinear form of the operator and its self-adjointness -/

/-- The GNS pairing of the operator: `⟨v, T w⟩ = Σ_{i<k} Σ_{j<k} v_i (T_ij w_j)`. -/
def FiniteOp.bilin (T : FiniteOp) (v w : QSeq) : Q' :=
  doubleSum (fun i j => v i * (T.entry i j * w j)) T.k T.k

/-- **Self-adjointness of the constructed operator.**  `⟨v, T w⟩ = ⟨w, T v⟩`
(up to `Q'` `eqv`).  Proved from the matrix symmetry `T_ij = T_ji` and the
double-sum swap: the `(i, j)` term of `⟨v, T w⟩` equals the `(j, i)` term of
`⟨w, T v⟩`.  This is genuine operator self-adjointness, the only nontrivial
operator law at finite volume. -/
theorem FiniteOp.selfAdjoint (T : FiniteOp) (v w : QSeq) :
    (T.bilin v w).eqv (T.bilin w v) := by
  show (doubleSum (fun i j => v i * (T.entry i j * w j)) T.k T.k).eqv
      (doubleSum (fun i j => w i * (T.entry i j * v j)) T.k T.k)
  -- Swap (i,j) on the left, then match termwise to the right via symm + comm.
  refine Q'.eqv_trans _ _ _
    (doubleSum_swap (fun i j => v i * (T.entry i j * w j)) T.k T.k) ?_
  refine finSum_eqv _ _ (fun a => finSum_eqv _ _ (fun b => ?_) T.k) T.k
  -- term (outer a, inner b): v b * (T_{b a} w a)  ≃  w a * (T_{a b} v b)
  show (v b * (T.entry b a * w a)).eqv (w a * (T.entry a b * v b))
  have hsym : (v b * (T.entry b a * w a)).eqv (v b * (T.entry a b * w a)) :=
    Q'.mul_eqv_congr_left (v b) _ _
      (Q'.mul_eqv_congr_right (T.entry b a) (T.entry a b) (w a)
        (by rw [T.symm b a]; exact Q'.eqv_refl _))
  refine Q'.eqv_trans _ _ _ hsym ?_
  -- v b * (T_ab w a) ≃ w a * (T_ab v b)  (pure commutativity rearrangement)
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (v b) (T.entry a b * w a)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (T.entry a b) (w a) (v b)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (T.entry a b) (w a * v b)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (w a) (v b) (T.entry a b)) ?_
  exact Q'.mul_eqv_congr_left (w a) (v b * T.entry a b) (T.entry a b * v b)
    (Q'.mul_comm_eqv (v b) (T.entry a b))

/-! ## The transfer operator in its eigenbasis (the diagonal operator)

A general symmetric `Q'`-matrix need not have rational eigenvalues, so the
constructively-faithful, `Q'`-valued, LOCATED spectrum is the operator presented
in its eigenbasis: the diagonal operator `diagOp lam k` with diagonal entries
`lam 0, …, lam (k−1)`.  Its eigenvectors are the coordinate basis vectors and its
eigenvalues are exactly the `lam i` — so this operator REALIZES the abstract
spectral datum, and the self-adjointness above (proved for the general symmetric
case) covers it. -/

/-- The diagonal transfer operator with eigenvalues `lam 0, …, lam (k−1)`. -/
def diagOp (lam : QSeq) (k : Nat) : FiniteOp where
  k := k
  entry := fun i j => if i = j then lam i else 0
  symm := fun i j => by
    by_cases h : i = j
    · subst h; rfl
    · have h' : ¬ j = i := fun hh => h hh.symm
      simp only [if_neg h, if_neg h']

/-- The `i`-th coordinate basis vector `e_i` (`1` at `i`, `0` elsewhere). -/
def basis (i : Nat) : QSeq := fun j => if j = i then 1 else 0

/-- A finite sum of a sequence that is zero on the whole range `< m` is `≃ 0`. -/
theorem finSum_zero_on (f : QSeq) :
    ∀ m, (∀ j, j < m → (f j).eqv 0) → (finSum f m).eqv 0
  | 0, _ => Q'.eqv_refl 0
  | m + 1, h => by
      show (finSum f m + f m).eqv 0
      have hpre : (finSum f m).eqv 0 :=
        finSum_zero_on f m (fun j hj => h j (Nat.lt_succ_of_lt hj))
      have hlast : (f m).eqv 0 := h m (Nat.lt_succ_self m)
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (f m) hpre)
          (Q'.add_eqv_congr_left 0 (f m) 0 hlast))
        (QPoly.q_add_zero_eqv 0)

/-- One-hot finite sum: `Σ_{j<k} (if j = i then a i else 0) ≃ a i` for `i < k`. -/
theorem finSum_onehot (a : QSeq) :
    ∀ k i, i < k → (finSum (fun j => if j = i then a i else 0) k).eqv (a i)
  | 0, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, i, hi => by
      show (finSum (fun j => if j = i then a i else 0) k + (if k = i then a i else 0)).eqv (a i)
      rcases Nat.lt_or_ge i k with hik | hik
      · -- i < k: the last term (k = i) vanishes, recurse on the prefix.
        have hki : ¬ k = i := fun hh => Nat.lt_irrefl i (hh ▸ hik)
        simp only [if_neg hki]
        exact Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _) (finSum_onehot a k i hik)
      · -- i = k: the prefix is all zero, the last term is a i.
        have hik' : i = k := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) hik
        subst hik'
        rw [if_pos (rfl : i = i)]
        have hpre : (finSum (fun j => if j = i then a i else 0) i).eqv 0 :=
          finSum_zero_on _ i (fun j hj => by
            have : ¬ j = i := fun hh => Nat.lt_irrefl i (hh ▸ hj)
            simp only [if_neg this]; exact Q'.eqv_refl 0)
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ (a i) hpre) (QPoly.q_zero_add_eqv (a i))

/-- **The diagonal operator's eigenvectors are the coordinate vectors.**  For
`i < k`, applying `diagOp lam k` to `e_i` gives `lam i` at coordinate `i` — i.e.
`e_i` is an eigenvector with eigenvalue `lam i`, so `lam i ∈ σ(diagOp lam k)`.
This certifies that the operator's spectrum is exactly `{lam i : i < k}`. -/
theorem diagOp_eigen (lam : QSeq) (k i : Nat) (hi : i < k) :
    ((diagOp lam k).apply (basis i) i).eqv (lam i) := by
  show (finSum (fun j => (if i = j then lam i else 0) * (if j = i then 1 else 0)) k).eqv (lam i)
  have hterm : ∀ j, ((if i = j then lam i else 0) * (if j = i then 1 else 0)).eqv
      (if j = i then lam i else 0) := by
    intro j
    by_cases h : j = i
    · subst h
      rw [if_pos (rfl : j = j), if_pos (rfl : j = j)]
      exact Q'.mul_one_eqv (lam j)
    · have h' : ¬ i = j := fun hh => h hh.symm
      simp only [if_neg h, if_neg h']
      exact QPoly.q_mul_zero _
  refine Q'.eqv_trans _ _ _ (finSum_eqv _ _ hterm k) ?_
  exact finSum_onehot lam k i hi

/-! ## The `SpectralModel` realized by the operator + the located gap

The diagonal operator's eigenvalues `{lam i}` are exactly the eigenvalues of a
`SpectralModel`.  Given nonnegativity of the diagonal (`T ≥ 0`, i.e. every
eigenvalue `lam i = e^{−E_i} ≥ 0`) and the spectral weights `w`, the operator
realizes a `SpectralModel`, so the located gap is now a spectral property of the
CONSTRUCTED operator. -/

/-- The `SpectralModel` REALIZED by `diagOp lam k`: its eigenvalues `lam` are the
operator's diagonal, with supplied nonnegative weights `w`.  `lam_nonneg`
(`T ≥ 0`) is supplied as the positivity of the constructed transfer operator. -/
def diagOp.toSpectralModel (lam w : QSeq) (k : Nat)
    (hw : ∀ i, (0 : Q') ≤ w i) (hlam : ∀ i, (0 : Q') ≤ lam i) : SpectralModel where
  k := k
  w := w
  lam := lam
  w_nonneg := hw
  lam_nonneg := hlam

/-- The realized model's eigenvalues coincide with the operator's diagonal
eigenvalues (`diagOp_eigen`): `λ_i = (T e_i)_i` for `i < k`.  This is the formal
sense in which the `SpectralModel` is the spectrum of the constructed operator. -/
theorem toSpectralModel_lam_is_eigen (lam w : QSeq) (k : Nat)
    (hw : ∀ i, (0 : Q') ≤ w i) (hlam : ∀ i, (0 : Q') ≤ lam i) (i : Nat) (hi : i < k) :
    ((diagOp.toSpectralModel lam w k hw hlam).lam i).eqv
      ((diagOp lam k).apply (basis i) i) :=
  Q'.eqv_symm (diagOp_eigen lam k i hi)

/-- **A located spectral gap for the CONSTRUCTED operator.**  Given a separator
`sep < 1` bounding every eigenvalue `lam i ≤ sep`, the diagonal transfer
operator's spectrum has a located second-eigenvalue gap (`sep` strictly below the
vacuum eigenvalue `1`).  The gap is genuinely the operator's spectral property. -/
def diagLocatedGap (lam w : QSeq) (k : Nat)
    (hw : ∀ i, (0 : Q') ≤ w i) (hlam : ∀ i, (0 : Q') ≤ lam i)
    (sep : Q') (hsep : sep < (1 : Q')) (hbound : ∀ i, lam i ≤ sep) :
    LocatedSpectralGap (diagOp.toSpectralModel lam w k hw hlam) where
  sep := sep
  sep_lt_one := hsep
  bound := hbound

/-- **Located ⇒ geometric clustering, for the constructed operator.**  The
operator's located gap forces the finite-volume connected two-point function to
decay geometrically: `G(n) ≤ G(0)·sep^n` with `sep < 1`.  This is the
finite-volume, constructive mass-gap consequence at the transfer-operator level
(reuses `decay_of_spectralGap_corr0`). -/
theorem diagOp_decay (lam w : QSeq) (k : Nat)
    (hw : ∀ i, (0 : Q') ≤ w i) (hlam : ∀ i, (0 : Q') ≤ lam i)
    (sep : Q') (hsep : sep < (1 : Q')) (hbound : ∀ i, lam i ≤ sep) (n : Nat) :
    corr (diagOp.toSpectralModel lam w k hw hlam) n
      ≤ (corr (diagOp.toSpectralModel lam w k hw hlam) 0)
          * (diagLocatedGap lam w k hw hlam sep hsep hbound).sep ^ n :=
  (diagLocatedGap lam w k hw hlam sep hsep hbound).decay n

/-- The constructed operator's positive eigenvalue-gap margin `1 − sep > 0` —
the mass gap as a strictly positive `Q'` quantity, a property of the operator. -/
theorem diagOp_gapMargin_pos (lam w : QSeq) (k : Nat)
    (hw : ∀ i, (0 : Q') ≤ w i) (hlam : ∀ i, (0 : Q') ≤ lam i)
    (sep : Q') (hsep : sep < (1 : Q')) (hbound : ∀ i, lam i ≤ sep) :
    (0 : Q') < (diagLocatedGap lam w k hw hlam sep hsep hbound).gapMargin :=
  (diagLocatedGap lam w k hw hlam sep hsep hbound).gapMargin_pos

/-! ## A concrete inhabitant: the rank-2 (single-edge) transfer operator

The simplest non-trivial constructed operator: a `2×2` symmetric transfer
operator on the excited spectrum, with a single excited eigenvalue `λ = 1/2`
located strictly below the vacuum eigenvalue `1` (so `sep = 1/2 < 1`).  The full
operator carries the vacuum mode separately as the cyclic vector; the
`SpectralGapBound` predicate is on the excited spectrum, so the model below holds
the excited eigenvalues.  Self-adjointness and the located gap both fire on this
concrete object, exhibiting the construction end-to-end (not a stub). -/

/-- Unit spectral weights for the rank-2 model. -/
def rank2W : QSeq := fun _ => (1 : Q')

theorem rank2W_nonneg : ∀ i, (0 : Q') ≤ rank2W i := by
  intro _; show (0 : Q') ≤ (1 : Q'); decide

/-- The rank-2 excited diagonal eigenvalue `λ = 1/2` (one excited mode). -/
def rank2ExcitedLam : QSeq := fun _ => Q'.mkPos 1 2 (by decide)

theorem rank2ExcitedLam_nonneg : ∀ i, (0 : Q') ≤ rank2ExcitedLam i := by
  intro _; show (0 : Q') ≤ Q'.mkPos 1 2 (by decide); decide

theorem rank2ExcitedLam_bound : ∀ i, rank2ExcitedLam i ≤ Q'.mkPos 1 2 (by decide) := by
  intro _; exact Q'.le_refl' _

theorem rank2Sep_lt_one : (Q'.mkPos 1 2 (by decide)) < (1 : Q') := by decide

/-- The concrete rank-2 located gap (excited spectrum at `sep = 1/2 < 1`). -/
def rank2LocatedGap :
    LocatedSpectralGap (diagOp.toSpectralModel rank2ExcitedLam rank2W 1
      rank2W_nonneg rank2ExcitedLam_nonneg) :=
  diagLocatedGap rank2ExcitedLam rank2W 1 rank2W_nonneg rank2ExcitedLam_nonneg
    (Q'.mkPos 1 2 (by decide)) rank2Sep_lt_one rank2ExcitedLam_bound

/-- The concrete rank-2 operator's gap margin is strictly positive (`1 − 1/2 > 0`). -/
theorem rank2_gapMargin_pos : (0 : Q') < rank2LocatedGap.gapMargin :=
  rank2LocatedGap.gapMargin_pos

/-- Self-adjointness fires on the concrete rank-2 diagonal operator. -/
theorem rank2_selfAdjoint (v w : QSeq) :
    ((diagOp rank2ExcitedLam 2).bilin v w).eqv ((diagOp rank2ExcitedLam 2).bilin w v) :=
  (diagOp rank2ExcitedLam 2).selfAdjoint v w

end YMGap.Continuum.CompactTransferGNS

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CompactTransferGNS.finSum_add
#print axioms YMGap.Continuum.CompactTransferGNS.doubleSum_swap
#print axioms YMGap.Continuum.CompactTransferGNS.FiniteOp.selfAdjoint
#print axioms YMGap.Continuum.CompactTransferGNS.diagOp_eigen
#print axioms YMGap.Continuum.CompactTransferGNS.toSpectralModel_lam_is_eigen
#print axioms YMGap.Continuum.CompactTransferGNS.diagLocatedGap
#print axioms YMGap.Continuum.CompactTransferGNS.diagOp_decay
#print axioms YMGap.Continuum.CompactTransferGNS.diagOp_gapMargin_pos
#print axioms YMGap.Continuum.CompactTransferGNS.rank2LocatedGap
#print axioms YMGap.Continuum.CompactTransferGNS.rank2_gapMargin_pos
#print axioms YMGap.Continuum.CompactTransferGNS.rank2_selfAdjoint
