/-
# The all-mode constructive SU(2) vacuum Haar functional

Finite rational quadratures can reproduce only finitely many SU(2) character
moments.  This module takes the representation-theoretic route instead.  A
`CharacterPacket N` stores the coefficients of every character
`U_0, ..., U_N` as genuine finite `Type`-level data.  Its polynomial synthesis
is an actual `QPoly.Poly`, and `eval_synthesis` identifies it with the finite
Chebyshev-U sum at every rational class point.

The Haar functional is the vacuum coefficient.  Pointwise multiplication is
the already-derived Clebsch--Gordan convolution `fusionProduct`; its vacuum
channel was proved in `FusionQuotientCollapse.fusionProduct_zero_diag` to be
the diagonal sum.  Consequently, for every cutoff and every coefficient
packet,

    H(P* P) = sum_{a <= N} c_a^2 >= 0.

Thus normalization, linearity, the exact all-mode character rule, and
positivity hold uniformly in the cutoff.  No node rule or measured constant
enters.

Honest scope: this constructs the Haar state on explicitly coefficient-bearing
finite character packets and connects those packets to `QPoly`.  Descending it
to a functional on a bare `QPoly.Poly` still requires the constructive
uniqueness (or a canonical extraction algorithm) for Chebyshev-U expansions.
It also does not identify this free Haar state with an interacting Wilson
state or its time evolution.

# Axiom gate

All declarations below are MLTT/HoTT-clean up to the repository-permitted
`propext` / `Quot.sound`.  There is no `Classical.*`, `Real`, `native_decide`,
`sorry`, or custom axiom.
-/

import YMGap.Continuum.SU2ClassPolynomialAlgebra
import YMGap.Continuum.FusionQuotientCollapse
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.SU2CharacterVacuumHaar

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse

/-! ## Finite coefficient packets and their polynomial synthesis -/

/-- Coefficients of all SU(2) characters through the arbitrary cutoff `N`.
The finite vector is data in `Type`, not an erased existence claim. -/
structure CharacterPacket (N : Nat) : Type where
  coeff : Fin (N + 1) -> Q'

/-- Extend a finite packet by zero to a sequence on all natural modes. -/
def coeffAt {N : Nat} (P : CharacterPacket N) (s : Nat) : Q' :=
  if h : s < N + 1 then P.coeff ⟨s, h⟩ else 0

theorem coeffAt_of_lt {N : Nat} (P : CharacterPacket N) {s : Nat}
    (hs : s < N + 1) : coeffAt P s = P.coeff ⟨s, hs⟩ := by
  unfold coeffAt
  rw [dif_pos hs]

theorem coeffAt_of_le {N : Nat} (P : CharacterPacket N) {s : Nat}
    (hs : s <= N) : coeffAt P s = P.coeff ⟨s, Nat.lt_succ_of_le hs⟩ := by
  exact coeffAt_of_lt P (Nat.lt_succ_of_le hs)

theorem coeffAt_of_gt {N : Nat} (P : CharacterPacket N) {s : Nat}
    (hs : N < s) : coeffAt P s = 0 := by
  unfold coeffAt
  rw [dif_neg (by omega)]

/-- The actual rational class polynomial represented by a character packet. -/
def synthesis {N : Nat} (P : CharacterPacket N) : Poly :=
  polyFinSum (fun s => pscale (coeffAt P s) (chebPoly s)) (N + 1)

/-- Polynomial synthesis evaluates to the advertised finite Chebyshev-U
series at every rational class point. -/
theorem eval_synthesis {N : Nat} (P : CharacterPacket N) (x : Q') :
    (eval (synthesis P) x).eqv
      (finSum (fun s => coeffAt P s * Cheb.U s x) (N + 1)) := by
  refine Q'.eqv_trans _ _ _ (eval_polyFinSum _ x (N + 1)) ?_
  exact finSum_congr_eqv
    (fun s => Q'.eqv_trans _ _ _
      (eval_pscale (coeffAt P s) (chebPoly s) x)
      (Q'.mul_eqv_congr_left (coeffAt P s) _ _ (eval_chebPoly s x))) (N + 1)

/-! ## Linear packet operations and the vacuum functional -/

def packetAdd {N : Nat} (P Q : CharacterPacket N) : CharacterPacket N where
  coeff i := P.coeff i + Q.coeff i

def packetScale {N : Nat} (a : Q') (P : CharacterPacket N) : CharacterPacket N where
  coeff i := a * P.coeff i

/-- The normalized SU(2) Haar functional: extract the trivial-character
coefficient. -/
def vacuumHaar {N : Nat} (P : CharacterPacket N) : Q' :=
  P.coeff ⟨0, Nat.succ_pos N⟩

theorem vacuumHaar_add {N : Nat} (P Q : CharacterPacket N) :
    (vacuumHaar (packetAdd P Q)).eqv (vacuumHaar P + vacuumHaar Q) :=
  Q'.eqv_refl _

theorem vacuumHaar_scale {N : Nat} (a : Q') (P : CharacterPacket N) :
    (vacuumHaar (packetScale a P)).eqv (a * vacuumHaar P) :=
  Q'.eqv_refl _

/-- The vacuum packet at every cutoff. -/
def vacuumPacket (N : Nat) : CharacterPacket N where
  coeff i := if i.val = 0 then 1 else 0

theorem vacuumHaar_normalized (N : Nat) :
    (vacuumHaar (vacuumPacket N)).eqv 1 := by
  exact Q'.eqv_refl 1

/-- The pure `n`-th character inside any cutoff that contains it. -/
def basisPacket {N : Nat} (n : Fin (N + 1)) : CharacterPacket N where
  coeff i := if i.val = n.val then 1 else 0

theorem vacuumHaar_basis {N : Nat} (n : Fin (N + 1)) :
    (vacuumHaar (basisPacket n)).eqv (if n.val = 0 then 1 else 0) := by
  change (if 0 = n.val then (1 : Q') else 0).eqv
    (if n.val = 0 then 1 else 0)
  by_cases h : n.val = 0
  · rw [if_pos h, if_pos h.symm]
    exact Q'.eqv_refl 1
  · rw [if_neg h, if_neg (fun h0 => h h0.symm)]
    exact Q'.eqv_refl 0

/-- Every nontrivial SU(2) character is annihilated, with no fixed upper-mode
bound: choose its own cutoff. -/
theorem vacuumHaar_all_nontrivial_characters (n : Nat) :
    (vacuumHaar
      (basisPacket (N := n) (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)))).eqv
      (if n = 0 then 1 else 0) :=
  vacuumHaar_basis ⟨n, Nat.lt_succ_self n⟩

/-! ## The genuine fusion product and positivity -/

/-- The Clebsch--Gordan product coefficient sequence of two packets. -/
def fusionCoeff {N : Nat} (P Q : CharacterPacket N) (s : Nat) : Q' :=
  fusionProduct N (coeffAt P) (coeffAt Q) s

/-- Haar applied to the genuine pointwise character product. -/
def fusionHaar {N : Nat} (P Q : CharacterPacket N) : Q' :=
  fusionCoeff P Q 0

/-- Package the genuine fusion product.  Modes `0, ..., 2N` contain the full
Clebsch--Gordan product of two packets supported through `N`. -/
def fusionPacket {N : Nat} (P Q : CharacterPacket N) : CharacterPacket (2 * N) where
  coeff s := fusionCoeff P Q s.val

/-- `fusionHaar` really is `vacuumHaar` applied to the packaged product. -/
theorem vacuumHaar_fusionPacket {N : Nat} (P Q : CharacterPacket N) :
    (vacuumHaar (fusionPacket P Q)).eqv (fusionHaar P Q) :=
  Q'.eqv_refl _

/-- The exact all-order Peter--Weyl/Haar pairing: the vacuum coefficient of
the genuine SU(2) fusion product is the diagonal dot product. -/
theorem fusionHaar_eq_diagonal {N : Nat} (P Q : CharacterPacket N) :
    (fusionHaar P Q).eqv
      (fsum (fun a => coeffAt P a * coeffAt Q a) (N + 1)) :=
  fusionProduct_zero_diag N (coeffAt P) (coeffAt Q)

/-- Positivity on every finite character combination, uniformly in the
cutoff: `H(P*P) = sum c_a^2 >= 0`. -/
theorem fusionHaar_square_nonneg {N : Nat} (P : CharacterPacket N) :
    (0 : Q') <= fusionHaar P P := by
  have hsum : (0 : Q') <=
      fsum (fun a => coeffAt P a * coeffAt P a) (N + 1) :=
    fsum_nonneg (fun a => SumOfSquares.q_mul_self_nonneg (coeffAt P a)) (N + 1)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv (Q'.eqv_symm (fusionHaar_eq_diagonal P P)))

/-- Positivity stated directly for the normalized functional on the packaged
pointwise square. -/
theorem vacuumHaar_fusionSquare_nonneg {N : Nat} (P : CharacterPacket N) :
    (0 : Q') <= vacuumHaar (fusionPacket P P) := by
  exact Q'.le_trans' _ _ _ (fusionHaar_square_nonneg P)
    (Q'.le_of_eqv (Q'.eqv_symm (vacuumHaar_fusionPacket P P)))

/-! ## Exact identity Gram matrix for every cutoff -/

theorem coeffAt_basis {N : Nat} (i : Fin (N + 1)) (s : Nat) :
    coeffAt (basisPacket i) s = if s = i.val then 1 else 0 := by
  by_cases hs : s < N + 1
  · simp [coeffAt, basisPacket, hs]
  · have hne : s ≠ i.val := by
      intro h
      subst s
      exact hs i.isLt
    simp [coeffAt, hs, hne]

/-- A pure coefficient packet synthesizes to the corresponding genuine
Chebyshev-U class polynomial.  This is the direct bridge from the all-mode
coefficient carrier to `QPoly`. -/
theorem synthesis_basis {N : Nat} (i : Fin (N + 1)) :
    PolyEqv (synthesis (basisPacket i)) (chebPoly i.val) := by
  intro x
  refine Q'.eqv_trans _ _ _ (eval_synthesis (basisPacket i) x) ?_
  rw [← YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
  have hzero : ∀ s, s ≠ i.val →
      (coeffAt (basisPacket i) s * Cheb.U s x).eqv 0 := by
    intro s hsi
    rw [coeffAt_basis i s, if_neg hsi]
    exact Q'.zero_mul_eqv _
  refine Q'.eqv_trans _ _ _
    (fsum_collapse hzero (N + 1) i.isLt) ?_
  rw [coeffAt_basis i i.val, if_pos rfl]
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv (Cheb.U i.val x)) ?_
  exact Q'.eqv_symm (eval_chebPoly i.val x)

/-- The all-mode character Gram matrix is exactly the identity at every
finite cutoff. -/
theorem fusionHaar_basis_delta {N : Nat} (i j : Fin (N + 1)) :
    (fusionHaar (basisPacket i) (basisPacket j)).eqv
      (if i.val = j.val then 1 else 0) := by
  refine Q'.eqv_trans _ _ _ (fusionHaar_eq_diagonal (basisPacket i) (basisPacket j)) ?_
  by_cases hij : i.val = j.val
  · rw [if_pos hij]
    have hzero : forall a, a ≠ i.val ->
        ((coeffAt (basisPacket i) a) * (coeffAt (basisPacket j) a)).eqv 0 := by
      intro a hai
      rw [coeffAt_basis i a, if_neg hai]
      exact Q'.zero_mul_eqv _
    refine Q'.eqv_trans _ _ _
      (fsum_collapse hzero (N + 1) i.isLt) ?_
    rw [coeffAt_basis i i.val, coeffAt_basis j i.val, if_pos rfl,
      if_pos hij]
    exact Q'.one_mul_eqv 1
  · rw [if_neg hij]
    apply fsum_zero_below
    intro a ha
    rw [coeffAt_basis i a, coeffAt_basis j a]
    by_cases hai : a = i.val
    · rw [if_pos hai]
      have haj : a ≠ j.val := by
        intro h
        exact hij (hai.symm.trans h)
      rw [if_neg haj]
      exact Q'.mul_zero_eqv 1
    · rw [if_neg hai]
      exact Q'.zero_mul_eqv _

/-- In particular, every pair of arbitrary mode labels has the exact Haar
Kronecker pairing by choosing a cutoff containing both. -/
theorem all_mode_character_orthogonality (i j : Nat) :
    let N := max i j
    let ii : Fin (N + 1) := ⟨i, by omega⟩
    let jj : Fin (N + 1) := ⟨j, by omega⟩
    (fusionHaar (basisPacket ii) (basisPacket jj)).eqv
      (if i = j then 1 else 0) := by
  dsimp
  exact fusionHaar_basis_delta _ _

end YMGap.Continuum.SU2CharacterVacuumHaar

#print axioms YMGap.Continuum.SU2CharacterVacuumHaar.eval_synthesis
#print axioms YMGap.Continuum.SU2CharacterVacuumHaar.vacuumHaar_add
#print axioms YMGap.Continuum.SU2CharacterVacuumHaar.vacuumHaar_scale
#print axioms YMGap.Continuum.SU2CharacterVacuumHaar.vacuumHaar_normalized
#print axioms YMGap.Continuum.SU2CharacterVacuumHaar.vacuumHaar_all_nontrivial_characters
#print axioms YMGap.Continuum.SU2CharacterVacuumHaar.synthesis_basis
#print axioms YMGap.Continuum.SU2CharacterVacuumHaar.vacuumHaar_fusionPacket
#print axioms YMGap.Continuum.SU2CharacterVacuumHaar.fusionHaar_eq_diagonal
#print axioms YMGap.Continuum.SU2CharacterVacuumHaar.fusionHaar_square_nonneg
#print axioms YMGap.Continuum.SU2CharacterVacuumHaar.vacuumHaar_fusionSquare_nonneg
#print axioms YMGap.Continuum.SU2CharacterVacuumHaar.fusionHaar_basis_delta
#print axioms YMGap.Continuum.SU2CharacterVacuumHaar.all_mode_character_orthogonality
