/-
# Constructive descent from bare class polynomials to character packets

The canonical Chebyshev extractor produces an ordinary finite coefficient
list.  This module turns such a list into the existing all-mode
`CharacterPacket` carrier at any cutoff large enough to contain it.  The
conversion is computational: coefficients outside the list are literally
zero, with no choice or quotient representative.

The main bridge proves that packet synthesis is extensionally equal to
Chebyshev-list synthesis.  Applied to `chebExtract`, every bare `QPoly.Poly`
therefore has a concrete packet representative whose synthesis is the
original polynomial and whose packet vacuum agrees with `bareVacuumHaar`.

Finally, two arbitrary bare polynomials are embedded at one common cutoff and
fed to the already-proved Clebsch--Gordan `fusionPacket`.  Its vacuum is the
exact diagonal pairing, and the square is nonnegative for every bare
polynomial.  The remaining multiplication residual is stated honestly in the
file footer: identifying the full synthesized fusion packet with ordinary
`QPoly.pmul` requires a finite fusion-sum rearrangement theorem not assumed
here.

# Axiom gate

All declarations are MLTT/HoTT-clean up to `propext` / `Quot.sound`.  There is
no classical choice, trusted native computation, proof hole, or custom axiom.
-/

import YMGap.Continuum.SU2ClassPolynomialChebUniqueness
import YMGap.Continuum.SU2CharacterVacuumHaar

namespace YMGap.Continuum.SU2ClassPolynomialPacketDescent

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebExtraction
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2CharacterVacuumHaar

/-! ## A finite list as a zero-extended mode sequence -/

/-- The coefficient at mode `s`, with literal zero extension beyond the end
of the finite list. -/
def listCoeff : List Q' -> Nat -> Q'
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, s + 1 => listCoeff as s

theorem listCoeff_eq_zero_of_length_le : forall (a : List Q') (s : Nat),
    a.length <= s -> listCoeff a s = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: as, s + 1, h => by
      exact listCoeff_eq_zero_of_length_le as s (by simpa using h)

/-- Put a finite list into any requested packet cutoff.  Correct synthesis
requires the explicit support condition `a.length <= N+1`, proved below. -/
def listPacketAt (N : Nat) (a : List Q') : CharacterPacket N where
  coeff i := listCoeff a i.val

theorem coeffAt_listPacketAt {N : Nat} (a : List Q')
    (hlen : a.length <= N + 1) (s : Nat) :
    coeffAt (listPacketAt N a) s = listCoeff a s := by
  unfold coeffAt
  by_cases hs : s < N + 1
  · rw [dif_pos hs]
    rfl
  · rw [dif_neg hs]
    exact (listCoeff_eq_zero_of_length_le a s
      (Nat.le_trans hlen (by omega))).symm

/-! ## Exact finite-sum bridge -/

private theorem finSum_shift (f : Nat -> Q') : forall n : Nat,
    (finSum f (n + 1)).eqv
      (f 0 + finSum (fun i => f (i + 1)) n)
  | 0 => by
      exact Q'.eqv_trans _ (f 0) _ (q_zero_add_eqv (f 0))
        (Q'.eqv_symm (q_add_zero_eqv (f 0)))
  | n + 1 => by
      show (finSum f (n + 1) + f (n + 1)).eqv
        (f 0 + (finSum (fun i => f (i + 1)) n + f (n + 1)))
      exact Q'.eqv_trans _ _ _
        (q_add_congr (finSum_shift f n) (Q'.eqv_refl (f (n + 1))))
        (Q'.add_assoc_eqv (f 0) (finSum (fun i => f (i + 1)) n)
          (f (n + 1)))

private theorem finSum_zero_extension {f : Nat -> Q'} {n m : Nat}
    (hnm : n <= m) (hz : forall i : Nat, n <= i -> (f i).eqv 0) :
    (finSum f m).eqv (finSum f n) := by
  induction hnm with
  | refl => exact Q'.eqv_refl _
  | @step m hnm ih =>
      show (finSum f m + f m).eqv (finSum f n)
      exact Q'.eqv_trans _ (finSum f n + 0) _
        (q_add_congr ih (hz m hnm)) (q_add_zero_eqv (finSum f n))

/-- A Chebyshev list evaluates to the finite mode sum indexed by its
zero-extended coefficient sequence. -/
theorem chebEvalFrom_eq_finSum_listCoeff : forall
    (k : Nat) (a : List Q') (x : Q'),
    (chebEvalFrom k a x).eqv
      (finSum (fun s => listCoeff a s * Cheb.U (s + k) x) a.length)
  | _, [], _ => Q'.eqv_refl 0
  | k, c :: cs, x => by
      have htail :
          (finSum (fun i => listCoeff cs i * Cheb.U ((i + 1) + k) x)
            cs.length).eqv
          (finSum (fun i => listCoeff cs i * Cheb.U (i + (k + 1)) x)
            cs.length) :=
        finSum_congr_eqv (fun i => by
          have hi : (i + 1) + k = i + (k + 1) := by omega
          rw [hi]
          exact Q'.eqv_refl _) cs.length
      have hsplit := finSum_shift
        (fun s => listCoeff (c :: cs) s * Cheb.U (s + k) x) cs.length
      have hsplit' :
          (finSum (fun s => listCoeff (c :: cs) s * Cheb.U (s + k) x)
            (c :: cs).length).eqv
          (c * Cheb.U k x +
            finSum (fun i => listCoeff cs i * Cheb.U (i + (k + 1)) x)
              cs.length) := by
        refine Q'.eqv_trans _ _ _ (by simpa [listCoeff] using hsplit) ?_
        exact q_add_congr (Q'.eqv_refl _) htail
      refine Q'.eqv_trans _
        (c * Cheb.U k x +
          finSum (fun i => listCoeff cs i * Cheb.U (i + (k + 1)) x)
            cs.length) _ ?_ (Q'.eqv_symm hsplit')
      exact q_add_congr (Q'.eqv_refl _)
        (chebEvalFrom_eq_finSum_listCoeff (k + 1) cs x)

theorem chebEval_eq_finSum_listCoeff (a : List Q') (x : Q') :
    (chebEval a x).eqv
      (finSum (fun s => listCoeff a s * Cheb.U s x) a.length) := by
  have h := chebEvalFrom_eq_finSum_listCoeff 0 a x
  simpa [chebEval] using h

/-! ## Synthesis and vacuum agreement -/

/-- Packet synthesis agrees with list synthesis at every cutoff containing
the whole finite coefficient list. -/
theorem synthesis_listPacketAt {N : Nat} (a : List Q')
    (hlen : a.length <= N + 1) :
    PolyEqv (synthesis (listPacketAt N a)) (chebSynthesis a) := by
  intro x
  refine Q'.eqv_trans _
    (finSum (fun s => coeffAt (listPacketAt N a) s * Cheb.U s x) (N + 1)) _
    (eval_synthesis (listPacketAt N a) x) ?_
  refine Q'.eqv_trans _
    (finSum (fun s => listCoeff a s * Cheb.U s x) (N + 1)) _ ?_ ?_
  · exact finSum_congr_eqv (fun s => by
      rw [coeffAt_listPacketAt a hlen s]
      exact Q'.eqv_refl _) (N + 1)
  · refine Q'.eqv_trans _
      (finSum (fun s => listCoeff a s * Cheb.U s x) a.length) _ ?_ ?_
    · exact finSum_zero_extension hlen (fun i hi => by
        rw [listCoeff_eq_zero_of_length_le a i hi]
        exact q_zero_mul (Cheb.U i x))
    · exact Q'.eqv_trans _ (chebEval a x) _
        (Q'.eqv_symm (chebEval_eq_finSum_listCoeff a x))
        (Q'.eqv_symm (eval_chebSynthesis a x))

/-- The packet vacuum is exactly the list's zeroth Chebyshev coefficient. -/
theorem vacuumHaar_listPacketAt (N : Nat) (a : List Q') :
    (vacuumHaar (listPacketAt N a)).eqv (headCoeff a) := by
  cases a with
  | nil => exact Q'.eqv_refl 0
  | cons c cs => exact Q'.eqv_refl c

/-! ## Every bare polynomial as an explicit packet -/

def polynomialPacketAt (N : Nat) (p : Poly) : CharacterPacket N :=
  listPacketAt N (chebExtract p)

theorem synthesis_polynomialPacketAt {N : Nat} (p : Poly)
    (hlen : (chebExtract p).length <= N + 1) :
    PolyEqv (synthesis (polynomialPacketAt N p)) p :=
  peqv_trans (synthesis_listPacketAt (chebExtract p) hlen)
    (chebExtract_expands p)

theorem vacuumHaar_polynomialPacketAt (N : Nat) (p : Poly) :
    (vacuumHaar (polynomialPacketAt N p)).eqv (bareVacuumHaar p) :=
  vacuumHaar_listPacketAt N (chebExtract p)

/-! ## Common-cutoff fusion of arbitrary bare polynomials -/

def pairCutoff (p q : Poly) : Nat :=
  max (chebExtract p).length (chebExtract q).length

def leftPolynomialPacket (p q : Poly) : CharacterPacket (pairCutoff p q) :=
  polynomialPacketAt (pairCutoff p q) p

def rightPolynomialPacket (p q : Poly) : CharacterPacket (pairCutoff p q) :=
  polynomialPacketAt (pairCutoff p q) q

theorem synthesis_leftPolynomialPacket (p q : Poly) :
    PolyEqv (synthesis (leftPolynomialPacket p q)) p := by
  apply synthesis_polynomialPacketAt
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)

theorem synthesis_rightPolynomialPacket (p q : Poly) :
    PolyEqv (synthesis (rightPolynomialPacket p q)) q := by
  apply synthesis_polynomialPacketAt
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)

theorem vacuumHaar_leftPolynomialPacket (p q : Poly) :
    (vacuumHaar (leftPolynomialPacket p q)).eqv (bareVacuumHaar p) :=
  vacuumHaar_polynomialPacketAt (pairCutoff p q) p

theorem vacuumHaar_rightPolynomialPacket (p q : Poly) :
    (vacuumHaar (rightPolynomialPacket p q)).eqv (bareVacuumHaar q) :=
  vacuumHaar_polynomialPacketAt (pairCutoff p q) q

/-- The full existing Clebsch--Gordan packet attached constructively to a pair
of arbitrary bare polynomials. -/
def polynomialFusionPacket (p q : Poly) : CharacterPacket (2 * pairCutoff p q) :=
  fusionPacket (leftPolynomialPacket p q) (rightPolynomialPacket p q)

/-- Haar on the packaged fusion product of two arbitrary bare polynomials. -/
def bareFusionHaar (p q : Poly) : Q' :=
  vacuumHaar (polynomialFusionPacket p q)

theorem bareFusionHaar_eq_diagonal (p q : Poly) :
    (bareFusionHaar p q).eqv
      (YMGap.Continuum.BondMovingStep.fsum
        (fun a => coeffAt (leftPolynomialPacket p q) a *
          coeffAt (rightPolynomialPacket p q) a)
        (pairCutoff p q + 1)) := by
  exact Q'.eqv_trans _ _ _
    (vacuumHaar_fusionPacket (leftPolynomialPacket p q)
      (rightPolynomialPacket p q))
    (fusionHaar_eq_diagonal (leftPolynomialPacket p q)
      (rightPolynomialPacket p q))

/-- Exact all-mode square positivity after constructive descent from an
arbitrary bare polynomial to its common-cutoff character packet. -/
theorem bareFusionHaar_square_nonneg (p : Poly) :
    (0 : Q') <= bareFusionHaar p p := by
  exact Q'.le_trans' _ _ _
    (vacuumHaar_fusionSquare_nonneg (leftPolynomialPacket p p))
    (Q'.le_of_eqv (Q'.eqv_refl _))

/-- The positive square is the vacuum of an actual, finite, synthesized class
polynomial carried by the existing fusion packet. -/
def polynomialFusionProduct (p q : Poly) : Poly :=
  synthesis (polynomialFusionPacket p q)

theorem polynomialFusionProduct_vacuum_nonneg (p : Poly) :
    (0 : Q') <= vacuumHaar (polynomialFusionPacket p p) :=
  bareFusionHaar_square_nonneg p

end YMGap.Continuum.SU2ClassPolynomialPacketDescent

#print axioms YMGap.Continuum.SU2ClassPolynomialPacketDescent.coeffAt_listPacketAt
#print axioms YMGap.Continuum.SU2ClassPolynomialPacketDescent.chebEvalFrom_eq_finSum_listCoeff
#print axioms YMGap.Continuum.SU2ClassPolynomialPacketDescent.synthesis_listPacketAt
#print axioms YMGap.Continuum.SU2ClassPolynomialPacketDescent.synthesis_polynomialPacketAt
#print axioms YMGap.Continuum.SU2ClassPolynomialPacketDescent.vacuumHaar_leftPolynomialPacket
#print axioms YMGap.Continuum.SU2ClassPolynomialPacketDescent.bareFusionHaar_eq_diagonal
#print axioms YMGap.Continuum.SU2ClassPolynomialPacketDescent.bareFusionHaar_square_nonneg
