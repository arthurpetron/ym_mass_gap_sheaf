/-
# All-label invariant diagonal Gram weights for Cayley transvectants

The finite mixed recoupling modules computed individual Hilbert--Schmidt
weights.  Here the computation is made uniform.  For arbitrary external
twice-spin labels `a,b,c`, output label `d`, and an arbitrary trilinear binary
form map `L`, the diagonal invariant Gram value is exactly

  sum_{i,j,k,s}
    C(a,i) C(b,j) C(c,k) / C(d,s) * L(i,j,k;s)^2.

The implementation writes `1/C(d,s)` as `symMonomialNormSq d s`; no division
operation or square root is introduced.  Thus every input reciprocal norm and
the output monomial norm remains visible in the theorem statement.  We also
prove uniformly that these factors, and hence the complete diagonal weight,
are nonnegative.  The reciprocal normalization identity

  symMonomialNormSq n i * tvBinomQ n i = 1   (i <= n)

is proved directly from the factorial carriers.

This is stronger than an admissibility-window computation: it holds for all
natural labels and every map.  In particular it applies to every admissible
left- and right-associated transvectant channel without a finite label table.
-/

import YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
import YMGap.RG.TonelliFactor

namespace YMGap.Continuum.SU2TransvectantAllLabelGramCompleted

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted

local infix:50 " ≈ " => Q'.eqv

/-! ## Exact reciprocal monomial normalization -/

private theorem mkN_den_of_pred (n d : Nat) (hd : 0 < d) :
    (Q'.mkN n (d - 1)).den = d := by
  change d - 1 + 1 = d
  omega

/-- A rational with a natural numerator and positive stored denominator is
nonnegative. -/
theorem mkN_nonneg_all (n d : Nat) : (0 : Q') ≤ Q'.mkN n d := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

/-- Every factorial binomial normalization is nonnegative, including indices
outside its support. -/
theorem tvBinomQ_nonneg_all (n i : Nat) : (0 : Q') ≤ tvBinomQ n i := by
  unfold tvBinomQ
  split
  · exact mkN_nonneg_all _ _
  · exact Q'.le_refl' 0

/-- Every invariant monomial squared norm is nonnegative, including indices
outside the degree window. -/
theorem symMonomialNormSq_nonneg_all (n i : Nat) :
    (0 : Q') ≤ symMonomialNormSq n i := by
  unfold symMonomialNormSq
  split
  · exact mkN_nonneg_all _ _
  · exact Q'.le_refl' 0

/-- The invariant monomial norm is exactly reciprocal to the binomial input
normalization.  This pins the output factor in `triMapInner`; it is not an
independent or measured constant. -/
theorem symMonomialNormSq_mul_tvBinomQ (n i : Nat) (hi : i ≤ n) :
    symMonomialNormSq n i * tvBinomQ n i ≈ 1 := by
  unfold symMonomialNormSq tvBinomQ
  rw [if_pos hi, if_pos hi]
  let A := tvFact i * tvFact (n - i)
  let B := tvFact n
  have hA : 0 < A := Nat.mul_pos (tvFact_pos i) (tvFact_pos (n - i))
  have hB : 0 < B := tvFact_pos n
  show (Q'.mkN A (B - 1) * Q'.mkN B (A - 1)).num * ((1 : Q').den : Int) =
    (1 : Q').num * ((Q'.mkN A (B - 1) * Q'.mkN B (A - 1)).den : Int)
  rw [Q'.mul_num_cast, Q'.mul_den_cast]
  rw [mkN_den_of_pred A B hB, mkN_den_of_pred B A hA]
  change ((A : Int) * (B : Int)) * 1 = 1 * ((B : Int) * (A : Int))
  simp only [Int.mul_one, Int.one_mul]
  exact Int.mul_comm (A : Int) (B : Int)

/-! ## The all-label diagonal identity -/

/-- One fully normalized diagonal Hilbert--Schmidt summand.  The first three
factors are reciprocal input monomial norms; the fourth is the invariant
output monomial norm; the last factor is the exact coefficient square. -/
def triDiagonalSummand (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm)
    (i j k s : Nat) : Q' :=
  tvBinomQ a i * tvBinomQ b j * tvBinomQ c k *
    symMonomialNormSq d s *
      (L (mono i) (mono j) (mono k) s *
        L (mono i) (mono j) (mono k) s)

/-- The exact finite diagonal weight for an arbitrary trilinear map. -/
def triDiagonalWeight (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm) : Q' :=
  finSum (fun i => finSum (fun j => finSum (fun k => finSum (fun s =>
    triDiagonalSummand a b c d L i j k s) (d + 1)) (c + 1))
      (b + 1)) (a + 1)

/-- **Uniform all-label invariant diagonal Gram identity.**  This is the exact
`triMapInner` diagonal, with every channel normalization factor displayed.
It holds for arbitrary natural labels and arbitrary maps, hence in particular
for every admissible transvectant channel. -/
theorem triMapInner_diagonal_all_labels (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm) :
    triMapInner a b c d L L =
      finSum (fun i => finSum (fun j => finSum (fun k => finSum (fun s =>
        tvBinomQ a i * tvBinomQ b j * tvBinomQ c k *
          symMonomialNormSq d s *
            (L (mono i) (mono j) (mono k) s *
              L (mono i) (mono j) (mono k) s))
        (d + 1)) (c + 1)) (b + 1)) (a + 1) := rfl

theorem triDiagonalSummand_nonneg (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm)
    (i j k s : Nat) :
    (0 : Q') ≤ triDiagonalSummand a b c d L i j k s := by
  unfold triDiagonalSummand
  have hab := Q'.mul_nonneg _ _
    (tvBinomQ_nonneg_all a i) (tvBinomQ_nonneg_all b j)
  have habc := Q'.mul_nonneg _ _ hab (tvBinomQ_nonneg_all c k)
  have habcd := Q'.mul_nonneg _ _ habc (symMonomialNormSq_nonneg_all d s)
  exact Q'.mul_nonneg _ _ habcd
    (SumOfSquares.q_mul_self_nonneg (L (mono i) (mono j) (mono k) s))

/-- The all-label invariant diagonal weight is nonnegative.  This supplies the
reflection-positivity witness needed to make any individual channel into a
constructive weighted GNS line. -/
theorem triMapInner_diagonal_nonneg_all (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm) :
    (0 : Q') ≤ triMapInner a b c d L L := by
  rw [triMapInner_diagonal_all_labels]
  refine YMGap.RG.finSum_nonneg _ (fun i => ?_) (a + 1)
  refine YMGap.RG.finSum_nonneg _ (fun j => ?_) (b + 1)
  refine YMGap.RG.finSum_nonneg _ (fun k => ?_) (c + 1)
  refine YMGap.RG.finSum_nonneg _ (fun s => ?_) (d + 1)
  exact triDiagonalSummand_nonneg a b c d L i j k s

/-! ## Uniform channel weights for the two local bracketings -/

def triLeftChannelWeight (a b c d e : Nat) : Q' :=
  triMapInner a b c d (triLeft a b c d e) (triLeft a b c d e)

def triRightChannelWeight (a b c d f : Nat) : Q' :=
  triMapInner a b c d (triRight a b c d f) (triRight a b c d f)

theorem triLeftChannelWeight_nonneg_all (a b c d e : Nat) :
    (0 : Q') ≤ triLeftChannelWeight a b c d e :=
  triMapInner_diagonal_nonneg_all a b c d (triLeft a b c d e)

theorem triRightChannelWeight_nonneg_all (a b c d f : Nat) :
    (0 : Q') ≤ triRightChannelWeight a b c d f :=
  triMapInner_diagonal_nonneg_all a b c d (triRight a b c d f)

end YMGap.Continuum.SU2TransvectantAllLabelGramCompleted

#print axioms YMGap.Continuum.SU2TransvectantAllLabelGramCompleted.mkN_nonneg_all
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGramCompleted.tvBinomQ_nonneg_all
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGramCompleted.symMonomialNormSq_nonneg_all
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGramCompleted.symMonomialNormSq_mul_tvBinomQ
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGramCompleted.triMapInner_diagonal_all_labels
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGramCompleted.triDiagonalSummand_nonneg
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGramCompleted.triMapInner_diagonal_nonneg_all
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGramCompleted.triLeftChannelWeight_nonneg_all
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGramCompleted.triRightChannelWeight_nonneg_all
