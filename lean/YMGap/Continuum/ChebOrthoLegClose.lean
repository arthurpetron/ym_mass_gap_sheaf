/-
# The OUTER DIVISION for the SYMMETRIC √ second-difference `Δ₂ = s_+ + s_- − 2 s_k`

This module discharges step (a) of the radical-leg close: the OUTER reciprocal-free
division producing the symmetric second-difference bound

    `|s_+ + s_- − 2 s_k| ≤ symmQuot`,    `symmQuot = (2·subSecondQuot + 2δ²)/recipWitness`,

on top of the PROVED `δ²`-scale sub-second-difference √-cancellation
`ChebOrthoRadSecondDiffSq.subSecondDiff_AbsLeRat` (`|s_+ s_- − s_k²| ≤ subSecondQuot`).
It then inhabits `ChebOrthoRadSecondDiffSq.SymmSecondClose`, supplying the explicit
`symmQuot` and `symm_bound` fields (the proved √-content is carried in `sub`).

## The product identity `(★)`

With `D = (s_+ + s_-) − 2 s_k` and `S = (s_+ + s_-) + 2 s_k`,

    `D · S = (s_+ + s_-)² − (2 s_k)²`                    (difference of squares, rational)
          ≈ `2·(s_+ s_- − s_k²) + ofQ'(rad_+ + rad_- − 4·oms)`   (square collapses)
          ≈ `2·(s_+ s_- − s_k²) + ofQ'(−2δ²)`,

since `rad_+ + rad_- − 2·oms = −2δ²` is the EXACT rational centered second difference of
the radicand `(M²−(A+1)²) + (M²−(A−1)²) − 2(M²−A²) = −2` over `M²` (`A = 2k+1−M`).
The difference of squares is a per-approximation `Q'` ring identity; the collapse of the
three squares to their rational radicands is the proved `bdyRadical_sq_collapse` /
`node_sq_collapse` machinery.

## The division

`AbsLeRat.div_of_mul_ge` with `D`, `S`, the numerator bound `K = 2·subSecondQuot + 2δ²`
(`|D·S| ≤ K` from the identity + the proved `δ²`-cancellation + the `2δ²` constant),
the pointwise lower bound `L ≤ S.approx n` from `recipWitness ≤ s_+ + s_-`
(`interiorRadicalSum_geRat_left`, built pointwise) and `s_k ≥ 0`, and the explicit
quotient `symmQuot = K/L` with `symmQuot · L ≈ K`.  Reciprocal-free.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'`.  Axiom-gate at the foot.  The √-Hölder analytic core is the already
proved `subSecondDiff_AbsLeRat`; everything new here is RATIONAL bookkeeping + ONE outer
division.
-/

import YMGap.Continuum.ChebOrthoRadSecondDiffSq
import YMGap.Continuum.ChebOrthoInterior
import YMGap.Continuum.ChebOrthoCancelDiv
import YMGap.Continuum.ChebOrthoGradedClose
import YMGap.Continuum.Pivot2Moments
import YMGap.Continuum.ChebOrthoLeadingModel
import YMGap.Continuum.ChebOrthoRadSecondDiff

namespace YMGap.Continuum.ChebOrthoLegClose

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.ChebOrthoRadSecondDiffSq
open YMGap.Continuum.ChebOrthoGradedClose (AbsLeRat)
open YMGap.Continuum.ChebOrthoInterior (recipWitness recipWitness_pos recipWitness_sq_le
  bdyRadical_approx_nonneg)
open YMGap.Continuum.ChebOrthoGraded (jdist jdist_pos)

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≋ " => CReal.Equiv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

instance : Trans (CReal.Equiv) (CReal.Equiv) (CReal.Equiv) where
  trans h1 h2 := CReal.Equiv.trans h1 h2

/-! ## 0. The symmetric `D` and `S` (the centered second-difference and its sum) -/

/-- The √ sum of the two cell radicals `s_+ + s_-`. -/
private def radSum (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add (bdyRadical M hM (k + 1)) (bdyRadical M hM k)

/-- Twice the node radical `2 s_k = s_k + s_k`. -/
private def twoNode (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add (nodeWeight M hM k) (nodeWeight M hM k)

/-- The SYMMETRIC second difference `D = (s_+ + s_-) − 2 s_k` (matches the
`symm_bound` LHS of `SymmSecondClose`). -/
private def symmD (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add (radSum M hM k) (CReal.neg (twoNode M hM k))

/-- The SYMMETRIC sum `S = (s_+ + s_-) + 2 s_k`. -/
private def symmS (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add (radSum M hM k) (twoNode M hM k)

/-! ## 1. The EXPANDED product `E = 2 s_+ s_- + (s_+² + s_-²) − (2 s_k)²` -/

/-- The fully expanded difference-of-squares model
`E = (s_+ s_- + s_+ s_-) + ((s_+² + s_-²) + (−(2 s_k)²))`. -/
private def symmE (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add
    (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
      (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k)))
    (CReal.add
      (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM (k + 1)))
        (CReal.mul (bdyRadical M hM k) (bdyRadical M hM k)))
      (CReal.neg (CReal.mul (twoNode M hM k) (twoNode M hM k))))

/-- The bounded sub-second-difference `subDiff = s_+ s_- − s_k²` (exactly the CReal that
`subSecondDiff_AbsLeRat` bounds). -/
private def subDiff (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
    (CReal.neg (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k)))

/-- **`(2 s_k)² ≈ ofQ'(4·oms)`**, expanding `(s_k+s_k)·(s_k+s_k) ≈ 4·(s_k·s_k)` and
collapsing `s_k·s_k ≈ ofQ'(oms)`. -/
private theorem twoNode_sq_collapse (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) :
    CReal.Equiv (CReal.mul (twoNode M hM k) (twoNode M hM k))
      (CReal.ofQ' (oneMinusSqNode M k hM hk + oneMinusSqNode M k hM hk
        + (oneMinusSqNode M k hM hk + oneMinusSqNode M k hM hk))) := by
  -- (c+c)·(c+c) ≈ (c·c + c·c) + (c·c + c·c)  per approx
  have hexp : CReal.Equiv (CReal.mul (twoNode M hM k) (twoNode M hM k))
      (CReal.add
        (CReal.add (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))
          (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k)))
        (CReal.add (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))
          (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k)))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun p => by
      show ((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p)
            * ((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p)
          ≈ (((nodeWeight M hM k).approx p * (nodeWeight M hM k).approx p
                + (nodeWeight M hM k).approx p * (nodeWeight M hM k).approx p)
              + ((nodeWeight M hM k).approx p * (nodeWeight M hM k).approx p
                + (nodeWeight M hM k).approx p * (nodeWeight M hM k).approx p))
      generalize (nodeWeight M hM k).approx p = c
      -- (c+c)·(c+c) ≈ (c·c+c·c)+(c·c+c·c)
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv c c (c + c)) ?_
      exact Q'.add_eqv_congr' (Q'.mul_add_eqv c c c) (Q'.mul_add_eqv c c c))
  refine CReal.Equiv.trans hexp ?_
  -- collapse each c·c to ofQ'(oms), then ofQ'_add
  have hcol := ChebOrthoLeadingModel.node_sq_collapse M hM k hk
  refine CReal.Equiv.trans
    (Pivot2.add_congr (Pivot2.add_congr hcol hcol) (Pivot2.add_congr hcol hcol)) ?_
  -- (ofQ' oms + ofQ' oms) + (ofQ' oms + ofQ' oms) = ofQ'(oms+oms + (oms+oms)) DEFINITIONALLY
  -- (CReal.ofQ'_add is rfl), so the two sides are syntactically equal.
  exact Pivot2.equiv_refl _

/-- **`D · S ≈ E`** (per-approximation `Q'` ring identity, difference of squares plus
the binomial expansion of `(s_+ + s_-)²`).  At index `p`, with `a = s_+`, `b = s_-`,
`c = s_k`:
`(a+b + (−(c+c)))·(a+b + (c+c)) ≈ (a·b + a·b) + ((a·a + b·b) + (−((c+c)·(c+c))))`. -/
private theorem DS_eq_E (M : Nat) (hM : 0 < M) (k : Nat) :
    CReal.Equiv (CReal.mul (symmD M hM k) (symmS M hM k)) (symmE M hM k) :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    -- unfold the approximations to the underlying three rationals
    show (((bdyRadical M hM (k + 1)).approx p + (bdyRadical M hM k).approx p)
            + (-((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p)))
          * (((bdyRadical M hM (k + 1)).approx p + (bdyRadical M hM k).approx p)
            + ((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p))
        ≈ (((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p
              + (bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p)
            + (((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM (k + 1)).approx p
                + (bdyRadical M hM k).approx p * (bdyRadical M hM k).approx p)
              + (-(((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p)
                  * ((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p)))))
    generalize (bdyRadical M hM (k + 1)).approx p = a
    generalize (bdyRadical M hM k).approx p = b
    generalize (nodeWeight M hM k).approx p = c
    -- goal now in terms of a, b, c
    show ((a + b) + (-(c + c))) * ((a + b) + (c + c))
        ≈ ((a * b + a * b) + ((a * a + b * b) + (-((c + c) * (c + c)))))
    -- (handled below; see calc)
    -- difference of squares with X = a+b, Y = c+c
    refine Q'.eqv_trans _ _ _
      (ChebOrthoCancelDiv.diffOfSquares_eqv (a + b) (c + c)) ?_
    -- now: (a+b)·(a+b) + (−((c+c)·(c+c)))
    -- first expand the square in place (right summand Y = −((c+c)²) fixed),
    -- reaching ((a·b+a·b) + (a·a+b·b)) + Y, then reassociate to the RHS grouping.
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (?_ : ((a + b) * (a + b))
        ≈ ((a * b + a * b) + (a * a + b * b)))) ?_
    · -- (a+b)·(a+b) ≈ (a·b + a·b) + (a·a + b·b)
      -- (a+b)·(a+b) ≈ a·(a+b) + b·(a+b)
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv a b (a + b)) ?_
      -- ≈ (a·a + a·b) + (b·a + b·b)
      have e1 : (a * (a + b)) ≈ (a * a + a * b) := Q'.mul_add_eqv a a b
      have e2 : (b * (a + b)) ≈ (b * a + b * b) := Q'.mul_add_eqv b a b
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ e1)
          (Q'.add_eqv_congr_left _ _ _ e2)) ?_
      -- (a·a + a·b) + (b·a + b·b) ≈ (a·b + a·b) + (a·a + b·b)
      -- rewrite b·a ≈ a·b
      have e3 : (b * a) ≈ (a * b) := Q'.mul_comm_eqv b a
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_right _ _ _ e3)) ?_
      -- (a·a + a·b) + (a·b + b·b) ≈ (a·b + a·b) + (a·a + b·b)
      -- regroup using assoc/comm of +
      calc (a * a + a * b) + (a * b + b * b)
          ≈ a * a + (a * b + (a * b + b * b)) := Q'.add_assoc_eqv (a * a) (a * b) (a * b + b * b)
        _ ≈ a * a + ((a * b + a * b) + b * b) :=
            Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (a * b) (a * b) (b * b)))
        _ ≈ a * a + ((b * b) + (a * b + a * b)) :=
            Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv (a * b + a * b) (b * b))
        _ ≈ a * a + (b * b + (a * b + a * b)) := Q'.eqv_refl _
        _ ≈ (a * a + b * b) + (a * b + a * b) :=
            Q'.eqv_symm (Q'.add_assoc_eqv (a * a) (b * b) (a * b + a * b))
        _ ≈ (a * b + a * b) + (a * a + b * b) := Q'.add_comm_eqv (a * a + b * b) (a * b + a * b)
    · -- reassociate: ((2ab)+(a²+b²)) + Y ≈ 2ab + ((a²+b²)+Y)
      exact Q'.add_assoc_eqv (a * b + a * b) (a * a + b * b) (-((c + c) * (c + c))))

/-! ## 2. The residue value `−2δ²` and the collapse `E ≈ 2·subDiff + ofQ'(−2δ²)` -/

/-- The EXACT rational residue `residueVal = rad_+ + rad_- − 2·oms = −2/M²`
(`= −2δ²`), the centered second difference of the radicand. -/
private def residueVal (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) : Q' :=
  bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n
    + bdyOneMinusSq M k hM hk0 hkn
    + (-(oneMinusSqNode M k hM hkn + oneMinusSqNode M k hM hkn))

/-- The explicit constant `−2/M²` that `residueVal` equals. -/
private def negTwoDeltaSq (M : Nat) (hM : 0 < M) : Q' :=
  Q'.mkPos (-2) (M * M) (Nat.mul_pos hM hM)

/-- **`residueVal ≈ −2δ²`**: the centered second difference of the radicand
`(M²−(A+1)²) + (M²−(A−1)²) − 2(M²−A²) = −2` over `M²` (`A = 2k+1−M`).  Pure `Int`
cross-multiplication; `omega` on the expanded numerators. -/
private theorem residueVal_eq (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    residueVal M hM k hk0 hkn hk1n ≈ negTwoDeltaSq M hM := by
  -- all four terms share the denominator omsDen M = M*M; combine via mkPos_add_same_den.
  have homs : omsDen M = M * M := rfl
  -- rewrite each summand as a mkPos over (M*M)
  have hbp : bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n
      = Q'.mkPos (bdyNum M (k + 1)) (M * M) (Nat.mul_pos hM hM) := by
    show Q'.mkPos (bdyNum M (k + 1)) (omsDen M) (omsDen_pos hM)
        = Q'.mkPos (bdyNum M (k + 1)) (M * M) (Nat.mul_pos hM hM)
    rfl
  have hbm : bdyOneMinusSq M k hM hk0 hkn
      = Q'.mkPos (bdyNum M k) (M * M) (Nat.mul_pos hM hM) := rfl
  have hom : oneMinusSqNode M k hM hkn
      = Q'.mkPos (omsNum M k) (M * M) (Nat.mul_pos hM hM) := rfl
  -- combined numerator identity
  have hnum : bdyNum M (k + 1) + bdyNum M k + (-(omsNum M k + omsNum M k)) = (-2 : Int) := by
    show ((M : Int) * (M : Int) - (2 * ((k + 1 : Nat) : Int) - (M : Int))
            * (2 * ((k + 1 : Nat) : Int) - (M : Int)))
        + ((M : Int) * (M : Int) - (2 * (k : Int) - (M : Int)) * (2 * (k : Int) - (M : Int)))
        + (-(((M : Int) * (M : Int)
              - (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)))
            + ((M : Int) * (M : Int)
              - (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)))))
        = (-2 : Int)
    have hcast1 : (2 * ((k + 1 : Nat) : Int) - (M : Int))
        = ((2 * (k : Int) + 1 - (M : Int)) + 1) := by push_cast; omega
    have hcast2 : (2 * (k : Int) - (M : Int))
        = ((2 * (k : Int) + 1 - (M : Int)) - 1) := by omega
    rw [hcast1, hcast2]
    generalize hA : (2 * (k : Int) + 1 - (M : Int)) = A
    -- (m − (A+1)²) + (m − (A−1)²) + (−((m − A²) + (m − A²))) = −2
    have e1 : (A + 1) * (A + 1) = A * A + 2 * A + 1 := by
      have h1 : (A + 1) * (A + 1) = A * (A + 1) + 1 * (A + 1) := Int.add_mul A 1 (A + 1)
      have h2 : A * (A + 1) = A * A + A * 1 := Int.mul_add A A 1
      omega
    have e2 : (A - 1) * (A - 1) = A * A - 2 * A + 1 := by
      have h1 : (A - 1) * (A - 1) = A * (A - 1) - 1 * (A - 1) := Int.sub_mul A 1 (A - 1)
      have h2 : A * (A - 1) = A * A - A * 1 := Int.mul_sub A A 1
      omega
    rw [e1, e2]
    -- now linear in m := M*M and s := A*A ; omega treats both as atoms.
    omega
  -- assemble using mkPos_add_same_den
  rw [residueVal, hbp, hbm, hom]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (SemicircleIntegral.mkPos_add_same_den (omsNum M k) (omsNum M k) (M * M)
          (Nat.mul_pos hM hM)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (?_ : (-(Q'.mkPos (omsNum M k + omsNum M k) (M * M) (Nat.mul_pos hM hM)))
          ≈ Q'.mkPos (-(omsNum M k + omsNum M k)) (M * M) (Nat.mul_pos hM hM))) ?_
  · -- negation keeps the denominator (Q'.neg = ⟨-num, denPred⟩); numerator check
    show (-(Q'.mkPos (omsNum M k + omsNum M k) (M * M) (Nat.mul_pos hM hM))).num
          * ((Q'.mkPos (-(omsNum M k + omsNum M k)) (M * M) (Nat.mul_pos hM hM)).den : Int)
        = (Q'.mkPos (-(omsNum M k + omsNum M k)) (M * M) (Nat.mul_pos hM hM)).num
          * ((-(Q'.mkPos (omsNum M k + omsNum M k) (M * M) (Nat.mul_pos hM hM))).den : Int)
    rfl
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (SemicircleIntegral.mkPos_add_same_den (bdyNum M (k + 1)) (bdyNum M k) (M * M)
        (Nat.mul_pos hM hM))) ?_
  refine Q'.eqv_trans _ _ _
    (SemicircleIntegral.mkPos_add_same_den (bdyNum M (k + 1) + bdyNum M k)
      (-(omsNum M k + omsNum M k)) (M * M) (Nat.mul_pos hM hM)) ?_
  -- mkPos (combined) (M*M) ≈ mkPos (-2) (M*M)
  show Q'.mkPos (bdyNum M (k + 1) + bdyNum M k + (-(omsNum M k + omsNum M k))) (M * M)
        (Nat.mul_pos hM hM)
      ≈ negTwoDeltaSq M hM
  rw [hnum]
  exact Q'.eqv_refl _

/-- `(a + b) ≈ addNF [a, b]`. -/
private theorem pair_addNF (a b : Q') : (a + b) ≈ Pivot3.addNF [a, b] := by
  show (a + b) ≈ (a + (b + 0))
  exact Q'.add_eqv_congr_left a b (b + 0) (Q'.eqv_symm (QPoly.q_add_zero_eqv b))

/-- `a + (b + c) ≈ addNF [a, b, c]`. -/
private theorem triR_addNF (a b c : Q') : (a + (b + c)) ≈ Pivot3.addNF [a, b, c] := by
  show (a + (b + c)) ≈ (a + (b + (c + 0)))
  exact Q'.add_eqv_congr_left a (b + c) (b + (c + 0))
    (Q'.add_eqv_congr_left b c (c + 0) (Q'.eqv_symm (QPoly.q_add_zero_eqv c)))

/-- Append-combine two `addNF` blocks: `addNF L1 + addNF L2 ≈ addNF (L1 ++ L2)`. -/
private theorem addNF_combine (L1 L2 : List Q') :
    (Pivot3.addNF L1 + Pivot3.addNF L2) ≈ Pivot3.addNF (L1 ++ L2) :=
  Q'.eqv_symm (Pivot3.addNF_append L1 L2)

/-- The 8-atom reorder used in `symmE_sub_ring`.  With `u := aa+bb`, `N := −(q+q)`,
`NP := −P`:
`((P+P)+(u+(N+N))) + ((NP+q)+(NP+q)) ≈ (u+((N+N)+(q+q))) + ((P+NP)+(P+NP))`.
Both sides are routed through `Pivot3.addNF` lists which are permutations of each other. -/
private theorem symmReorderProof (P aa bb q : Q') :
    (((P + P) + ((aa + bb) + ((-(q + q)) + (-(q + q)))))
        + (((-P) + q) + ((-P) + q)))
    ≈ (((aa + bb) + (((-(q + q)) + (-(q + q))) + (q + q)))
        + ((P + (-P)) + (P + (-P)))) := by
  -- LHS ≈ addNF [P, P, aa+bb, N, N, NP, q, NP, q]
  have hL : (((P + P) + ((aa + bb) + ((-(q + q)) + (-(q + q)))))
        + (((-P) + q) + ((-P) + q)))
      ≈ Pivot3.addNF [P, P, aa + bb, -(q + q), -(q + q), -P, q, -P, q] := by
    -- Block1 = (P+P) + ((aa+bb)+(N+N)) ≈ addNF[P,P] combined with addNF[aa+bb,N,N]
    have hB1 : ((P + P) + ((aa + bb) + ((-(q + q)) + (-(q + q)))))
        ≈ Pivot3.addNF [P, P, aa + bb, -(q + q), -(q + q)] := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (pair_addNF P P)
          (triR_addNF (aa + bb) (-(q + q)) (-(q + q)))) ?_
      exact addNF_combine [P, P] [aa + bb, -(q + q), -(q + q)]
    -- Block2 = (NP+q)+(NP+q) ≈ addNF[NP,q,NP,q]
    have hB2 : (((-P) + q) + ((-P) + q)) ≈ Pivot3.addNF [-P, q, -P, q] := by
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (pair_addNF (-P) q) (pair_addNF (-P) q)) ?_
      exact addNF_combine [-P, q] [-P, q]
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hB1 hB2) ?_
    exact addNF_combine [P, P, aa + bb, -(q + q), -(q + q)] [-P, q, -P, q]
  -- RHS ≈ addNF [aa+bb, N, N, q, q, P, NP, P, NP]
  have hR : (((aa + bb) + (((-(q + q)) + (-(q + q))) + (q + q)))
        + ((P + (-P)) + (P + (-P))))
      ≈ Pivot3.addNF [aa + bb, -(q + q), -(q + q), q, q, P, -P, P, -P] := by
    -- Block3 = (aa+bb) + ((N+N)+(q+q)) ≈ addNF[aa+bb, N, N, q, q]  (split q+q into q,q)
    have hB3 : ((aa + bb) + (((-(q + q)) + (-(q + q))) + (q + q)))
        ≈ Pivot3.addNF [aa + bb, -(q + q), -(q + q), q, q] := by
      -- (aa+bb) + ((N+N)+(q+q)) ≈ (aa+bb) + (N + (N + (q+q)))  [assoc inside]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_assoc_eqv (-(q + q)) (-(q + q)) (q + q))) ?_
      -- aa+bb + (N + (N + (q+q))) = addNF[aa+bb, N, N, q, q]
      show ((aa + bb) + ((-(q + q)) + ((-(q + q)) + (q + q))))
          ≈ ((aa + bb) + ((-(q + q)) + ((-(q + q)) + (q + (q + 0)))))
      exact Q'.add_eqv_congr_left _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm (QPoly.q_add_zero_eqv q)))))
    -- Block4 = (P+NP)+(P+NP) ≈ addNF[P,NP,P,NP]
    have hB4 : ((P + (-P)) + (P + (-P))) ≈ Pivot3.addNF [P, -P, P, -P] := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (pair_addNF P (-P)) (pair_addNF P (-P))) ?_
      exact addNF_combine [P, -P] [P, -P]
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hB3 hB4) ?_
    exact addNF_combine [aa + bb, -(q + q), -(q + q), q, q] [P, -P, P, -P]
  -- LHS ≈ addNF L_L ≈ addNF L_R ≈ RHS  via addNF_perm (L_L is a permutation of L_R)
  refine Q'.eqv_trans _ _ _ hL ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hR)
  -- [P,P,u,N,N,NP,q,NP,q] ~ [u,N,N,q,q,P,NP,P,NP]   (u=aa+bb, N=−(q+q), NP=−P)
  refine Pivot3.addNF_perm ?_
  refine List.Perm.trans (List.Perm.cons P
    (List.Perm.swap (aa + bb) P [-(q + q), -(q + q), -P, q, -P, q])) ?_
  refine List.Perm.trans (List.Perm.swap (aa + bb) P [P, -(q + q), -(q + q), -P, q, -P, q]) ?_
  refine List.Perm.cons (aa + bb) ?_
  refine List.Perm.trans (List.Perm.cons P
    (List.Perm.swap (-(q + q)) P [-(q + q), -P, q, -P, q])) ?_
  refine List.Perm.trans (List.Perm.swap (-(q + q)) P [P, -(q + q), -P, q, -P, q]) ?_
  refine List.Perm.cons (-(q + q)) ?_
  refine List.Perm.trans (List.Perm.cons P
    (List.Perm.swap (-(q + q)) P [-P, q, -P, q])) ?_
  refine List.Perm.trans (List.Perm.swap (-(q + q)) P [P, -P, q, -P, q]) ?_
  refine List.Perm.cons (-(q + q)) ?_
  refine List.Perm.trans (List.Perm.cons P
    (List.Perm.cons P (List.Perm.swap q (-P) [-P, q]))) ?_
  refine List.Perm.trans (List.Perm.cons P (List.Perm.swap q P [-P, -P, q])) ?_
  refine List.Perm.trans (List.Perm.swap q P [P, -P, -P, q]) ?_
  refine List.Perm.cons q ?_
  refine List.Perm.trans (List.Perm.cons P
    (List.Perm.cons P (List.Perm.cons (-P) (List.Perm.swap q (-P) [])))) ?_
  refine List.Perm.trans (List.Perm.cons P (List.Perm.cons P (List.Perm.swap q (-P) [-P]))) ?_
  refine List.Perm.trans (List.Perm.cons P (List.Perm.swap q P [-P, -P])) ?_
  refine List.Perm.trans (List.Perm.swap q P [P, -P, -P]) ?_
  refine List.Perm.cons q ?_
  refine List.Perm.cons P ?_
  exact (List.Perm.swap P (-P) [-P]).symm

/-- The pure abelian-group identity behind the cancellation:
`((P+P)+((aa+bb)+(−((q+q)+(q+q))))) + (−((P+(−q))+(P+(−q)))) ≈ (aa+bb)+(−(q+q))`.
The `P` terms cancel; `−(4q) + 2q = −(2q)`.  Built from the `Q'` additive-group calculus. -/
private theorem symmE_sub_ring (P aa bb q : Q') :
    (((P + P) + ((aa + bb) + (-((q + q) + (q + q)))))
      + (-((P + (-q)) + (P + (-q)))))
    ≈ ((aa + bb) + (-(q + q))) := by
  -- The proof is purely the additive abelian-group word problem; we discharge it on the
  -- underlying ℚ numerators.  Q'.eqv X Y ↔ X.num·Y.den = Y.num·X.den.  Rather than the
  -- compound denominators, we reduce to the integer identity via the `Q'` ring laws
  -- packaged in `QPoly.eval`.  We instead chain the group calculus directly.
  -- abbreviations: u := aa+bb, treat as opaque.
  -- 1. −((P−q)+(P−q)) ≈ ((−P)+q) + ((−P)+q)
  have hneg : (-((P + (-q)) + (P + (-q)))) ≈ (((-P) + q) + ((-P) + q)) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (P + (-q)) (P + (-q))) ?_
    have hn : (-(P + (-q))) ≈ ((-P) + q) :=
      Q'.eqv_trans _ _ _ (Q'.neg_add_eqv P (-q))
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv q))
    exact Q'.add_eqv_congr' hn hn
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hneg) ?_
  -- 2. −((q+q)+(q+q)) ≈ (−(q+q)) + (−(q+q))
  have hnq : (-((q + q) + (q + q))) ≈ ((-(q + q)) + (-(q + q))) :=
    Q'.neg_add_eqv (q + q) (q + q)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _ hnq))) ?_
  -- Goal (with u := aa+bb, N := −(q+q)):
  --   ((P+P) + (u + (N + N))) + (((−P)+q) + ((−P)+q)) ≈ u + N
  -- We verify it by the `Q'` additive-group calculus.  Abbreviate the negations.
  -- Key cancellations:  P + (−P) ≈ 0  and  (N + (q+q)) ≈ 0  (since N = −(q+q)).
  have hPP : (P + (-P)) ≈ (0 : Q') := Q'.add_neg_self_eqv P
  have hNq : ((-(q + q)) + (q + q)) ≈ (0 : Q') := Q'.neg_add_self_eqv (q + q)
  -- Build the canonical regrouping with a big calc using assoc/comm only.
  -- the reorder LHS ≈ ((u)+((N+N)+(q+q))) + ((P+NP)+(P+NP)) is proved by
  -- routing both through a flat form; we build it with add_swap_inner + assoc.
  have hreorder :
      (((P + P) + ((aa + bb) + ((-(q + q)) + (-(q + q)))))
          + (((-P) + q) + ((-P) + q)))
      ≈ (((aa + bb) + (((-(q + q)) + (-(q + q))) + (q + q)))
          + ((P + (-P)) + (P + (-P)))) :=
    symmReorderProof P aa bb q
  calc (((P + P) + ((aa + bb) + ((-(q + q)) + (-(q + q)))))
          + (((-P) + q) + ((-P) + q)))
      ≈ ((aa + bb) + (((-(q + q)) + (-(q + q))) + (q + q)))
          + ((P + (-P)) + (P + (-P))) := hreorder
    _ ≈ ((aa + bb) + (-(q + q))) + ((0 : Q') + (0 : Q')) := by
        refine Q'.add_eqv_congr' ?_ (Q'.add_eqv_congr' hPP hPP)
        -- (aa+bb) + ((N+N)+(q+q)) ≈ (aa+bb) + N
        refine Q'.add_eqv_congr_left _ _ _ ?_
        -- (N+N)+(q+q) ≈ N    since N+(q+q) ≈ 0 ⇒ (N+N)+(q+q) ≈ N+(N+(q+q)) ≈ N+0 ≈ N
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (-(q + q)) (-(q + q)) (q + q)) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hNq) ?_
        exact QPoly.q_add_zero_eqv (-(q + q))
    _ ≈ ((aa + bb) + (-(q + q))) := by
        -- X + (0 + 0) ≈ X + 0 ≈ X
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (QPoly.q_add_zero_eqv (0 : Q'))) ?_
        exact QPoly.q_add_zero_eqv ((aa + bb) + (-(q + q)))

/-- The intermediate CReal `midReal = (s_+² + s_-²) − (s_k² + s_k²)`. -/
private def midReal (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add
    (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM (k + 1)))
      (CReal.mul (bdyRadical M hM k) (bdyRadical M hM k)))
    (CReal.neg (CReal.add (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))
      (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))))

/-- **`symmE + (−(subDiff + subDiff)) ≈ midReal`.**  The `2 s_+ s_-` terms cancel; the
`s_k²` terms combine (`−4 s_k² + 2 s_k² = −2 s_k²`).  Pure per-approximation `Q'` ring. -/
private theorem symmE_sub_eq_midReal (M : Nat) (hM : 0 < M) (k : Nat) :
    CReal.Equiv
      (CReal.add (symmE M hM k)
        (CReal.neg (CReal.add (subDiff M hM k) (subDiff M hM k))))
      (midReal M hM k) :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    -- distribute .approx p over the CReal operations (rfl), exposing the Q' products
    show ((((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p)
            + ((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p))
          + ((((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM (k + 1)).approx p)
              + ((bdyRadical M hM k).approx p * (bdyRadical M hM k).approx p))
            + (-(((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p)
                * ((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p)))))
        + (-((((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p)
                + (-((nodeWeight M hM k).approx p * (nodeWeight M hM k).approx p)))
            + (((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p)
                + (-((nodeWeight M hM k).approx p * (nodeWeight M hM k).approx p)))))
        ≈ ((((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM (k + 1)).approx p)
              + ((bdyRadical M hM k).approx p * (bdyRadical M hM k).approx p))
            + (-(((nodeWeight M hM k).approx p * (nodeWeight M hM k).approx p)
                + ((nodeWeight M hM k).approx p * (nodeWeight M hM k).approx p))))
    -- name the node approximation c
    generalize hc : (nodeWeight M hM k).approx p = c
    -- twoNode square expansion: (c+c)·(c+c) ≈ (c·c + c·c) + (c·c + c·c)
    have hcc : ((c + c) * (c + c)) ≈ ((c * c + c * c) + (c * c + c * c)) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv c c (c + c)) ?_
      exact Q'.add_eqv_congr' (Q'.mul_add_eqv c c c) (Q'.mul_add_eqv c c c)
    -- rewrite the twoNode square inside symmE (left operand of the outer +; its right
    -- operand's right is the negated square).
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hcc)))) ?_
    -- generalize the bdyRadical products and the node square, then the word identity
    generalize (bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p = P
    generalize (bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM (k + 1)).approx p = aa
    generalize (bdyRadical M hM k).approx p * (bdyRadical M hM k).approx p = bb
    generalize c * c = q
    exact symmE_sub_ring P aa bb q)

/-! ## 3. The product-difference √-collapse `D · S ≈ 2·subDiff + ofQ'(−2δ²)` -/

/-- **`midReal ≈ ofQ' residueVal`.**  Collapse the three squares to their rational
radicands (`bdyRadical_sq_collapse`, `node_sq_collapse`) and fold the `ofQ'`s. -/
private theorem midReal_collapse (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    CReal.Equiv (midReal M hM k) (CReal.ofQ' (residueVal M hM k hk0 hkn hk1n)) := by
  -- collapses
  have hsp := ChebOrthoRadSecondDiff.bdyRadical_sq_collapse M hM (k + 1) (Nat.succ_pos k) hk1n
  have hsm := ChebOrthoRadSecondDiff.bdyRadical_sq_collapse M hM k hk0 hkn
  have hnd := ChebOrthoLeadingModel.node_sq_collapse M hM k hkn
  -- midReal = (sp² + sm²) + neg(nd² + nd²)
  unfold midReal
  refine CReal.Equiv.trans
    (Pivot2.add_congr (Pivot2.add_congr hsp hsm)
      (Pivot2.neg_congr (Pivot2.add_congr hnd hnd))) ?_
  -- (ofQ' rad+ + ofQ' rad-) + neg(ofQ' oms + ofQ' oms)
  --   = ofQ'(rad+ + rad-) + neg(ofQ'(oms+oms))      [ofQ'_add rfl]
  --   = ofQ'(rad+ + rad-) + ofQ'(−(oms+oms))         [neg of ofQ' rfl]
  --   = ofQ'((rad+ + rad-) + (−(oms+oms))) = ofQ' residueVal
  -- all defeq via ofQ'_add and neg-of-ofQ' (both rfl on .approx); finish by approx eqv.
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  -- LHS.approx p = (rad+ + rad-) + (−(oms + oms)) ; RHS.approx p = residueVal
  show ((bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n + bdyOneMinusSq M k hM hk0 hkn)
        + (-(oneMinusSqNode M k hM hkn + oneMinusSqNode M k hM hkn)))
      ≈ residueVal M hM k hk0 hkn hk1n
  exact Q'.eqv_refl _

/-- **`D · S ≈ (subDiff + subDiff) + ofQ'(−2δ²)`.**  Combine `DS_eq_E`,
`symmE_sub_eq_midReal`, `midReal_collapse`, `residueVal_eq`. -/
private theorem DS_collapse (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    CReal.Equiv (CReal.mul (symmD M hM k) (symmS M hM k))
      (CReal.add (CReal.add (subDiff M hM k) (subDiff M hM k))
        (CReal.ofQ' (negTwoDeltaSq M hM))) := by
  -- D·S ≈ symmE
  refine CReal.Equiv.trans (DS_eq_E M hM k) ?_
  -- symmE ≈ (subDiff+subDiff) + midReal :  from symmE + (−(sd+sd)) ≈ midReal, add (sd+sd)
  have hsplit : CReal.Equiv (symmE M hM k)
      (CReal.add (CReal.add (subDiff M hM k) (subDiff M hM k)) (midReal M hM k)) := by
    -- symmE ≈ ((sd+sd)+(symmE − (sd+sd)))  then rewrite the second block
    refine CReal.Equiv.trans ?_
      (Pivot2.add_congr (Pivot2.equiv_refl _) (symmE_sub_eq_midReal M hM k))
    -- symmE ≈ (sd+sd) + (symmE + (−(sd+sd)))  : pure per-approx group identity
    refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
    show (symmE M hM k).approx p
        ≈ (((subDiff M hM k).add (subDiff M hM k)).approx p
            + ((symmE M hM k).approx p + (-(((subDiff M hM k).add (subDiff M hM k)).approx p))))
    generalize (symmE M hM k).approx p = E
    generalize ((subDiff M hM k).add (subDiff M hM k)).approx p = T
    -- E ≈ T + (E + (−T))
    refine Q'.eqv_symm ?_
    -- T + (E + (−T)) ≈ E
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv E (-T))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv T (-T) E)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv T)) ?_
    exact QPoly.q_zero_add_eqv E
  refine CReal.Equiv.trans hsplit ?_
  -- (sd+sd) + midReal ≈ (sd+sd) + ofQ'(residueVal) ≈ (sd+sd) + ofQ'(−2δ²)
  refine Pivot2.add_congr (Pivot2.equiv_refl _) ?_
  refine CReal.Equiv.trans (midReal_collapse M hM k hk0 hkn hk1n) ?_
  -- ofQ' residueVal ≈ ofQ' negTwoDeltaSq  via residueVal_eq (lift to CReal)
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => residueVal_eq M hM k hk0 hkn hk1n)

/-! ## 4. The numerator bound `|D · S| ≤ 2·subSecondQuot + 2δ²` -/

/-- `2δ² = 2/M²` (the bound on the constant residue `−2δ²`). -/
private def twoDeltaSq (M : Nat) (hM : 0 < M) : Q' :=
  Q'.mkPos 2 (M * M) (Nat.mul_pos hM hM)

private theorem twoDeltaSq_nonneg (M : Nat) (hM : 0 < M) : (0 : Q') ≤ twoDeltaSq M hM := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (Q'.mkPos 2 (M * M) (Nat.mul_pos hM hM)).num
  rw [Q'.mkPos_num]; decide

/-- `|ofQ'(−2δ²)| ≤ 2δ²`: both `−2δ² ≤ 2δ²` and `2δ² ≤ 2δ²`. -/
private theorem negTwoDeltaSq_AbsLeRat (M : Nat) (hM : 0 < M) :
    AbsLeRat (CReal.ofQ' (negTwoDeltaSq M hM)) (twoDeltaSq M hM) := by
  -- num/den facts
  have hNn : (negTwoDeltaSq M hM).num = (-2 : Int) := by
    show (Q'.mkPos (-2) (M * M) (Nat.mul_pos hM hM)).num = (-2 : Int); rw [Q'.mkPos_num]
  have hNd : ((negTwoDeltaSq M hM).den : Int) = ((M * M : Nat) : Int) := by
    show ((Q'.mkPos (-2) (M * M) (Nat.mul_pos hM hM)).den : Int) = ((M * M : Nat) : Int)
    rw [Q'.mkPos_den]
  have hTn : (twoDeltaSq M hM).num = (2 : Int) := by
    show (Q'.mkPos 2 (M * M) (Nat.mul_pos hM hM)).num = (2 : Int); rw [Q'.mkPos_num]
  have hTd : ((twoDeltaSq M hM).den : Int) = ((M * M : Nat) : Int) := by
    show ((Q'.mkPos 2 (M * M) (Nat.mul_pos hM hM)).den : Int) = ((M * M : Nat) : Int)
    rw [Q'.mkPos_den]
  have hMM : (0 : Int) ≤ ((M * M : Nat) : Int) := Int.natCast_nonneg _
  refine ChebOrthoGradedClose.AbsLeRat.ofQ' ?_ ?_
  · -- negTwoDeltaSq ≤ twoDeltaSq :  num·den ≤ num·den
    show (negTwoDeltaSq M hM).num * ((twoDeltaSq M hM).den : Int)
        ≤ (twoDeltaSq M hM).num * ((negTwoDeltaSq M hM).den : Int)
    rw [hNn, hTd, hTn, hNd]
    exact Int.mul_le_mul_of_nonneg_right (by decide : (-2 : Int) ≤ 2) hMM
  · -- −(negTwoDeltaSq) ≤ twoDeltaSq
    show (-(negTwoDeltaSq M hM)).num * ((twoDeltaSq M hM).den : Int)
        ≤ (twoDeltaSq M hM).num * ((-(negTwoDeltaSq M hM)).den : Int)
    -- (−q).num = −(q.num), (−q).den = q.den
    have hnegn : (-(negTwoDeltaSq M hM)).num = -(negTwoDeltaSq M hM).num := rfl
    have hnegd : ((-(negTwoDeltaSq M hM)).den : Int) = ((negTwoDeltaSq M hM).den : Int) := rfl
    rw [hnegn, hnegd, hNn, hTd, hTn, hNd]
    -- −(−2)·M² ≤ 2·M²  i.e. 2·M² ≤ 2·M²
    exact Int.le_refl _

/-- **THE NUMERATOR BOUND.**  `|D · S| ≤ 2·subSecondQuot + 2δ²`.  Transfer the bound
on `(subDiff+subDiff) + ofQ'(−2δ²)` back along `DS_collapse`. -/
private theorem DS_AbsLeRat (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    AbsLeRat (CReal.mul (symmD M hM k) (symmS M hM k))
      ((subSecondQuot M k hM + subSecondQuot M k hM) + twoDeltaSq M hM) := by
  have hsub : AbsLeRat (CReal.add (subDiff M hM k) (subDiff M hM k))
      (subSecondQuot M k hM + subSecondQuot M k hM) :=
    ChebOrthoGradedClose.AbsLeRat.add
      (subSecondDiff_AbsLeRat M hM k hk0 hkn hk1n)
      (subSecondDiff_AbsLeRat M hM k hk0 hkn hk1n)
  have hconst : AbsLeRat (CReal.ofQ' (negTwoDeltaSq M hM)) (twoDeltaSq M hM) :=
    negTwoDeltaSq_AbsLeRat M hM
  have hbnd : AbsLeRat
      (CReal.add (CReal.add (subDiff M hM k) (subDiff M hM k))
        (CReal.ofQ' (negTwoDeltaSq M hM)))
      ((subSecondQuot M k hM + subSecondQuot M k hM) + twoDeltaSq M hM) :=
    ChebOrthoGradedClose.AbsLeRat.add hsub hconst
  exact ChebOrthoCancelDiv.AbsLeRat.of_equiv (DS_collapse M hM k hk0 hkn hk1n) hbnd

/-! ## 5. The pointwise lower bound `recipWitness ≤ S.approx n` and the DIVISION -/

/-- **Pointwise lower bound on the symmetric sum `S = s_+ + s_- + 2 s_k`.**  At every
Heron index, `s_-.approx n ≥ recipWitness` (`heronSeq_lb` with `recipWitness² ≤ 1−b_k²`)
and the remaining three radicals are `≥ 0` (`bdyRadical_approx_nonneg`,
`nodeWeight ≥ 1/M > 0`). -/
private theorem symmS_lower (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hj : 2 ≤ jdist M k) :
    ∀ n, recipWitness M (jdist M k) hM ≤ (symmS M hM k).approx n := by
  intro n
  show recipWitness M (jdist M k) hM
      ≤ (((bdyRadical M hM (k + 1)).approx n + (bdyRadical M hM k).approx n)
          + ((nodeWeight M hM k).approx n + (nodeWeight M hM k).approx n))
  -- s_-.approx n ≥ recipWitness
  have hsm : recipWitness M (jdist M k) hM ≤ (bdyRadical M hM k).approx n := by
    rw [ChebOrthoRemainder.bdyRadical_interior M hM k hk0 hkn]
    show recipWitness M (jdist M k) hM
        ≤ (CReal.sqrtFrom (bdyOneMinusSq M k hM hk0 hkn) (SemicircleIntegral.nodeLB M hM)
            (ChebOrthoMidpoint.bdyOneMinusSq_pos hM hk0 hkn) (SemicircleIntegral.nodeLB_pos hM)
            (ChebOrthoMidpoint.bdyLB_sq_le hM hk0 hkn)).approx n
    rw [CReal.sqrtFrom_approx]
    exact CReal.heronSeq_lb (bdyOneMinusSq M k hM hk0 hkn) (recipWitness M (jdist M k) hM)
      (ChebOrthoMidpoint.bdyOneMinusSq_pos hM hk0 hkn)
      (recipWitness_pos M (jdist M k) hM hj)
      (recipWitness_sq_le M hM k hk0 hkn hj) n
  -- the other three are ≥ 0
  have hsp : (0 : Q') ≤ (bdyRadical M hM (k + 1)).approx n :=
    ChebOrthoInterior.bdyRadical_approx_nonneg M hM (k + 1) n
  have hnd : (0 : Q') ≤ (nodeWeight M hM k).approx n :=
    Q'.le_trans' _ _ _ (Q'.le_of_lt (SemicircleIntegral.nodeLB_pos hM))
      (ChebOrthoLeadingModel.nodeWeight_approx_ge M hM k hkn n)
  -- recipWitness ≤ (0 + recipWitness) + (0 + 0) ≤ S.approx n
  have hsum1 : recipWitness M (jdist M k) hM
      ≤ ((bdyRadical M hM (k + 1)).approx n + (bdyRadical M hM k).approx n) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv _))) ?_
    exact Q'.add_le_add hsp hsm
  have hsum2 : (0 : Q') ≤ ((nodeWeight M hM k).approx n + (nodeWeight M hM k).approx n) :=
    Q'.zero_le_add _ _ hnd hnd
  refine Q'.le_trans' _ _ _ hsum1 ?_
  exact Q'.add_le_self_of_nonneg _ _ hsum2

/-- **THE SYMMETRIC SECOND-DIFFERENCE BOUND (the outer division).**  For an interior
cell `0 < k`, `k+1 < M` with `2 ≤ jdist M k`,

    `|s_+ + s_- − 2 s_k| ≤ symmQuot`,
    `symmQuot = (2·subSecondQuot + 2δ²) · (1/recipWitness)`.

PROOF: `AbsLeRat.div_of_mul_ge` with the proved numerator bound `DS_AbsLeRat`
(`|D·S| ≤ 2·subSecondQuot + 2δ²`, via the product identity `(★)` + the √-cancellation),
the pointwise lower bound `symmS_lower` (`recipWitness ≤ S.approx n`,
`recipWitness > 0`), and the explicit quotient `K·(1/recipWitness)`.  Reciprocal-free. -/
theorem symmSecondDiff_AbsLeRat (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) (hj : 2 ≤ jdist M k) :
    AbsLeRat (symmD M hM k)
      (((subSecondQuot M k hM + subSecondQuot M k hM) + twoDeltaSq M hM)
        * Q'.recipPos (recipWitness M (jdist M k) hM) (recipWitness_pos M (jdist M k) hM hj)) := by
  -- abbreviate the numerator K and reciprocal R
  refine ChebOrthoCancelDiv.AbsLeRat.div_of_mul_ge
    (D := symmD M hM k) (S := symmS M hM k)
    (K := (subSecondQuot M k hM + subSecondQuot M k hM) + twoDeltaSq M hM)
    (L := recipWitness M (jdist M k) hM)
    (KL := ((subSecondQuot M k hM + subSecondQuot M k hM) + twoDeltaSq M hM)
        * Q'.recipPos (recipWitness M (jdist M k) hM) (recipWitness_pos M (jdist M k) hM hj))
    (DS_AbsLeRat M hM k hk0 hkn hk1n)
    (symmS_lower M hM k hk0 hkn hj)
    (recipWitness_pos M (jdist M k) hM hj)
    ?_ ?_
  · -- KL = K·(1/L) ≥ 0 :  product of nonnegatives
    have hKnn : (0 : Q') ≤ (subSecondQuot M k hM + subSecondQuot M k hM) + twoDeltaSq M hM :=
      Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (subSecondQuot_nonneg M k hM)
        (subSecondQuot_nonneg M k hM)) (twoDeltaSq_nonneg M hM)
    have hRnn : (0 : Q') ≤ Q'.recipPos (recipWitness M (jdist M k) hM)
        (recipWitness_pos M (jdist M k) hM hj) :=
      Q'.le_of_lt (Q'.recipPos_pos _ _)
    exact Q'.mul_nonneg _ _ hKnn hRnn
  · -- KL · L ≈ K :  (K·(1/L))·L ≈ K·((1/L)·L) ≈ K·1 ≈ K
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv ((subSecondQuot M k hM + subSecondQuot M k hM) + twoDeltaSq M hM)
        (Q'.recipPos (recipWitness M (jdist M k) hM) (recipWitness_pos M (jdist M k) hM hj))
        (recipWitness M (jdist M k) hM)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
          (Q'.mul_recipPos_eqv (recipWitness M (jdist M k) hM)
            (recipWitness_pos M (jdist M k) hM hj)))) ?_
    -- K · 1 ≈ K
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.one_mul_eqv _)

/-! ## 6. The `SymmSecondClose` inhabitant (the structural feed) -/

/-- **THE SYMMETRIC SECOND-DIFFERENCE GRADED CLOSE.**  Inhabit
`ChebOrthoRadSecondDiffSq.SymmSecondClose`: the proved √-cancellation
`subSecondDiff_AbsLeRat` fills `sub`; the explicit quotient
`symmQuot = (2·subSecondQuot + 2δ²)·(1/recipWitness)` and the assembled symmetric
second-difference bound `symmSecondDiff_AbsLeRat` fill `symmQuot`/`symm_bound`.  The
ONLY genuine analytic content (the √-Hölder `δ²`-cancellation) was already proved; this
inhabitant adds the rational product identity `(★)` + the outer reciprocal-free
division. -/
def symmSecondClose (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) (hj : 2 ≤ jdist M k) :
    ChebOrthoRadSecondDiffSq.SymmSecondClose M hM k hk0 hkn hk1n where
  sub := subSecondDiff_AbsLeRat M hM k hk0 hkn hk1n
  symmQuot := ((subSecondQuot M k hM + subSecondQuot M k hM) + twoDeltaSq M hM)
      * Q'.recipPos (recipWitness M (jdist M k) hM) (recipWitness_pos M (jdist M k) hM hj)
  symmQuot_nonneg := by
    refine Q'.mul_nonneg _ _ ?_ (Q'.le_of_lt (Q'.recipPos_pos _ _))
    exact Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (subSecondQuot_nonneg M k hM)
      (subSecondQuot_nonneg M k hM)) (twoDeltaSq_nonneg M hM)
  symm_bound := symmSecondDiff_AbsLeRat M hM k hk0 hkn hk1n hj

end YMGap.Continuum.ChebOrthoLegClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoLegClose.residueVal_eq
#print axioms YMGap.Continuum.ChebOrthoLegClose.DS_eq_E
#print axioms YMGap.Continuum.ChebOrthoLegClose.symmReorderProof
#print axioms YMGap.Continuum.ChebOrthoLegClose.symmE_sub_ring
#print axioms YMGap.Continuum.ChebOrthoLegClose.symmE_sub_eq_midReal
#print axioms YMGap.Continuum.ChebOrthoLegClose.midReal_collapse
#print axioms YMGap.Continuum.ChebOrthoLegClose.DS_collapse
#print axioms YMGap.Continuum.ChebOrthoLegClose.DS_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoLegClose.symmS_lower
#print axioms YMGap.Continuum.ChebOrthoLegClose.symmSecondDiff_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoLegClose.symmSecondClose
