/-
# The sharp `(k+2)²` divided-difference secant bound — closing the `dd` field
# of `CosNodeResidual` down to the single exact-identity residual
# (`CosPiEnclosure`)

`CosNodeBracket.CosNodeResidual k` carries the `dd` field
`DDBound (Cheb.T (k+2)) lo hi (ofNat ((k+2)²))`, whose two-sided
term-by-term bound `−(k+2)² ≤ B ≤ (k+2)²` was believed to be deep
sharp-constant work.  It is not: it is elementary once the second-kind bound
`|U_j(x)| ≤ j+1` (`ChebU.absU_le`) is in hand.

## The load-bearing closed form

For the divided difference of `T_n` (`n = k+2`), the discrete
variation-of-parameters solution of the DD recurrence is the **polynomial
convolution** (here written in the reindexed form `j = n−2−m`):

    ddSecant k a b  =  U_{k+1}(b)  +  Σ_{j=0}^{k}  2·U_j(b)·T_{k+1−j}(a).

* Each summand is bounded `|2·U_j(b)·T_{k+1−j}(a)| ≤ 2·(j+1)` on `[−1,1]`, via
  the proved `|U_j| ≤ j+1` and `|T_m| ≤ 1`.
* The finite triangular count `Σ_{j=0}^{k} 2·(j+1) = (k+1)·(k+2)` then gives
  `|ddSecant| ≤ (k+2) + (k+1)·(k+2) = (k+2)²` — the hardcoded constant, EXACTLY.

## What is PROVED here (axiom-clean)

  * `absSum_le` — the finite-`Q'`-sum triangle inequality
    `|Σ f| ≤ Σ |f|` (reusable; the requested finite-sum wrapper, built off
    the two-term `TsumDeriv.abs_add_le`).
  * `absT_le_one` — `|T_m(x)| ≤ 1` on `[−1,1]` for every `m` (from
    `ChebU.Tabs_le_one`, plus the `m = 0` base).
  * `finSum_le_finSum` — pointwise monotonicity of `finSum` (reusable).
  * `ofNat_mul_eqv` / `count_id` — the triangular-sum count
    `Σ_{j<N} 2·(j+1) ≈ ofNat (N·(N+1))`.
  * `ddSecant_abs_le` — **the sharp two-sided bound**
    `|ddSecant k a b| ≤ ofNat ((k+2)²)` on the subbox `[−1,1]`, consuming
    `ChebU.absU_le` and the count.  This is the whole quantitative content of
    the `dd` field.
  * `ddBound_of_ddId` — from ONLY the exact DD polynomial identity
    (`ddId`), build a full `CosNodeBracket.DDBound (Cheb.T (k+2)) lo hi
    (ofNat ((k+2)²))`; the `Bub`/`Blb` fields are discharged by
    `ddSecant_abs_le`.
  * `cosNodeResidual_of_walls` / `deMoivreNode_of_walls` — assemble a
    `CosNodeResidual k` (hence a `DeMoivreNode (k+1)`) from `ddId` + the three
    sign walls + the interval rationals.

## The honest residual (NOT closed here)

The `dd` field is reduced to the SINGLE `Type`-level/propositional obligation
`ddId` — the exact divided-difference identity `T_n(b) − T_n(a) ≈ (b−a)·
ddSecant` — whose proof is the routine (but long) two-step `Q'`-`eqv`
induction off `Cheb.T_succ_succ`.  It is a genuine identity (verified `n =
1,2,3` by hand), so the residual is satisfiable, not a gaming hole.  The three
`π`-sign walls `loSign`/`hiSign`/`tsign` and the interval rationals remain
hypotheses (the `loSign`/`hiSign` uniform-in-`k` version is the genuine
rational-`π` `U`-sign wall).

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no
`sorry`/`sorryAx`, no `native_decide`, no custom axiom.  `DDBound` /
`CosNodeResidual` are `Type`-level records; `ddId` is a propositional
`eqv`-identity carried as a hypothesis, not an erased `Prop`-∃.
-/

import YMGap.Continuum.CosNodeBracket
import YMGap.Continuum.TsumDeriv
import YMGap.Constructive.RationalTail

namespace YMGap.Continuum.CosPiEnclosure

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Small numeric helper -/

/-- `0 ≤ ofNat n` for every `n`. -/
theorem ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

/-- `ofNat a · ofNat b ≈ ofNat (a·b)` (the multiplicative analogue of
`ChebU.ofNat_add_eqv`). -/
theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  show (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int)
      = (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
  rw [Q'.mul_den_cast]
  show ((Int.ofNat a) * (Int.ofNat b)) * 1
      = (Int.ofNat (a * b)) * (1 * 1)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  omega

/-! ## 1. The finite-`Q'`-sum triangle inequality (requested reusable atom) -/

/-- **Finite-sum triangle inequality**: `|Σ_{i<n} f i| ≤ Σ_{i<n} |f i|`.
Induction on `n` off `finSum_succ`, reusing the two-term
`TsumDeriv.abs_add_le`. -/
theorem absSum_le (f : QSeq) :
    ∀ n, Q'.abs (finSum f n) ≤ finSum (fun i => Q'.abs (f i)) n
  | 0 => by
      show Q'.abs (0 : Q') ≤ (0 : Q')
      exact Q'.abs_le (by decide) (by decide)
  | n + 1 => by
      show Q'.abs (finSum f n + f n)
          ≤ finSum (fun i => Q'.abs (f i)) n + Q'.abs (f n)
      refine Q'.le_trans' _ _ _ (TsumDeriv.abs_add_le (finSum f n) (f n)) ?_
      exact Q'.add_le_add_right _ _ _ (absSum_le f n)

/-- **Pointwise monotonicity of `finSum`**: `(∀ i, f i ≤ g i) → Σ f ≤ Σ g`. -/
theorem finSum_le_finSum (f g : QSeq) (h : ∀ i, f i ≤ g i) :
    ∀ n, finSum f n ≤ finSum g n
  | 0 => by
      show (0 : Q') ≤ (0 : Q')
      exact Q'.le_refl' 0
  | n + 1 => by
      show finSum f n + f n ≤ finSum g n + g n
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (finSum_le_finSum f g h n)) ?_
      exact Q'.add_le_add_left _ _ _ (h n)

/-! ## 2. `|T_m(x)| ≤ 1` on `[−1,1]` for every `m` -/

/-- `|T_m(x)| ≤ 1` on `[−1,1]`, all `m` (from `ChebU.Tabs_le_one`, base
`T₀ = 1`). -/
theorem absT_le_one (m : Nat) (a : Q') (ha1 : a ≤ (1 : Q')) (ham1 : (-(1 : Q')) ≤ a) :
    Q'.abs (Cheb.T m a) ≤ (1 : Q') := by
  cases m with
  | zero =>
      show Q'.abs (Cheb.T 0 a) ≤ (1 : Q')
      have h0 : Cheb.T 0 a = (1 : Q') := rfl
      rw [h0]
      exact Q'.abs_le (by decide) (by decide)
  | succ p =>
      obtain ⟨hlb, hub⟩ := ChebU.Tabs_le_one p a ha1 ham1
      exact Q'.abs_le hlb hub

/-! ## 3. The closed-form secant and the per-term / count bounds -/

/-- The per-term bound sequence `c j = 2·ofNat (j+1)`. -/
def cseq : QSeq := fun j => (2 : Q') * Q'.ofNat (j + 1)

/-- The secant's summand sequence `g j = 2·(U_j(b)·T_{k+1−j}(a))`. -/
def gseq (k : Nat) (a b : Q') : QSeq :=
  fun j => (2 : Q') * (Cheb.U j b * Cheb.T (k + 1 - j) a)

/-- **The closed-form divided-difference secant** for `T_{k+2}` on `[lo,hi]`:
`ddSecant k a b = U_{k+1}(b) + Σ_{j=0}^{k} 2·U_j(b)·T_{k+1−j}(a)`. -/
def ddSecant (k : Nat) (a b : Q') : Q' :=
  Cheb.U (k + 1) b + finSum (gseq k a b) (k + 1)

/-- **Per-term bound** `|g j| ≤ c j` on `[−1,1]`. -/
theorem gseq_abs_le (k : Nat) (a b : Q')
    (ha1 : a ≤ (1 : Q')) (ham1 : (-(1 : Q')) ≤ a)
    (hb1 : b ≤ (1 : Q')) (hbm1 : (-(1 : Q')) ≤ b) (j : Nat) :
    Q'.abs (gseq k a b j) ≤ cseq j := by
  show Q'.abs ((2 : Q') * (Cheb.U j b * Cheb.T (k + 1 - j) a))
      ≤ (2 : Q') * Q'.ofNat (j + 1)
  -- |U_j(b)| ≤ ofNat (j+1)
  have habsU : Q'.abs (Cheb.U j b) ≤ Q'.ofNat (j + 1) := by
    obtain ⟨hub, hlb⟩ := ChebU.absU_le j b hb1 hbm1
    exact Q'.abs_le hlb hub
  -- |T_{k+1-j}(a)| ≤ 1
  have habsT : Q'.abs (Cheb.T (k + 1 - j) a) ≤ (1 : Q') := absT_le_one (k + 1 - j) a ha1 ham1
  -- |U_j(b)·T_{..}(a)| ≤ ofNat (j+1)
  have habsW : Q'.abs (Cheb.U j b * Cheb.T (k + 1 - j) a) ≤ Q'.ofNat (j + 1) := by
    refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le _ _) ?_
    have h1 : Q'.abs (Cheb.U j b) * Q'.abs (Cheb.T (k + 1 - j) a)
        ≤ Q'.ofNat (j + 1) * Q'.abs (Cheb.T (k + 1 - j) a) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ habsU (Q'.abs_nonneg _)
    have h2 : Q'.ofNat (j + 1) * Q'.abs (Cheb.T (k + 1 - j) a)
        ≤ Q'.ofNat (j + 1) * (1 : Q') :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ habsT (ofNat_nonneg _)
    have h3 : Q'.ofNat (j + 1) * (1 : Q') ≤ Q'.ofNat (j + 1) :=
      Q'.le_of_eqv (Q'.mul_one_eqv _)
    exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 h3)
  -- |2·w| ≤ 2·|w| ≤ 2·ofNat (j+1)
  have habs2 : Q'.abs (2 : Q') = (2 : Q') := by
    unfold Q'.abs
    rw [if_pos (show (0 : Q') ≤ (2 : Q') from by decide)]
  refine Q'.le_trans' _ _ _
    (TsumDeriv.Q'.abs_mul_le (2 : Q') (Cheb.U j b * Cheb.T (k + 1 - j) a)) ?_
  rw [habs2]
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ habsW (by decide)

/-- **The triangular count** `Σ_{j<N} 2·(j+1) ≈ ofNat (N·(N+1))`. -/
theorem count_id : ∀ N, finSum cseq N ≈ Q'.ofNat (N * (N + 1))
  | 0 => by decide
  | N + 1 => by
      show finSum cseq N + cseq N ≈ Q'.ofNat ((N + 1) * ((N + 1) + 1))
      -- cseq N = 2·ofNat (N+1) ≈ ofNat (2·(N+1))
      have hcN : cseq N ≈ Q'.ofNat (2 * (N + 1)) := by
        show (2 : Q') * Q'.ofNat (N + 1) ≈ Q'.ofNat (2 * (N + 1))
        rw [ChebU.two_eq_ofNat]
        exact ofNat_mul_eqv 2 (N + 1)
      have ih := count_id N
      have hsum : finSum cseq N + cseq N
          ≈ Q'.ofNat (N * (N + 1)) + Q'.ofNat (2 * (N + 1)) :=
        Cheb.add_eqv_congr _ _ _ _ ih hcN
      have hadd : Q'.ofNat (N * (N + 1)) + Q'.ofNat (2 * (N + 1))
          ≈ Q'.ofNat (N * (N + 1) + 2 * (N + 1)) :=
        ChebU.ofNat_add_eqv (N * (N + 1)) (2 * (N + 1))
      have hnat : N * (N + 1) + 2 * (N + 1) = (N + 1) * ((N + 1) + 1) := by
        have e : (N + 1) * ((N + 1) + 1) = (N + 1) * (N + 1) + (N + 1) :=
          Nat.mul_succ (N + 1) (N + 1)
        have e2 : (N + 1) * (N + 1) = N * (N + 1) + (N + 1) :=
          Nat.succ_mul N (N + 1)
        rw [e, e2]
        omega
      refine Q'.eqv_trans _ _ _ hsum ?_
      refine Q'.eqv_trans _ _ _ hadd ?_
      rw [hnat]
      exact Q'.eqv_refl _

/-! ## 4. The sharp two-sided secant bound (the whole `dd` quantitative core) -/

/-- **The sharp bound** `|ddSecant k a b| ≤ ofNat ((k+2)²)` on `[−1,1]`.
Consumes `ChebU.absU_le` (via the per-term bound) and the triangular count. -/
theorem ddSecant_abs_le (k : Nat) (a b : Q')
    (ha1 : a ≤ (1 : Q')) (ham1 : (-(1 : Q')) ≤ a)
    (hb1 : b ≤ (1 : Q')) (hbm1 : (-(1 : Q')) ≤ b) :
    Q'.abs (ddSecant k a b) ≤ Q'.ofNat ((k + 2) ^ 2) := by
  show Q'.abs (Cheb.U (k + 1) b + finSum (gseq k a b) (k + 1))
      ≤ Q'.ofNat ((k + 2) ^ 2)
  -- |U + Σg| ≤ |U| + |Σg|
  have hsplit := TsumDeriv.abs_add_le (Cheb.U (k + 1) b) (finSum (gseq k a b) (k + 1))
  -- |U_{k+1}(b)| ≤ ofNat (k+2)
  have hU : Q'.abs (Cheb.U (k + 1) b) ≤ Q'.ofNat (k + 2) := by
    obtain ⟨hub, hlb⟩ := ChebU.absU_le (k + 1) b hb1 hbm1
    exact Q'.abs_le hlb hub
  -- |Σg| ≤ Σ|g| ≤ Σc
  have hFS : Q'.abs (finSum (gseq k a b) (k + 1)) ≤ finSum cseq (k + 1) := by
    refine Q'.le_trans' _ _ _ (absSum_le (gseq k a b) (k + 1)) ?_
    exact finSum_le_finSum (fun i => Q'.abs (gseq k a b i)) cseq
      (fun i => gseq_abs_le k a b ha1 ham1 hb1 hbm1 i) (k + 1)
  have hcombined :
      Q'.abs (Cheb.U (k + 1) b) + Q'.abs (finSum (gseq k a b) (k + 1))
        ≤ Q'.ofNat (k + 2) + finSum cseq (k + 1) :=
    ChebU.add_le_add _ _ _ _ hU hFS
  -- Σc ≈ ofNat ((k+1)·(k+2))
  have hcount : finSum cseq (k + 1) ≈ Q'.ofNat ((k + 1) * ((k + 1) + 1)) :=
    count_id (k + 1)
  have hR : Q'.ofNat (k + 2) + finSum cseq (k + 1)
      ≈ Q'.ofNat (k + 2) + Q'.ofNat ((k + 1) * ((k + 1) + 1)) :=
    Q'.add_eqv_congr_left _ _ _ hcount
  have hAdd : Q'.ofNat (k + 2) + Q'.ofNat ((k + 1) * ((k + 1) + 1))
      ≈ Q'.ofNat ((k + 2) + (k + 1) * ((k + 1) + 1)) :=
    ChebU.ofNat_add_eqv (k + 2) ((k + 1) * ((k + 1) + 1))
  -- (k+2) + (k+1)·(k+2) = (k+2)²
  have hFinNat : (k + 2) + (k + 1) * ((k + 1) + 1) = (k + 2) ^ 2 := by
    have e1 : (k + 1) + 1 = k + 2 := rfl
    rw [e1]
    have hp : (k + 2) ^ 2 = (k + 2) * (k + 2) := by rw [Nat.pow_succ, Nat.pow_one]
    have hmul : (k + 2) * (k + 2) = (k + 1) * (k + 2) + (k + 2) :=
      Nat.succ_mul (k + 1) (k + 2)
    rw [hp, hmul]
    omega
  -- assemble
  refine Q'.le_trans' _ _ _ hsplit ?_
  refine Q'.le_trans' _ _ _ hcombined ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _ hR ?_
  refine Q'.eqv_trans _ _ _ hAdd ?_
  rw [hFinNat]
  exact Q'.eqv_refl _

/-! ## 5. The `DDBound` producer (reduces the whole `dd` field to `ddId`) -/

/-- **From the exact DD identity alone, a full `DDBound`.**  `Bub`/`Blb` are
discharged by the proved `ddSecant_abs_le`; only the exact identity `ddId`
(`T_{k+2}(b) − T_{k+2}(a) ≈ (b−a)·ddSecant`) is supplied externally. -/
def ddBound_of_ddId (k : Nat) (lo hi : Q')
    (hlo1 : (-(1 : Q')) ≤ lo) (hhi1 : hi ≤ (1 : Q'))
    (ddId : ∀ a b : Q', lo ≤ a → a ≤ b → b ≤ hi →
        Cheb.T (k + 2) b + -(Cheb.T (k + 2) a) ≈ (b + -a) * ddSecant k a b) :
    CosNodeBracket.DDBound (Cheb.T (k + 2)) lo hi (Q'.ofNat ((k + 2) ^ 2)) where
  B := ddSecant k
  Cnn := ofNat_nonneg _
  ddId := ddId
  Bub := by
    intro a b ha hab hb
    have ha1 : a ≤ (1 : Q') := Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hab hb) hhi1
    have ham1 : (-(1 : Q')) ≤ a := Q'.le_trans' _ _ _ hlo1 ha
    have hbb1 : b ≤ (1 : Q') := Q'.le_trans' _ _ _ hb hhi1
    have hbm1 : (-(1 : Q')) ≤ b :=
      Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hlo1 ha) hab
    have habs := ddSecant_abs_le k a b ha1 ham1 hbb1 hbm1
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self _) habs
  Blb := by
    intro a b ha hab hb
    have ha1 : a ≤ (1 : Q') := Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hab hb) hhi1
    have ham1 : (-(1 : Q')) ≤ a := Q'.le_trans' _ _ _ hlo1 ha
    have hbb1 : b ≤ (1 : Q') := Q'.le_trans' _ _ _ hb hhi1
    have hbm1 : (-(1 : Q')) ≤ b :=
      Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hlo1 ha) hab
    have habs := ddSecant_abs_le k a b ha1 ham1 hbb1 hbm1
    have h1 : -(ddSecant k a b) ≤ Q'.ofNat ((k + 2) ^ 2) :=
      Q'.le_trans' _ _ _ (Q'.neg_le_abs _) habs
    have h2 := Q'.neg_le_neg h1
    exact Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.neg_neg_eqv _))

/-! ## 6. The `CosNodeResidual` / `DeMoivreNode` assembly -/

/-- **Assembly**: a full `CosNodeResidual k` from `ddId` + the three sign walls
+ the interval rationals.  The `dd` field is `ddBound_of_ddId`. -/
def cosNodeResidual_of_walls (k : Nat) (lo hi : Q')
    (hlo1 : (-(1 : Q')) ≤ lo) (hhi1 : hi ≤ (1 : Q')) (hle : lo ≤ hi)
    (ddId : ∀ a b : Q', lo ≤ a → a ≤ b → b ≤ hi →
        Cheb.T (k + 2) b + -(Cheb.T (k + 2) a) ≈ (b + -a) * ddSecant k a b)
    (loSign : ChebRoot.Ueval (k + 1) lo ≤ (0 : Q'))
    (hiSign : (0 : Q') ≤ ChebRoot.Ueval (k + 1) hi)
    (tsign : Cheb.T (k + 2) hi + Q'.ofNat ((k + 2) ^ 2) * (hi + -lo) ≤ (0 : Q')) :
    CosNodeBracket.CosNodeResidual k where
  lo := lo
  hi := hi
  hlo1 := hlo1
  hhi1 := hhi1
  hle := hle
  dd := ddBound_of_ddId k lo hi hlo1 hhi1 ddId
  loSign := loSign
  hiSign := hiSign
  tsign := tsign

/-- A fully inhabited `DeMoivreNode (k+1)` from `ddId` + the sign walls
(general-`M` off-diagonal OS2 Gram positivity downstream), conditional ONLY on
the exact DD identity and the three `π`-sign walls. -/
def deMoivreNode_of_walls (k : Nat) (lo hi : Q')
    (hlo1 : (-(1 : Q')) ≤ lo) (hhi1 : hi ≤ (1 : Q')) (hle : lo ≤ hi)
    (ddId : ∀ a b : Q', lo ≤ a → a ≤ b → b ≤ hi →
        Cheb.T (k + 2) b + -(Cheb.T (k + 2) a) ≈ (b + -a) * ddSecant k a b)
    (loSign : ChebRoot.Ueval (k + 1) lo ≤ (0 : Q'))
    (hiSign : (0 : Q') ≤ ChebRoot.Ueval (k + 1) hi)
    (tsign : Cheb.T (k + 2) hi + Q'.ofNat ((k + 2) ^ 2) * (hi + -lo) ≤ (0 : Q')) :
    ChebRotationPair.DeMoivreNode (k + 1) :=
  CosNodeBracket.deMoivreNode_of_residual k
    (cosNodeResidual_of_walls k lo hi hlo1 hhi1 hle ddId loSign hiSign tsign)

end YMGap.Continuum.CosPiEnclosure

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CosPiEnclosure.absSum_le
#print axioms YMGap.Continuum.CosPiEnclosure.finSum_le_finSum
#print axioms YMGap.Continuum.CosPiEnclosure.absT_le_one
#print axioms YMGap.Continuum.CosPiEnclosure.ofNat_mul_eqv
#print axioms YMGap.Continuum.CosPiEnclosure.count_id
#print axioms YMGap.Continuum.CosPiEnclosure.gseq_abs_le
#print axioms YMGap.Continuum.CosPiEnclosure.ddSecant_abs_le
#print axioms YMGap.Continuum.CosPiEnclosure.ddBound_of_ddId
#print axioms YMGap.Continuum.CosPiEnclosure.cosNodeResidual_of_walls
#print axioms YMGap.Continuum.CosPiEnclosure.deMoivreNode_of_walls
