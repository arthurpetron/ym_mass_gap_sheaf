/-
# Quaternion-block locality under head integration and lifting

The actual partial Haar map removes four leading exponents and changes
only the coefficient. The actual head lift prepends four zero exponents.
Thus neither operation creates dependence on a new remaining block.
These are syntactic locality statements, including zero coefficients and
the zero-block boundary case; no positivity or analytic input is used.
-/

import YMGap.Continuum.SU2QuaternionBlockLocality
import YMGap.Continuum.SU2QuaternionPartialFactorizedHaar

namespace YMGap.Continuum.SU2QuaternionBlockLocality

open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar

namespace BlockLocal

/-- Integrating the head preserves precisely the shifted allowed blocks. -/
theorem partialHaarHead {blocks : Nat} {allowed : Nat → Prop} {p : RatPoly}
    (hp : BlockLocal blocks allowed p) :
    BlockLocal (blocks - 1) (fun b => allowed (b + 1))
      (SU2QuaternionHaarHeadFubini.partialHaarHead p) := by
  intro t ht block hb hn component hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  change exponentAt (s.1.drop 4) (4 * block + component) = 0
  rw [exponentAt_drop,
    show 4 + (4 * block + component) = 4 * (block + 1) + component by omega]
  exact hp s hs (block + 1) (by omega) hn component hc

/-- Lifting inserts an independent head and shifts the existing locality.
No positive block-count hypothesis is needed. -/
theorem liftHead {blocks : Nat} {allowed : Nat → Prop} {r : RatPoly}
    (hr : BlockLocal (blocks - 1) allowed r) :
    BlockLocal blocks (fun b => 0 < b ∧ allowed (b - 1))
      (SU2QuaternionPartialFactorizedHaar.liftHead r) := by
  intro t ht block hb hn component hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  change exponentAt (0 :: 0 :: 0 :: 0 :: s.1) (4 * block + component) = 0
  cases block with
  | zero =>
      have hcomponent : component = 0 ∨ component = 1 ∨ component = 2 ∨ component = 3 := by
        omega
      rcases hcomponent with rfl | rfl | rfl | rfl <;> rfl
  | succ block =>
      rw [show 4 * (block + 1) + component = (4 * block + component) + 4 by omega]
      change exponentAt s.1 (4 * block + component) = 0
      have hnot : ¬ allowed block := by
        intro ha
        apply hn
        refine ⟨Nat.zero_lt_succ _, ?_⟩
        rw [show Nat.succ block - 1 = block by omega]
        exact ha
      exact hr s hs block (by omega) hnot component hc

end BlockLocal

end YMGap.Continuum.SU2QuaternionBlockLocality

#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.partialHaarHead
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.liftHead
