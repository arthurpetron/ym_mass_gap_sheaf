/-
# Cleared rational covariance response to an insertion

The difference of the two partition-cleared covariance numerators is the
inserted mass times the third connected numerator, minus the product of
the two probe-insertion covariance numerators. Both endpoint partitions
and every signed term remain explicit.

This is a polynomial identity for arbitrary rational inputs, not a decay
estimate or a positivity statement. Its intended consumer substitutes
moments from the same original action before estimating connected terms.
-/

import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RationalConnectedResponse

set_option autoImplicit false

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

/-- Cleared covariance response equals inserted mass times the third
connected numerator minus the product of the two insertion covariances. -/
theorem connected_response_identity (z a b r ab ar br abr : Q') :
    ((abr * r + -(ar * br)) * (z * z) + -((ab * z + -(a * b)) * (r * r))) ≈
      r * (abr * (z * z) + -(ab * r * z) + -(ar * b * z) + -(br * a * z) +
        2 * a * b * r) + -((ar * z + -(a * r)) * (br * z + -(b * r))) :=
  RingNormaliser.poly_identity_of_normal_eq
    (.add
      (.mul (.add (.mul (.var 7) (.var 3)) (.neg (.mul (.var 5) (.var 6))))
        (.mul (.var 0) (.var 0)))
      (.neg (.mul (.add (.mul (.var 4) (.var 0)) (.neg (.mul (.var 1) (.var 2))))
        (.mul (.var 3) (.var 3)))))
    (.add
      (.mul (.var 3)
        (.add
          (.add
            (.add
              (.add (.mul (.var 7) (.mul (.var 0) (.var 0)))
                (.neg (.mul (.mul (.var 4) (.var 3)) (.var 0))))
              (.neg (.mul (.mul (.var 5) (.var 2)) (.var 0))))
            (.neg (.mul (.mul (.var 6) (.var 1)) (.var 0))))
          (.mul (.mul (.mul (.const 2) (.var 1)) (.var 2)) (.var 3))))
      (.neg (.mul
        (.add (.mul (.var 5) (.var 0)) (.neg (.mul (.var 1) (.var 3))))
        (.add (.mul (.var 6) (.var 0)) (.neg (.mul (.var 2) (.var 3)))))))
    (by decide) (fun | 0 => z | 1 => a | 2 => b | 3 => r | 4 => ab | 5 => ar | 6 => br | _ => abr)

/-- Clear the partition square using the supplied SAME reciprocal equality. -/
theorem covariance_clear (z a b ab s : Q') (hz : z * s ≈ 1) :
    (ab * s + -((a * s) * (b * s))) * (z * z) ≈ ab * z + -(a * b) := by
  have hfactor : (ab * s + -((a * s) * (b * s))) * (z * z) ≈
      (ab * z + -((a * b) * (z * s))) * (z * s) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.add (.mul (.var 3) (.var 4))
        (.neg (.mul (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 4)))))
        (.mul (.var 0) (.var 0)))
      (.mul (.add (.mul (.var 3) (.var 0))
        (.neg (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 4)))))
        (.mul (.var 0) (.var 4)))
      (by decide) (fun | 0 => z | 1 => a | 2 => b | 3 => ab | _ => s)
  have houter : (ab * z + -((a * b) * (z * s))) * (z * s) ≈
      ab * z + -((a * b) * (z * s)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_one_eqv _)
  have hinner : (a * b) * (z * s) ≈ a * b :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_one_eqv _)
  exact Q'.eqv_trans _ _ _ hfactor (Q'.eqv_trans _ _ _ houter
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hinner)))

/-- Clear a difference using its two existing endpoint equalities. -/
theorem difference_clear (A B C D X Y : Q')
    (hA : A * X ≈ C) (hB : B * Y ≈ D) :
    (A + -B) * (X * Y) ≈ C * Y + -(D * X) := by
  have hfactor : (A + -B) * (X * Y) ≈ (A * X) * Y + -((B * Y) * X) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.neg (.var 1))) (.mul (.var 2) (.var 3)))
      (.add (.mul (.mul (.var 0) (.var 2)) (.var 3))
        (.neg (.mul (.mul (.var 1) (.var 3)) (.var 2))))
      (by decide) (fun | 0 => A | 1 => B | 2 => X | _ => Y)
  exact Q'.eqv_trans _ _ _ hfactor
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ _ hA))
      (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ hB))))

end YMGap.Continuum.RationalConnectedResponse

#print axioms YMGap.Continuum.RationalConnectedResponse.connected_response_identity
#print axioms YMGap.Continuum.RationalConnectedResponse.covariance_clear
#print axioms YMGap.Continuum.RationalConnectedResponse.difference_clear
