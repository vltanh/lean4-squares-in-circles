module
public import SquaresInCircles.Six.Stress.PairLocal

@[expose] public section

/-!
# A common global adjacent-pair lower envelope

This theorem covers all four central-bit choices and all four genuine source
axes. The finite outer cover and the analytic six-sector local proof meet on
closed boundaries. Equality-compatible sources are distinguished from the two
strict alternatives without assuming a preferred source in the packing.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open ProofTools PairCertificate

lemma pair_root_mem {n w : ℝ} (hn : -3/10≤n ∧ n≤5/12)
    (hw : -11/25≤w ∧ w≤2/5) : PairCertificate.root.Mem ![n,w] := by
  intro i
  fin_cases i
  · exact hn
  · exact hw

/-- The common envelope used by both N/W and the reflected E/S pair. -/
theorem pair_lower_bound (no wo : Bool) (u : Fin 4) {n w : ℝ}
    (hn : -3/10≤n ∧ n≤5/12) (hw : -11/25≤w ∧ w≤2/5) :
    pairBase+pairLine w+(1/1000)*|n|≤pairValue no wo u n w := by
  have hroot := pair_root_mem hn hw
  have hcheck := certify_sound (outerClaim no wo u) (fun _ => 1) 0 96
    (outer_checked no wo u) hroot
  by_cases hcan : u=0 ∨ u=3
  · have h : (|n|≤1/128 ∧ |w|≤1/128) ∨
        0<pairValue no wo u n w-pairBase-pairLine w-(1/1000)*|n| := by
      simpa only [outerClaim,if_pos hcan,localSquare,Formula.Holds,Expr.denote,
        denote_gapE] using hcheck
    rcases h with hlocal | hstrict
    · rcases hcan with rfl | rfl
      · exact local_pair_lower no wo 0 hlocal.1 hlocal.2
      · exact local_pair_lower no wo 1 hlocal.1 hlocal.2
    · linarith
  · have h : 0<pairValue no wo u n w-pairBase-pairLine w-(1/1000)*|n| := by
      simpa only [outerClaim,if_neg hcan,Formula.Holds,Expr.denote,denote_gapE] using hcheck
    linarith

/-- The two alternative sources have a strict reserve on the entire rectangle. -/
theorem pair_lower_bound_strict (no wo : Bool) {u : Fin 4} (hu : u≠0 ∧ u≠3)
    {n w : ℝ} (hn : -3/10≤n ∧ n≤5/12) (hw : -11/25≤w ∧ w≤2/5) :
    pairBase+pairLine w+(1/1000)*|n|<pairValue no wo u n w := by
  have hroot := pair_root_mem hn hw
  have hcheck := certify_sound (outerClaim no wo u) (fun _ => 1) 0 96
    (outer_checked no wo u) hroot
  have hcan : ¬ (u=0 ∨ u=3) := by tauto
  have h : 0<pairValue no wo u n w-pairBase-pairLine w-(1/1000)*|n| := by
    simpa only [outerClaim,if_neg hcan,Formula.Holds,Expr.denote,denote_gapE] using hcheck
  linarith

lemma pair_zero_equality_sources (no wo : Bool) (u : Fin 4)
    (heq : pairValue no wo u 0 0=pairBase) : u=0 ∨ u=3 := by
  by_contra h
  have hs := pair_lower_bound_strict no wo (u := u) (by tauto)
    (n := (0:ℝ)) (w := (0:ℝ)) (by norm_num) (by norm_num)
  simp only [pairLine_zero,abs_zero,mul_zero,add_zero,heq] at hs
  exact lt_irrefl _ hs

end SquaresInCircles.Six.Stress
