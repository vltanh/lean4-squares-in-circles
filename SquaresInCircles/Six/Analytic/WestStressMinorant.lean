import SquaresInCircles.Six.Analytic.EndpointReduction
import SquaresInCircles.Six.Analytic.OwnAxisWindows

/-!
# A minorant for the west stress

The function `westMinorant K L t u`, a constant plus `(3/10) cos u + L sin u`,
`(3483/20000) cos t + K sin t` and `(cos (u - t) + sin (u - t))/4`, is positive
on the parts `t ≤ u ≤ 0`, `t ≤ 0 ≤ u` and `0 ≤ t ≤ u` of the domain
`-2/3 ≤ t ≤ u`, `-2/5 ≤ u ≤ 2/5`, with the coefficients `K` and `L` that the
signs of `sin t` and `sin u` select there. In `t`, in `u` and along the diagonal
`t = u` it has the form `C + A cos x + B sin x` with `A ≥ 0` and `B sin x ≥ 0`,
which is concave, so it is positive once it is at the seven vertices of the
three parts; there Taylor bounds of `sin` and `cos` at rational angles prove it.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

private def cW : ℝ := -3611073/5000000
private def aW : ℝ := 3483/20000
private def kNeg : ℝ := 19759/400000
private def kPos : ℝ := 179419/400000

def westMinorant (K L t u : ℝ) : ℝ :=
  cW+(3/10)*Real.cos u+L*Real.sin u+aW*Real.cos t+K*Real.sin t+
    (1/4)*(Real.cos (u-t)+Real.sin (u-t))

lemma westMinorant_in_t (K L t u : ℝ) : westMinorant K L t u =
    (cW+(3/10)*Real.cos u+L*Real.sin u)+
      (aW+(Real.cos u+Real.sin u)/4)*Real.cos t+
      (K+(Real.sin u-Real.cos u)/4)*Real.sin t := by
  dsimp [westMinorant]
  rw [Real.cos_sub,Real.sin_sub]
  ring

lemma westMinorant_in_u (K L t u : ℝ) : westMinorant K L t u =
    (cW+aW*Real.cos t+K*Real.sin t)+
      (3/10+(Real.cos t-Real.sin t)/4)*Real.cos u+
      (L+(Real.sin t+Real.cos t)/4)*Real.sin u := by
  dsimp [westMinorant]
  rw [Real.cos_sub,Real.sin_sub]
  ring

lemma westMinorant_diagonal (K L u : ℝ) : westMinorant K L u u =
    (cW+1/4)+(3/10+aW)*Real.cos u+(K+L)*Real.sin u := by
  simp only [westMinorant,sub_self,Real.cos_zero,Real.sin_zero]
  ring

private lemma trig_positive {C A B l u x:ℝ}
    (hA:0≤A) (hB:0≤B) (hl:0≤l) (hu:u≤Real.pi/2) (hx:l≤x ∧ x≤u)
    (hleft:0<C+A*Real.cos l+B*Real.sin l)
    (hright:0<C+A*Real.cos u+B*Real.sin u) :
    0<C+A*Real.cos x+B*Real.sin x := by
  have h := trig_lower_of_endpoints hA hB hl hu hx
    (show -C<A*Real.cos l+B*Real.sin l by linarith)
    (show -C<A*Real.cos u+B*Real.sin u by linarith)
  linarith

private lemma trig_positive_negative {C A B l u x:ℝ}
    (hA:0≤A) (hB:B≤0) (hl:-Real.pi/2≤l) (hu:u≤0) (hx:l≤x ∧ x≤u)
    (hleft:0<C+A*Real.cos l+B*Real.sin l)
    (hright:0<C+A*Real.cos u+B*Real.sin u) :
    0<C+A*Real.cos x+B*Real.sin x := by
  have h := trig_positive (C:=C) (A:=A) (B:=-B)
    (l:=-u) (u:=-l) (x:=-x) hA (by linarith) (by linarith) (by linarith)
    ⟨by linarith [hx.2],by linarith [hx.1]⟩
    (by simpa only [Real.cos_neg,Real.sin_neg,neg_mul_neg] using hright)
    (by simpa only [Real.cos_neg,Real.sin_neg,neg_mul_neg] using hleft)
  simpa only [Real.cos_neg,Real.sin_neg,neg_mul_neg] using h

/-- The minorant is positive at the seven vertices. -/
private lemma vertex_bounds :
    0<westMinorant kNeg (-3/10) (-2/3) (-2/5) ∧
    0<westMinorant kNeg (-3/10) (-2/5) (-2/5) ∧
    0<westMinorant kNeg 0 (-2/3) 0 ∧
    0<westMinorant kNeg 0 0 0 ∧
    0<westMinorant kNeg 0 (-2/3) (2/5) ∧
    0<westMinorant kPos 0 0 (2/5) ∧
    0<westMinorant kPos 0 (2/5) (2/5) := by
  have c23 := Seven.cos_lower_six (x:=(2:ℝ)/3) (by norm_num)
  have s23 := Seven.sin_lower_seven (x:=(2:ℝ)/3) (by norm_num)
  have u23 := Seven.sin_upper_five (x:=(2:ℝ)/3) (by norm_num)
  have c25 := Seven.cos_lower_six (x:=(2:ℝ)/5) (by norm_num)
  have s25 := Seven.sin_lower_seven (x:=(2:ℝ)/5) (by norm_num)
  have u25 := Seven.sin_upper_five (x:=(2:ℝ)/5) (by norm_num)
  have c415 := Seven.cos_lower_six (x:=(4:ℝ)/15) (by norm_num)
  have s415 := Seven.sin_lower_seven (x:=(4:ℝ)/15) (by norm_num)
  have c1615 := Seven.cos_lower_six (x:=(16:ℝ)/15) (by norm_num)
  have s1615 := Seven.sin_lower_seven (x:=(16:ℝ)/15) (by norm_num)
  norm_num at c23 s23 u23 c25 s25 u25 c415 s415 c1615 s1615
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    norm_num [westMinorant,cW,aW,kNeg,kPos,Real.cos_neg,Real.sin_neg]
  all_goals linarith

private lemma small_u {u:ℝ} (hu:-2/5≤u ∧ u≤2/5) :
    23/25≤Real.cos u ∧ -2/5≤Real.sin u ∧ Real.sin u≤2/5 := by
  have habs : |u|≤2/5 := abs_le.mpr ⟨by linarith [hu.1],hu.2⟩
  have hs : |Real.sin u|≤2/5 := by
    have h := Real.abs_sin_sub_sin_le u 0
    simp only [Real.sin_zero,sub_zero] at h
    exact h.trans habs
  have hsq := pow_le_pow_left₀ (abs_nonneg u) habs 2
  rw [sq_abs] at hsq
  refine ⟨?_,by linarith [(abs_le.mp hs).1],(abs_le.mp hs).2⟩
  nlinarith [Real.one_sub_sq_div_two_le_cos (x:=u)]

private lemma t_coefficients {u:ℝ} (hu:-2/5≤u ∧ u≤2/5) :
    0≤aW+(Real.cos u+Real.sin u)/4 ∧
      kNeg+(Real.sin u-Real.cos u)/4≤0 ∧
      0≤kPos+(Real.sin u-Real.cos u)/4 := by
  have h := small_u hu
  dsimp [aW,kNeg,kPos]
  exact ⟨by linarith [h.1,h.2.1],by linarith [h.1,h.2.2],
    by linarith [h.2.1,Real.cos_le_one u]⟩

private lemma far_coefficients :
    0≤3/10+(Real.cos (-2/3)-Real.sin (-2/3))/4 ∧
      -3/10+(Real.sin (-2/3)+Real.cos (-2/3))/4≤0 ∧
      0≤(Real.sin (-2/3)+Real.cos (-2/3))/4 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x:=(2:ℝ)/3)
  have hs := Real.sin_le (show (0:ℝ)≤2/3 by norm_num)
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi
    (show (0:ℝ)≤2/3 by norm_num) (show (2:ℝ)/3≤Real.pi by linarith [Real.pi_gt_d2])
  rw [show (-2:ℝ)/3=-(2/3) by norm_num,Real.cos_neg,Real.sin_neg]
  refine ⟨?_,?_,?_⟩ <;> nlinarith [Real.cos_le_one ((2:ℝ)/3)]

private lemma far_negative {u:ℝ} (hu:-2/5≤u ∧ u≤0) :
    0<westMinorant kNeg (-3/10) (-2/3) u := by
  have he0 := vertex_bounds.1
  have he1 := vertex_bounds.2.2.1
  have he1' : 0<westMinorant kNeg (-3/10) (-2/3) 0 := by
    simpa only [westMinorant,Real.sin_zero,mul_zero] using he1
  rw [westMinorant_in_u] at he0 he1' ⊢
  exact trig_positive_negative far_coefficients.1 far_coefficients.2.1
    (by linarith [Real.pi_gt_d2]) (by norm_num) hu he0 he1'

private lemma far_positive {u:ℝ} (hu:0≤u ∧ u≤2/5) :
    0<westMinorant kNeg 0 (-2/3) u := by
  have he0 := vertex_bounds.2.2.1
  have he1 := vertex_bounds.2.2.2.2.1
  rw [westMinorant_in_u] at he0 he1 ⊢
  exact trig_positive far_coefficients.1 (by simpa using far_coefficients.2.2)
    (by norm_num) (by linarith [Real.pi_gt_d2]) hu he0 he1

private lemma zero_edge {K u:ℝ} (hu:0≤u ∧ u≤2/5) :
    0<westMinorant K 0 0 u := by
  have he0 := vertex_bounds.2.2.2.1
  have he1 := vertex_bounds.2.2.2.2.2.1
  have he0' : 0<westMinorant K 0 0 0 := by
    simpa only [westMinorant,Real.sin_zero,mul_zero] using he0
  have he1' : 0<westMinorant K 0 0 (2/5) := by
    simpa only [westMinorant,Real.sin_zero,mul_zero] using he1
  rw [westMinorant_in_u] at he0' he1' ⊢
  exact trig_positive (by norm_num) (by norm_num)
    (by norm_num) (by linarith [Real.pi_gt_d2]) hu he0' he1'

private lemma negative_diagonal {u:ℝ} (hu:-2/5≤u ∧ u≤0) :
    0<westMinorant kNeg (-3/10) u u := by
  have he0 := vertex_bounds.2.1
  have he1 := vertex_bounds.2.2.2.1
  have he1' : 0<westMinorant kNeg (-3/10) 0 0 := by
    simpa only [westMinorant,Real.sin_zero,mul_zero] using he1
  rw [westMinorant_diagonal] at he0 he1' ⊢
  exact trig_positive_negative (by norm_num [aW]) (by norm_num [kNeg])
    (by linarith [Real.pi_gt_d2]) (by norm_num) hu he0 he1'

private lemma positive_diagonal {u:ℝ} (hu:0≤u ∧ u≤2/5) :
    0<westMinorant kPos 0 u u := by
  have he0 := vertex_bounds.2.2.2.1
  have he1 := vertex_bounds.2.2.2.2.2.2
  have he0' : 0<westMinorant kPos 0 0 0 := by
    simpa only [westMinorant,Real.sin_zero,mul_zero] using he0
  rw [westMinorant_diagonal] at he0' he1 ⊢
  exact trig_positive (by norm_num [aW]) (by norm_num [kPos])
    (by norm_num) (by linarith [Real.pi_gt_d2]) hu he0' he1

/-- Positivity on `t ≤ u ≤ 0`, from the edge `t = -2/3` and the diagonal. -/
lemma westMinorant_negative {t u:ℝ}
    (ht:-2/3≤t) (hu:-2/5≤u ∧ u≤0) (htu:t≤u) :
    0<westMinorant (19759/400000) (-3/10) t u := by
  have hc := t_coefficients (show -2/5≤u ∧ u≤2/5 by exact ⟨hu.1,by linarith [hu.2]⟩)
  have hleft := far_negative hu
  have hright := negative_diagonal hu
  change 0<westMinorant kNeg (-3/10) t u
  rw [westMinorant_in_t] at hleft hright ⊢
  exact trig_positive_negative hc.1 hc.2.1
    (by linarith [Real.pi_gt_d2]) hu.2 ⟨ht,htu⟩ hleft hright

/-- Positivity on `t ≤ 0 ≤ u`, from the edges `t = -2/3` and `t = 0`. -/
lemma westMinorant_mixed {t u:ℝ}
    (ht:-2/3≤t ∧ t≤0) (hu:0≤u ∧ u≤2/5) :
    0<westMinorant (19759/400000) 0 t u := by
  have hc := t_coefficients (show -2/5≤u ∧ u≤2/5 by exact ⟨by linarith [hu.1],hu.2⟩)
  have hleft := far_positive hu
  have hright := zero_edge (K:=kNeg) hu
  change 0<westMinorant kNeg 0 t u
  rw [westMinorant_in_t] at hleft hright ⊢
  exact trig_positive_negative hc.1 hc.2.1
    (by linarith [Real.pi_gt_d2]) (by norm_num) ht hleft hright

/-- Positivity on `0 ≤ t ≤ u ≤ 2/5`, from the edge `t = 0` and the diagonal. -/
lemma westMinorant_positive {t u:ℝ}
    (ht:0≤t) (hu:u≤2/5) (htu:t≤u) :
    0<westMinorant (179419/400000) 0 t u := by
  have huc : 0≤u ∧ u≤2/5 := ⟨ht.trans htu,hu⟩
  have hc := t_coefficients (show -2/5≤u ∧ u≤2/5 by exact ⟨by linarith,hu⟩)
  have hleft := zero_edge (K:=kPos) huc
  have hright := positive_diagonal huc
  change 0<westMinorant kPos 0 t u
  rw [westMinorant_in_t] at hleft hright ⊢
  exact trig_positive hc.1 hc.2.2 (by norm_num)
    (by linarith [Real.pi_gt_d2]) ⟨ht,htu⟩ hleft hright

end SquaresInCircles.Six.Analytic
