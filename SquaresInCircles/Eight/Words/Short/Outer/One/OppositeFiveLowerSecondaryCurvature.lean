module

public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveLowerSecondaryGeometry

/-!
# Eight squares: uniform curvature along the original lower secondary contact

Both positive circle contributions are kept. The constants `1.915` and `1.457` bound the roots
on every segment from the axial reference to a feasible original contact (`tangent`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerSecondary
open CommonQuarter CorePairGeometry Arithmetic

lemma cost_hasDerivAt (r : Bool) {v u : ℝ} (hd : Domain v u) :
    HasDerivAt (fun w => cost r w u) (first r v u) v := by
  have hT0 := (root_hasDerivAt hd.2.2).comp v ((hasDerivAt_id' v).add_const (Real.cos u))
  have hT : HasDerivAt (fun w => root (w+Real.cos u)) (rootD (Z v u)*1) v := hT0
  have hh := (((((root_hasDerivAt hd.2.1).const_mul (p r)).const_add
    (Real.pi/2-u+cShift r)).fun_sub ((hasDerivAt_id' v).const_mul (q r+D r u))).sub_const
      (D r u*Real.cos u)).fun_sub (hT.const_mul (E r u))
  exact hh.congr_deriv (by simp only [first]; ring)

lemma first_hasDerivAt (r : Bool) {v u : ℝ} (hd : Domain v u) :
    HasDerivAt (fun w => first r w u) (second r v u) v := by
  have hT0 := (rootD_hasDerivAt hd.2.2).comp v ((hasDerivAt_id' v).add_const (Real.cos u))
  have hT : HasDerivAt (fun w => rootD (w+Real.cos u)) (rootDD (Z v u)*1) v := hT0
  have hh := (((rootD_hasDerivAt hd.2.1).const_mul (p r)).sub_const (q r+D r u)).fun_sub
    (hT.const_mul (E r u))
  exact hh.congr_deriv (by simp only [second]; ring)

lemma second_formula (r : Bool) (v u : ℝ) : second r v u=
    (-p r)*Q0/(root v)^3+E r u*Q0/(T v u)^3 := by
  dsimp [second,rootDD,T]
  ring

lemma roots_upper {v u : ℝ} (hd : Domain v u) :
    root v<(383/200:ℝ) ∧ T v u<(1457/1000:ℝ) := by
  have hs : root v<(383/200:ℝ) := (root_le_X0 hd.2.1).trans_lt (by linarith [X0_bounds.2])
  have hz : (67/50:ℝ)<Z v u := by dsimp [Z]; linarith [hd.2.1.1,(small_trig hd.1).1]
  have ht := root_sq hd.2.2
  have hp := root_positive hd.2.2
  have ht' : T v u<(1457/1000:ℝ) := by
    dsimp [T]
    norm_num [Q0] at ht
    nlinarith
  exact ⟨hs,ht'⟩

lemma second_lower (r : Bool) {v u : ℝ} (hd : Domain v u) : (57/50:ℝ)<second r v u := by
  have hS := root_positive hd.2.1
  have hT := root_positive hd.2.2
  have hS3 : 0<(root v)^3 := pow_pos hS _
  have hT3 : 0<(T v u)^3 := pow_pos hT _
  have hSmax : (root v)^3<(383/200:ℝ)^3 := by
    gcongr
    exact (roots_upper hd).1
  have hTmax : (T v u)^3<(1457/1000:ℝ)^3 := by
    gcongr
    exact (roots_upper hd).2
  have hp : (20967/100000:ℝ)≤-p r := by linarith [(coefficient_bounds r).2.1]
  have hE := E_lower r hd.1
  have hsrc : ((20967/100000:ℝ)*Q0)/(383/200:ℝ)^3<(-p r)*Q0/(root v)^3 := by
    apply (lt_div_iff₀ hS3).2
    have hnum := mul_le_mul_of_nonneg_right hp (by norm_num [Q0] : 0≤Q0)
    norm_num [Q0] at hSmax hnum ⊢
    nlinarith
  have htgt : ((81/100:ℝ)*Q0)/(1457/1000:ℝ)^3<E r u*Q0/(T v u)^3 := by
    apply (lt_div_iff₀ hT3).2
    have hnum := mul_lt_mul_of_pos_right hE (by norm_num [Q0] : 0<Q0)
    norm_num [Q0] at hTmax hnum ⊢
    nlinarith
  rw [second_formula]
  norm_num [Q0] at hsrc htgt ⊢
  linarith

lemma axial_identity (r : Bool) (u : ℝ) : cost r (1/2) u=axial r u := by
  dsimp [cost,T,Z]
  rw [root_half,X0_eq]
  dsimp [axial,cShift,axialZ,axialT]
  ring

theorem tangent (r : Bool) {v u : ℝ} (hd : Domain v u) :
    axial r u+first r (1/2) u*(v-1/2)+(57/100:ℝ)*(v-1/2)^2≤cost r v u := by
  have hh := CenteredMonomialBounds.second_derivative_tangent_lower
    (f:=fun w => cost r w u) (df:=fun w => first r w u) (ddf:=fun w => second r w u)
    (l:=1/2) (h:=v) (x₀:=1/2) (x:=v) (κ:=57/50)
    (fun w hw => cost_hasDerivAt r (interval_domain hd hw))
    (fun w hw => first_hasDerivAt r (interval_domain hd hw))
    (fun w hw => (second_lower r (interval_domain hd hw)).le)
    (left_mem_Icc.2 hd.2.1.1) (right_mem_Icc.2 hd.2.1.1)
  have h0 : cost r (1/2) u+first r (1/2) u*(v-1/2)+(57/50)/2*(v-1/2)^2≤cost r v u := hh
  rw [axial_identity] at h0
  linarith

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerSecondary
