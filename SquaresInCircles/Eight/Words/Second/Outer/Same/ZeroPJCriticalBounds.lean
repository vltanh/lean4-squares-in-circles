module

public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJCurvature

/-!
# Eight squares: the complete P/J critical-coordinate and mixed-curvature bounds

E>0 makes U increase.  The full radial interval
then controls the derivative of V/U, and integration gives the single
lower bound (V/U)(P')^3>.2725 on the whole critical curve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic

lemma criticalU_monotone : MonotoneOn criticalU sourceInterval :=
  monoOn_of_hasDeriv_nonneg
    (fun t ht => (criticalU_hasDerivAt (source_domain ht)).continuousAt.continuousWithinAt)
    (fun t ht => criticalU_hasDerivAt (source_domain (Ioo_subset_Icc_self ht)))
    (fun t ht => div_nonneg (by linarith [(E_bounds (Ioo_subset_Icc_self ht)).1])
      (pow_nonneg (p_positive (source_domain (Ioo_subset_Icc_self ht))).le 3))

lemma criticalU_bounds {t : ℝ} (ht : t∈sourceInterval) :
    (1801/1000:ℝ)<criticalU t ∧ criticalU t<37/20 := by
  exact ⟨criticalU_endpoints.1.trans_le
      (criticalU_monotone ⟨le_rfl,six_mem.2⟩ ht ht.1),
    (criticalU_monotone ht ⟨six_mem.2,le_rfl⟩ ht.2).trans_lt
      criticalU_endpoints.2.2⟩

lemma critical_data {t : ℝ} (ht : t∈sourceInterval) :
    0<criticalU t ∧ 0<Q0-(criticalU t)^2 ∧ 0<criticalV t ∧
      (criticalU t)^2+(criticalV t)^2=Q0 ∧
      (7/10:ℝ)<criticalV t ∧ criticalV t<41/50 ∧
      (189/500:ℝ)<criticalRatio t := by
  have hu := criticalU_bounds ht
  have hu0 : 0<criticalU t := by linarith
  have hl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1801/1000) hu.1.le 2
  have hh := pow_le_pow_left₀ hu0.le hu.2.le 2
  have hrad : 0<Q0-(criticalU t)^2 := by norm_num [Q0]; linarith
  have hv : 0<criticalV t := Real.sqrt_pos.mpr hrad
  have hc := criticalV_sq hrad.le
  have hvl : (7/10:ℝ)<criticalV t := by norm_num [Q0] at hc; nlinarith
  have hvu : criticalV t<(41/50:ℝ) := by norm_num [Q0] at hc; nlinarith
  refine ⟨hu0,hrad,hv,by linarith,hvl,hvu,?_⟩
  apply (lt_div_iff₀ hu0).2
  nlinarith

lemma critical_mass_lower {t : ℝ} (ht : t∈sourceInterval) :
    (463/250:ℝ)^2*(871/1250)<(criticalU t)^2*criticalV t := by
  let f : ℝ→ℝ := fun u => u^4*(Q0-u^2)
  let df : ℝ→ℝ := fun u => 2*u^3*(2*Q0-3*u^2)
  have hd (u : ℝ) : HasDerivAt f (df u) u :=
    (((hasDerivAt_id' u).fun_pow 4).fun_mul
      (((hasDerivAt_id' u).fun_pow 2).const_sub Q0)).congr_deriv
        (by dsimp only [df]; push_cast; ring)
  have hm : AntitoneOn f (Icc (9/5:ℝ) (463/250)) :=
    antiOn_of_hasDeriv_nonpos
      (fun u _ => (hd u).continuousAt.continuousWithinAt)
      (fun u _ => hd u)
      (fun u hu => by
        have hu0 : 0≤u := by linarith [hu.1]
        have hu2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤9/5) hu.1.le 2
        have hn : 2*Q0-3*u^2≤0 := by norm_num [Q0]; linarith
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hn)
  have hu := criticalU_bounds ht
  have hdom : criticalU t∈Icc (9/5:ℝ) (463/250) :=
    ⟨by linarith,by linarith⟩
  have hmin := hm hdom (by norm_num) hdom.2
  have hreference : ((463/250:ℝ)^2*(871/1250))^2<f (463/250) := by
    norm_num [f,Q0]
  have hh := critical_data ht
  have he : ((criticalU t)^2*criticalV t)^2=f (criticalU t) := by
    dsimp only [f]
    linear_combination (criticalU t)^4*hh.2.2.2.1
  have hpos : 0<(criticalU t)^2*criticalV t :=
    mul_pos (pow_pos hh.1 2) hh.2.2.1
  exact lt_of_pow_lt_pow_left₀ 2 hpos.le (by rw [he]; linarith)

lemma criticalRatio_derivative_lower {t : ℝ} (ht : t∈sourceInterval) :
    -(23/50:ℝ)<criticalRatioD t := by
  have hd := critical_data ht
  have hp := p_positive (source_domain ht)
  have hfirst := first_tangent ht
  have hpbase : (219/250:ℝ)<p t := by linarith [ht.1]
  have hp3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤219/250) hpbase.le 3
  have hmass := critical_mass_lower ht
  have hden := mul_lt_mul hmass hp3
    (by norm_num : (0:ℝ)<(219/250)^3)
    (mul_nonneg (sq_nonneg (criticalU t)) hd.2.2.1.le)
  have he := (E_bounds ht).2
  have hpos : 0<(criticalU t)^2*criticalV t*(p t)^3 := by positivity
  dsimp [criticalRatioD]
  apply (lt_div_iff₀ hpos).2
  norm_num [Q0] at he hden ⊢
  nlinarith

lemma criticalRatio_initial : (227/500:ℝ)<criticalRatio (3/5) := by
  have ht : (3/5:ℝ)∈sourceInterval := ⟨le_rfl,six_mem.2⟩
  have hd := critical_data ht
  have hu := criticalU_endpoints.2.1
  have hu2 := pow_le_pow_left₀ hd.1.le hu.le 2
  have hprod := mul_le_mul_of_nonneg_left hu2
    (by norm_num : (0:ℝ)≤1+(227/500)^2)
  dsimp [criticalRatio]
  apply (lt_div_iff₀ hd.1).2
  have hc := hd.2.2.2.1
  norm_num [Q0] at hc
  nlinarith [hd.2.2.1]

lemma criticalRatio_tangent {t : ℝ} (ht : t∈sourceInterval) :
    (227/500:ℝ)-(23/50)*(t-3/5)<criticalRatio t := by
  have hm : MonotoneOn (fun u => criticalRatio u+(23/50)*u) sourceInterval :=
    monoOn_of_hasDeriv_nonneg
      (fun u hu => ((criticalRatio_hasDerivAt (source_domain hu)
        (critical_data hu).1 (critical_data hu).2.1).add
          ((hasDerivAt_id u).const_mul (23/50))).continuousAt.continuousWithinAt)
      (fun u hu => (criticalRatio_hasDerivAt (source_domain (Ioo_subset_Icc_self hu))
        (critical_data (Ioo_subset_Icc_self hu)).1
        (critical_data (Ioo_subset_Icc_self hu)).2.1).add
          ((hasDerivAt_id u).const_mul (23/50)))
      (fun u hu => by linarith [criticalRatio_derivative_lower (Ioo_subset_Icc_self hu)])
  have hh := hm ⟨le_rfl,six_mem.2⟩ ht ht.1
  linarith [criticalRatio_initial]

def productMinorant (x : ℝ) : ℝ :=
  (227/500-(23/50)*x)*(219/250+(253/1000)*x)^3

lemma productMinorant_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (3/10)) :
    (109/400:ℝ)<productMinorant x := by
  let df : ℝ→ℝ := fun y => (219/250+(253/1000)*y)^2*
    (3*(253/1000)*(227/500)-(23/50)*(219/250)-4*(23/50)*(253/1000)*y)
  have hd (y : ℝ) : HasDerivAt productMinorant (df y) y :=
    ((((hasDerivAt_id' y).const_mul (23/50)).const_sub (227/500)).fun_mul
      ((((hasDerivAt_id' y).const_mul (253/1000)).const_add (219/250)).fun_pow 3)).congr_deriv
        (by dsimp only [df]; push_cast; ring)
  have hm : AntitoneOn productMinorant (Icc (0:ℝ) (3/10)) :=
    antiOn_of_hasDeriv_nonpos
      (fun y _ => (hd y).continuousAt.continuousWithinAt) (fun y _ => hd y)
      (fun y hy => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
        (by norm_num; linarith [hy.1]))
  exact (by norm_num [productMinorant] : (109/400:ℝ)<productMinorant (3/10)).trans_le
    (hm hx (by norm_num) hx.2)

theorem critical_mixed_lower {t : ℝ} (ht : t∈sourceInterval) :
    (109/400:ℝ)<criticalRatio t*(p t)^3 := by
  let x := t-3/5
  have hx : x∈Icc (0:ℝ) (3/10) := by
    dsimp [x]
    constructor <;> linarith [ht.1,ht.2,outer_endpoint_bounds.2.2.2]
  have hr := criticalRatio_tangent ht
  have hp := first_tangent ht
  have hrl : 0≤(227/500:ℝ)-(23/50)*x := by linarith [hx.2]
  have hpl : 0≤(219/250:ℝ)+(253/1000)*x := by linarith [hx.1]
  have hp3 := pow_le_pow_left₀ hpl (show (219/250:ℝ)+(253/1000)*x≤p t by
    simpa [x] using hp.le) 3
  have hle := mul_le_mul_of_nonneg_left hp3 hrl
  have hlt := mul_lt_mul_of_pos_right
    (show (227/500:ℝ)-(23/50)*x<criticalRatio t by simpa [x] using hr)
    (pow_pos (p_positive (source_domain ht)) 3)
  have hh := productMinorant_lower hx
  dsimp [productMinorant] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.SameZero.PJ
