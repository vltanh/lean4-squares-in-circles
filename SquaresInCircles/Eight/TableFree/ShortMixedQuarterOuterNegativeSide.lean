module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterNegativeSideReferences

/-!
# The whole negative-core side domain from one norm chord

Uncompiled transcription of equations (18)--(23). J''' is positive
throughout [0,.7]. The four named references and J''(.4) give a positive
quadratic lower bound on [.4,.7]. On [0,.4], the convex first derivative
ends negative, so the minimum is at an endpoint. The actual side target
then cancels under the stipulated positive separator multiplier.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.SideChord
open CommonQuarter CorePairGeometry Arithmetic

theorem J3_positive (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (13/10:ℝ)<J3 r x := by
  have hb := Reference.coefficient_bounds r hr
  have tr := positive_trig hx
  have hfirst := mul_lt_mul''
    (show (77/40:ℝ)<3-C r by linarith [hb.2.2.2]) tr.1
    (by norm_num : (0:ℝ)≤77/40) (by norm_num : (0:ℝ)≤19121/25000)
  have hAx : -(221/1000:ℝ)≤A r-x := by linarith [hb.1,hx.2]
  have hsecond := mul_le_mul_of_nonneg_right hAx tr.2.2.1
  have hnegative := mul_le_mul_of_nonpos_left tr.2.2.2.1.le
    (by norm_num : (-(221/1000):ℝ)≤0)
  dsimp [J3]
  linarith

theorem J2_monotone (r : Row) (hr : Rows r) : MonotoneOn (J2 r) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (J2_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => J2_hasDerivAt r x)
    (fun x hx => by linarith [J3_positive r hr (Ioo_subset_Icc_self hx)])

theorem tail_curvature (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈Icc (2/5:ℝ) (7/10)) :
    (9/100:ℝ)<J2 r x :=
  (Reference.initial_shape r hr).2.2.trans_le
    ((J2_monotone r hr) (by norm_num : (2/5:ℝ)∈Icc 0 (7/10))
      ⟨by linarith [hx.1],hx.2⟩ hx.1)

theorem tail_positive (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈Icc (2/5:ℝ) (7/10)) :
    0<J r x := by
  have href := Reference.reference_mem r
  have hv := Reference.reference_reserve r hr
  have hs := abs_lt.mp hv.2
  have hprod := mul_pos (show 0<1/20000-J1 r (reference r) by linarith [hs.2])
    (show 0<J1 r (reference r)+1/20000 by linarith [hs.1])
  apply positive_of_curvature (κ:=(9/100:ℝ)) (by norm_num) hx href
    (fun y _ => J_hasDerivAt r y) (fun y _ => J1_hasDerivAt r y)
    (fun y hy => (tail_curvature r hr hy).le)
  nlinarith [hv.1]

theorem early_derivative_convex (r : Row) (hr : Rows r) : ConvexOn ℝ (Icc 0 (2/5:ℝ)) (J1 r) := by
  have hc : ConcaveOn ℝ (Icc 0 (2/5:ℝ)) (fun x => -J1 r x) := concave_of_deriv2
    (fun x _ => (J1_hasDerivAt r x).neg)
    (fun x _ => (J2_hasDerivAt r x).neg)
    (fun x hx => neg_nonpos.mpr (by
      linarith [J3_positive r hr ⟨hx.1,hx.2.trans (by norm_num : (2/5:ℝ)≤7/10)⟩]))
  have h2 := hc.neg
  have he : (-fun x => -J1 r x)=J1 r := by
    funext x
    simp
  rwa [he] at h2

theorem J_positive (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<J r x := by
  by_cases ht : (2/5:ℝ)≤x
  · exact tail_positive r hr ⟨ht,hx.2⟩
  have hmin := SplitConcavityTools.minimum_of_convex_derivative
    (fun y _ => J_hasDerivAt r y) (early_derivative_convex r hr)
    (show J1 r (2/5)≤0 by linarith [(Reference.initial_shape r hr).2.1])
    (show x∈Icc 0 (2/5:ℝ) from ⟨hx.1,(lt_of_not_ge ht).le⟩)
  have h0 : 0<J r 0 := by linarith [(Reference.initial_shape r hr).1]
  have hlast := tail_positive r hr (show (2/5:ℝ)∈Icc (2/5:ℝ) (7/10) by norm_num)
  exact (lt_min h0 hlast).trans_le hmin

theorem scaled_norm (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    Real.sqrt ((ocG r/Real.cos x-ocP r)^2+(ocQ r)^2)=norm r (Real.cos x)/Real.cos x := by
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have he : (norm r (Real.cos x)/Real.cos x)^2=
      (ocG r/Real.cos x-ocP r)^2+(ocQ r)^2 := by
    rw [div_pow,norm_square]
    field_simp
  have hn : 0≤norm r (Real.cos x)/Real.cos x := div_nonneg (Real.sqrt_nonneg _) hc.le
  rw [← he,Real.sqrt_sq hn]

theorem scaled_value (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (F r x-449/500)*Real.cos x=
      (K r-x)*Real.cos x+ocG r+C r*Real.sin x-CommonQuarter.radius*norm r (Real.cos x) := by
  have hc : Real.cos x≠0 := by linarith [(positive_trig hx).1]
  rw [F,scaled_norm r hx]
  dsimp [K]
  field_simp [hc]
  ring

theorem J_le_scaled_value (r : Row) (hr : Remaining r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    J r x≤(F r x-449/500)*Real.cos x := by
  have hnorm := norm_chord r hr (cosine_mem hx)
  have hp := mul_le_mul_of_nonneg_left hnorm (show 0≤CommonQuarter.radius by linarith [radius_bounds.1])
  rw [scaled_value r hx]
  dsimp [J,A,B]
  nlinarith only [hp]

theorem F_lower (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<F r x := by
  have hh := (J_positive r hr hx).trans_le (J_le_scaled_value r (remaining r hr) hx)
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hpos : 0<F r x-449/500 := pos_of_mul_pos_left hh hc.le
  linarith

theorem original_ge_F (r : Row) (hr : Remaining r) {a b aC bC x : ℝ}
    (hs : OuterState a b) (hside : aC=7/12) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b aC bC (angle false x)) :
    F r x≤outerCoreCost r a b aC bC (angle false x) := by
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  let w := ocG r/Real.cos x
  have hw : 0<w := div_pos (coefficients r hr).2.1 hc
  have hwk : w*Real.cos x=ocG r := div_mul_cancel₀ _ hc.ne'
  have hsep := (primary_separator r hr a b aC bC (angle false x)).1 hm
  rw [angle_width false hx,angle_cos,angle_sin,hside] at hsep
  dsimp [direction] at hsep
  have hp := mul_le_mul_of_nonneg_left hsep hw.le
  have hcircle := outer_circle_lower (X:=ocP r-w) (Y:=-(ocQ r)) hs
  have hnorm : (ocP r-w)^2+(-(ocQ r))^2=(w-ocP r)^2+(ocQ r)^2 := by ring
  rw [hnorm] at hcircle
  have hB : w*bC*Real.cos x=ocG r*bC := by
    calc
      w*bC*Real.cos x=(w*Real.cos x)*bC := by ring
      _=ocG r*bC := by rw [hwk]
  rw [primary_cost r hr]
  dsimp [F,C,angle,direction]
  change Real.pi/2-x+ocC r+w+(-ocP r+ocQ r+ocG r)/2+
      (13*ocG r/12)*(Real.sin x/Real.cos x)-CommonQuarter.radius*Real.sqrt ((w-ocP r)^2+(ocQ r)^2)≤_
  have hcot : (13*ocG r/12)*(Real.sin x/Real.cos x)=(13/12)*w*Real.sin x := by
    dsimp [w]
    ring
  rw [hcot]
  nlinarith only [hp,hcircle,hwk,hB]

theorem original_side (r : Row) (hr : Remaining r) (hrow : Rows r) {a b aC bC x : ℝ}
    (hs : OuterState a b) (hside : aC=7/12) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b aC bC (angle false x)) :
    (449/500:ℝ)<outerCoreCost r a b aC bC (angle false x) :=
  (F_lower r hrow hx).trans_le (original_ge_F r hr hs hside hx hm)

theorem original (r : Row) (hr : Remaining r) (hrow : Rows r) {a b aC bC x : ℝ}
    (hs : OuterState a b) (_ht : CoreState aC bC) (hside : aC=7/12)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b aC bC (angle false x)) :
    (449/500:ℝ)<outerCoreCost r a b aC bC (angle false x) :=
  original_side r hr hrow hs hside hx hm

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.SideChord
