module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoPrimaryReferences

/-!
# Eight squares: the complete lower source-primary diagonal bound

The physical diagonal cost is concave through `.4` and decreases
afterward.  The increasing circle coordinate reaches its actual sorted
endpoint before `.556`.  Both true endpoints have strict reserves.
The final theorem identifies this curve from the original target circle
and original weak-axis contact equation.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.PrimaryDiagonal

open CommonQuarter CorePairGeometry Arithmetic

def cost (x : ℝ) : ℝ := value outerDiagonal (height x) (Real.pi/2-x)
def first (x : ℝ) : ℝ := -1+TLabel.d1 (height x)*speed x
def second (x : ℝ) : ℝ :=
  TLabel.d2 (height x)*(speed x)^2+TLabel.d1 (height x)*acceleration x

lemma before {x t : ℝ} (hx : Domain x) (ht : t∈Icc 0 x) : Domain t := by
  have htf : t∈Icc 0 (7/10) := ⟨ht.1,ht.2.trans hx.1.2⟩
  exact ⟨htf,(height_monotone htf hx.1 ht.2).trans hx.2⟩

lemma cost_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt cost (first x) x := by
  have hT := (TLabel.outer_hasDerivAt (outer_domain (target_mem hx))).comp x
    (height_hasDerivAt hx.1)
  have hd := (((hasDerivAt_id' x).const_sub (Real.pi/2)).sub_const
    (P outerDiagonal)).fun_add hT
  show HasDerivAt (fun y => Real.pi/2-y-P outerDiagonal+(TLabel.outer ∘ height) y) _ x
  exact hd.congr_deriv (by dsimp [first])

lemma first_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt first (second x) x := by
  have hd := (((TLabel.d1_hasDerivAt (outer_domain (target_mem hx))).comp x
    (height_hasDerivAt hx.1)).fun_mul (speed_hasDerivAt hx.1)).const_add (-1)
  show HasDerivAt (fun y => -1+(TLabel.d1 ∘ height) y*speed y) _ x
  refine hd.congr_deriv ?_
  simp only [Function.comp_apply,second]
  ring

lemma target_second_mid {b : ℝ} (hb : b∈Icc 0 (181/250)) :
    TLabel.d2 b<(99/250:ℝ) := by
  have href : (181/250:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hm := T_second_monotone ⟨hb.1,hb.2.trans href.2⟩ href hb.2
  have hh := TLabel.second_chart_reference (outer_domain href)
    (l := (3887/2500:ℝ)) (u := (15549/10000:ℝ))
    (dlo := (-2:ℝ)) (dhi := (99/250:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  exact hm.trans_lt hh.2

lemma target_first_late {b : ℝ} (hb : b∈Icc (3/5) outerDiagonal) :
    TLabel.d1 b<(387/500:ℝ) := by
  have hdom (t : ℝ) (ht : t∈Icc (3/5) outerDiagonal) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2⟩
  have hh := positive_of_second_nonpos
    (f := fun t => 387/500-TLabel.d1 t)
    (d := fun t => -TLabel.d2 t) (dd := fun t => -TLabel.d3 t) hb
    (fun t ht => (TLabel.d1_hasDerivAt (outer_domain (hdom t ht))).const_sub (387/500))
    (fun t ht => (TLabel.d2_hasDerivAt (outer_domain (hdom t ht))).neg)
    (fun t ht => by linarith [T_third_lower (hdom t ht)])
    (by linarith [T_six_first.2])
    (by rw [T_first_diagonal]; linarith [fine_outer_endpoint_bounds.2])
  linarith

lemma early_second {x : ℝ} (hx : x∈Icc 0 (3/10)) : second x<0 := by
  have hd := before four_domain (show x∈Icc 0 (2/5) from ⟨hx.1,by linarith [hx.2]⟩)
  have hB := target_mem hd
  have hm := height_monotone hd.1 (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num) hx.2
  have ht := T_second_early (show height x∈Icc 0 (3/5) from
    ⟨hB.1,by linarith [three_reference.1]⟩)
  have hleft := mul_neg_of_neg_of_pos (by linarith [ht] : TLabel.d2 (height x)<0)
    (pow_pos (show 0<speed x by linarith [speed_positive hd.1]) 2)
  have hright := mul_neg_of_pos_of_neg
    (by linarith [T_first_lower hB] : 0<TLabel.d1 (height x))
    (acceleration_negative hd.1)
  dsimp [second]
  linarith

lemma middle_second {x : ℝ} (hx : x∈Icc (3/10) (2/5)) : second x<0 := by
  have hd := before four_domain (show x∈Icc 0 (2/5) from ⟨by linarith [hx.1],hx.2⟩)
  have hB := target_mem hd
  have hheight := height_monotone hd.1 four_domain.1 hx.2
  have hT := target_second_mid ⟨hB.1,by linarith [four_reference.2.1]⟩
  have hspeed := speed_antitone (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num) hd.1 hx.1
  have hspeedupper : speed x<(697/500:ℝ) := hspeed.trans_lt three_reference.2.2
  have hspeed0 : 0<speed x := by linarith [speed_positive hd.1]
  have hsq := pow_lt_pow_left₀ hspeedupper hspeed0.le (by norm_num : (2:ℕ)≠0)
  have hpositive := mul_lt_mul_of_pos_right hT (pow_pos hspeed0 2)
  have hvertical := height_monotone (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num) hd.1 hx.1
  have hV : (273/250:ℝ)<vertical x := by
    dsimp [height] at hvertical
    linarith [three_reference.2.1]
  have hhorizontal := horizontal_antitone hd.1 four_domain.1 hx.2
  have hU : (777/500:ℝ)<horizontal x := four_reference.2.2.1.trans_le hhorizontal
  have hfactor := factor_antitone hd.1 four_domain.1 hx.2
  have hf : (159/200:ℝ)<factor x := four_reference.2.2.2.1.trans_le hfactor
  have hf2 := pow_lt_pow_left₀ hf (by norm_num : (0:ℝ)≤159/200) (by norm_num : (2:ℕ)≠0)
  have hleft := mul_lt_mul hV hf2.le (by norm_num : (0:ℝ)<(159/200)^2)
    (by linarith [hV] : 0≤vertical x)
  have hfd := mid_factorD (show x∈Icc 0 (2/5) from ⟨by linarith [hx.1],hx.2⟩)
  have hright := mul_lt_mul hU (show (2/5:ℝ)≤ -factorD x by linarith)
    (by norm_num : (0:ℝ)<2/5) (by linarith [hU] : 0≤horizontal x)
  have hacc : (273/250:ℝ)*(159/200)^2+(777/500)*(2/5)< -acceleration x := by
    dsimp [acceleration]
    linarith
  have hpaid := mul_lt_mul (T_first_lower hB) hacc.le
    (by norm_num : (0:ℝ)<(273/250)*(159/200)^2+(777/500)*(2/5))
    (by linarith [T_first_lower hB] : 0≤TLabel.d1 (height x))
  dsimp [second]
  norm_num at hsq hpaid
  linarith

lemma initial_concave : ConcaveOn ℝ (Icc 0 (2/5)) cost := by
  apply concave_of_deriv2
    (fun x hx => cost_hasDerivAt (before four_domain hx))
    (fun x hx => first_hasDerivAt (before four_domain hx))
  intro x hx
  rcases le_total x (3/10) with h | h
  · exact (early_second ⟨hx.1,h⟩).le
  · exact (middle_second ⟨h,hx.2⟩).le

lemma late_first {x : ℝ} (hx : Domain x) (hfour : (2/5:ℝ)≤x) : first x<0 := by
  have hm := height_monotone four_domain.1 hx.1 hfour
  have hT := target_first_late (show height x∈Icc (3/5) outerDiagonal from
    ⟨by linarith [four_reference.1],hx.2⟩)
  have hspeed := speed_antitone four_domain.1 hx.1 hfour
  have hspeedupper := hspeed.trans_lt four_reference.2.2.2.2
  have hh := mul_lt_mul hT hspeedupper.le
    (by linarith [speed_positive hx.1] : 0<speed x) (by norm_num : (0:ℝ)≤387/500)
  dsimp [first]
  norm_num at hh
  linarith

lemma end_contact : ∃ e : ℝ, e∈Icc (2/5) (139/250) ∧ height e=outerDiagonal := by
  have hcont : ContinuousOn height (Icc (2/5) (139/250)) := by
    intro x hx
    exact (height_hasDerivAt (show x∈Icc 0 (7/10) from
      ⟨by linarith [hx.1],by linarith [hx.2]⟩)).continuousAt.continuousWithinAt
  obtain ⟨e,he,heq⟩ := intermediate_value_Icc (show (2/5:ℝ)≤139/250 by norm_num)
    hcont (show outerDiagonal∈Icc (height (2/5)) (height (139/250)) from
      ⟨four_domain.2,end_reference.le⟩)
  exact ⟨e,he,heq⟩

lemma target_diagonal_lower : (679/1000:ℝ)<T outerDiagonal := by
  have hd := diagonal_fine
  have hs := (ShortOuterOne.SameContact.arc_state
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩)).2.2
  rw [ShortOuterOne.SameContact.arc_diagonal] at hs
  have he : T outerDiagonal=167/10000+(121161/50000)*outerDiagonal-
      (187513/100000)*outerDiagonal^2 := by
    dsimp [T,RoleLabel.outer,RoleLabel.eval,TLabel]
    rw [ShortOuterOne.SameContact.arc_diagonal]
    ring
  rw [he]
  norm_num [Q0] at hs
  linarith [hd.1]

lemma zero_value : (8977827/10000000:ℝ)<cost 0 := by
  have hb := target_mem (before four_domain (show (0:ℝ)∈Icc 0 (2/5) by norm_num))
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hh := original_aligned (ShortOuterOne.SameContact.arc_state hd)
    (ShortOuterOne.SameContact.arc_state hb)
    (show 1≤ShortOuterOne.SameContact.arc outerDiagonal+height 0 by
      rw [ShortOuterOne.SameContact.arc_diagonal,height_zero]
      linarith)
  simpa only [cost,sub_zero] using hh

lemma endpoint_value {e : ℝ} (he : e∈Icc (2/5) (139/250)) (hc : height e=outerDiagonal) :
    (9/10:ℝ)<cost e := by
  dsimp [cost,value]
  rw [hc]
  linarith [pi_hand_enclosure.1,P_diagonal_fine,target_diagonal_lower,he.2]

lemma bounded_by_end {x e : ℝ} (hx : Domain x) (he : e∈Icc (2/5) (139/250))
    (hc : height e=outerDiagonal) : x≤e := by
  rcases le_total x e with h | h
  · exact h
  · have hef : e∈Icc 0 (7/10) := ⟨by linarith [he.1],by linarith [he.2]⟩
    have hm := height_half_monotone hef hx.1 h
    dsimp only at hm
    rw [hc] at hm
    linarith [hx.2]

theorem cost_lower {x : ℝ} (hx : Domain x) : (8977827/10000000:ℝ)<cost x := by
  obtain ⟨e,he,hc⟩ := end_contact
  have hefull : e∈Icc 0 (7/10) := ⟨by linarith [he.1],by linarith [he.2]⟩
  have hed : Domain e := ⟨hefull,by rw [hc]⟩
  have hxe := bounded_by_end hx he hc
  have hanti : AntitoneOn cost (Icc (2/5) e) := by
    have hdom (t : ℝ) (ht : t∈Icc (2/5) e) : Domain t :=
      before hed ⟨by linarith [ht.1],ht.2⟩
    exact antiOn_of_hasDeriv_nonpos
      (fun t ht => (cost_hasDerivAt (hdom t ht)).continuousAt.continuousWithinAt)
      (fun t ht => cost_hasDerivAt (hdom t (Ioo_subset_Icc_self ht)))
      (fun t ht => (late_first (hdom t (Ioo_subset_Icc_self ht)) ht.1.le).le)
  have hend := endpoint_value he hc
  rcases le_total x (2/5) with h | h
  · have hfour := hanti (show (2/5:ℝ)∈Icc (2/5) e from ⟨le_rfl,he.1⟩)
      (show e∈Icc (2/5) e from ⟨he.1,le_rfl⟩) he.1
    exact concave_gt_of_endpoints initial_concave ⟨hx.1.1,h⟩ zero_value (by linarith)
  · have hm := hanti (show x∈Icc (2/5) e from ⟨h,hxe⟩)
      (show e∈Icc (2/5) e from ⟨he.1,le_rfl⟩) hxe
    linarith

lemma original_height {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hc : lowerSource A B x=outerDiagonal) : height x=B := by
  let r : ℝ := (A+1/2)*Real.cos x+(B+1/2)*Real.sin x
  have htr := positive_trig hx
  have hr : 0<r := by
    have hfirst := mul_pos (show 0<A+1/2 by linarith [ht.1,ht.2.1])
      (show 0<Real.cos x by linarith [htr.1])
    have hlast := mul_nonneg (show 0≤B+1/2 by linarith [ht.1]) htr.2.2.1
    dsimp [r]
    linarith
  have hz : Z x=(B+1/2)*Real.cos x-(A+1/2)*Real.sin x := by
    dsimp [lowerSource] at hc
    dsimp [Z,offset]
    linarith
  have hcircle : r^2+(Z x)^2=Q0 := by
    rw [hz]
    dsimp [r]
    linear_combination ht.2.2+
      ((A+1/2)^2+(B+1/2)^2)*(Real.sin_sq_add_cos_sq x)
  have hY : Y x=r := by
    have hy := radical_data hx
    have h2 : (Y x)^2=r^2 := by linarith [hy.2.2.2.2]
    exact (pow_left_inj₀ (by linarith [hy.2.2.1]) hr.le two_ne_zero).1 h2
  dsimp [height,vertical]
  rw [hY,hz]
  dsimp [r]
  linear_combination (B+1/2)*(Real.sin_sq_add_cos_sq x)

theorem original_contact {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hc : lowerSource A B x=outerDiagonal) :
    (8977827/10000000:ℝ)<value outerDiagonal B (Real.pi/2-x) := by
  have he := original_height ht hx hc
  have hd : Domain x := ⟨hx,by rw [he]; exact (source_mem ht).2⟩
  simpa only [cost,he] using cost_lower hd

end SquaresInCircles.Eight.SecondWord.NegativeTwo.PrimaryDiagonal
