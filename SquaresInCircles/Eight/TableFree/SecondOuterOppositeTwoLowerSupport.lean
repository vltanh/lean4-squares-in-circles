module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoLowerSupportCurvature

/-!
# The actual weak lower target-secondary owner on the full angle tail

The source chord follows directly from the original circle and
primary height at least one.  The target tangent is integrated from
its true derivative.  A single circle support then gives the exact
concave scalar; two fixed endpoint comparisons cover [.01,.7].
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.LowerSupport

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma small_norm : norm (1/100)<134561/100000 := by
  have hn := norm_data (show (1/100:ℝ)∈Icc 0 (7/10) by norm_num)
  have hs := sin_lower_seven (show (0:ℝ)≤1/100 by norm_num)
  norm_num at hs
  norm_num [g,h] at hn
  nlinarith

lemma cap_norm : norm (7/10)<82613/100000 := by
  have hn := norm_data (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have hs := ShortOuterOne.FiveSame.cap_fine.1
  norm_num [g,h] at hn
  nlinarith

lemma zero_label : V 0< -(1449/100000:ℝ) := by
  norm_num [V,RoleLabel.outer,RoleLabel.eval,VLabel,ShortOuterOne.SameContact.arc_zero]
  linarith [ShortOuterZero.fine_axial_bounds.1]

lemma small_value : (4491/5000:ℝ)<value (1/100) := by
  have hn := norm_data (show (1/100:ℝ)∈Icc 0 (7/10) by norm_num)
  have hprod := mul_le_mul R_data.2.2.le small_norm.le hn.1.le (by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := 1/100)
  have hpi : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  have hV := zero_label
  norm_num [value,g,h,P,RoleLabel.outer,RoleLabel.eval,PLabel] at hc ⊢
  nlinarith

lemma cap_value : (493/500:ℝ)<value (7/10) := by
  have hn := norm_data (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have hprod := mul_le_mul R_data.2.2.le cap_norm.le hn.1.le (by norm_num)
  have hc := ShortOuterOne.FiveSame.cap_fine.2.2.1
  have hpi : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  have hV := zero_label
  norm_num [value,g,h,P,RoleLabel.outer,RoleLabel.eval,PLabel]
  nlinarith

theorem value_lower {x : ℝ} (hx : x∈Icc (1/100) (7/10)) :
    (44889/50000:ℝ)<value x := by
  have hmem {y : ℝ} (hy : y∈Icc (1/100) (7/10)) : y∈Icc 0 (7/10) :=
    ⟨by linarith [hy.1],hy.2⟩
  have hc : ConcaveOn ℝ (Icc (1/100) (7/10)) value :=
    concave_of_deriv2 (fun y hy => value_hasDerivAt (hmem hy))
      (fun y hy => first_hasDerivAt (hmem hy))
      (fun y hy => (second_negative (hmem hy)).le)
  exact concave_gt_of_endpoints hc hx
    (by linarith [small_value]) (by linarith [cap_value])

lemma source_chord {b : ℝ} (hb : b∈Icc 0 bOne) : P b≤P 0+g*b := by
  have hB : b∈Icc 0 outerDiagonal := ⟨hb.1,hb.2.trans bOne_mem.2⟩
  have harc := ShortOuterOne.SameContact.arc_antitone (outer_domain hB)
    (outer_domain bOne_mem) hb.2
  rw [bOne_arc] at harc
  have hprod := mul_le_mul_of_nonneg_right harc hb.1
  have hquad := mul_nonneg hb.1 (show 0≤bOne-b by linarith [hb.2])
  have hcoef : (8196/10000:ℝ)+(2363/100000)*bOne<g := by
    dsimp [g]
    linarith [bOne_bounds.2]
  have hlast := mul_le_mul_of_nonneg_right hcoef.le hb.1
  norm_num [P,RoleLabel.outer,RoleLabel.eval,PLabel]
  nlinarith

lemma target_linear {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : V B≤V 0+h*B := by
  have hd {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
      HasDerivAt (fun s => h*s-V s) (h-VLabel.d1 t) t := by
    exact (((hasDerivAt_id t).const_mul h).sub
      (VLabel.outer_hasDerivAt (outer_domain ht))).congr_deriv (by ring)
  have hm : MonotoneOn (fun s => h*s-V s) (Icc 0 outerDiagonal) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => (hd ht).continuousAt.continuousWithinAt
    · exact fun t ht => hd (Ioo_subset_Icc_self ht)
    · intro t ht
      dsimp [h]
      linarith [V_first_upper (Ioo_subset_Icc_self ht)]
  have hh := hm outer_zero_mem hB hB.1
  nlinarith

lemma circle_support {b x : ℝ} (hb : b∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    h*Real.cos x*U b+(g-h*Real.sin x)*W b≤R*norm x := by
  have hc := UW_circle (outer_domain hb)
  have hn := norm_data hx
  have ht := Real.sin_sq_add_cos_sq x
  have hn2 : (h*Real.cos x)^2+(g-h*Real.sin x)^2=(norm x)^2 := by
    rw [hn.2]
    linear_combination h^2*ht
  have hid : Q0*((h*Real.cos x)^2+(g-h*Real.sin x)^2)-
      (h*Real.cos x*U b+(g-h*Real.sin x)*W b)^2=
      (h*Real.cos x*W b-(g-h*Real.sin x)*U b)^2 := by
    linear_combination -((h*Real.cos x)^2+(g-h*Real.sin x)^2)*hc
  rw [hn2,←R_data.2.1] at hid
  have hprod := mul_pos R_data.1 hn.1
  have hs := sq_nonneg (h*Real.cos x*W b-(g-h*Real.sin x)*U b)
  nlinarith

lemma actual_support {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hcut : B≤lowerCut a b x) :
    value x≤OppositeTwo.value b B (Real.pi/2-x) := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2⟩
  have hA : a∈Icc outerDiagonal outerAxial := ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩
  have ha : 1≤a := by linarith [LowerSecondary.cut_upper hs hx,ht.1]
  have hbone := ShortOuterOne.SameContact.arc_antitone (primary_domain primary_one_mem)
    (primary_domain hA) ha
  rw [(ShortOuterOne.SameContact.actual_arc hs).2] at hbone
  change b≤bOne at hbone
  have hP := source_chord ⟨hs.1,hbone⟩
  have hV := target_linear hB
  have htarget := mul_le_mul_of_nonneg_left hcut (show 0≤h by norm_num [h])
  have hcircle := circle_support hb hx
  dsimp [U,W] at hcircle
  rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hcircle
  dsimp [value,OppositeTwo.value,lowerCut] at *
  nlinarith

theorem original_tail {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc (1/100) (7/10))
    (hm : 0≤forwardMargin 2 a b A B (-1) 1 (Real.pi/2-x)) :
    (44889/50000:ℝ)<OppositeTwo.value b B (Real.pi/2-x) := by
  have hangle : x∈Icc 0 (7/10) := ⟨by linarith [hx.1],hx.2⟩
  have hcut : B≤lowerCut a b x := by
    have hw := lower_width hangle
    norm_num [forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
    dsimp [lowerCut]
    linarith
  exact (value_lower hx).trans_le (actual_support hs ht hangle hcut)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.LowerSupport
