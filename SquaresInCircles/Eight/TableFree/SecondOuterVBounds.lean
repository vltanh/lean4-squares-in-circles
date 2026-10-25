module

public import SquaresInCircles.Eight.TableFree.SecondOuterHigherCalculus
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoLabels

/-!
# Source chords and strict circle derivatives for positive edge three

Both chords follow from strict concavity and their two actual endpoint
values.  The additional derivative references are single rational
coordinates with radicals enclosed by exact integer squares.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma V_zero : V 0= -(41/4000)*outerAxial := by
  norm_num [V,RoleLabel.outer,RoleLabel.eval,VLabel,ShortOuterOne.SameContact.arc_zero]

lemma V_zero_bounds : (-29/2000:ℝ)<V 0 ∧ V 0< -1449/100000 := by
  rw [V_zero]
  constructor <;> linarith [ShortOuterZero.fine_axial_bounds.1,
    ShortOuterZero.fine_axial_bounds.2]

lemma V_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : (-29/2000:ℝ)<V b :=
  V_zero_bounds.1.trans_le (V_monotone outer_zero_mem hb hb.1)

lemma V_concave : ConcaveOn ℝ (Icc 0 outerDiagonal) V :=
  concave_of_deriv2
    (fun b hb => VLabel.outer_hasDerivAt (outer_domain hb))
    (fun b hb => VLabel.d1_hasDerivAt (outer_domain hb))
    (fun b hb => by linarith [V_second_upper hb])

lemma V_diagonal : V outerDiagonal=(7503/50000)*outerDiagonal+
    (63457/100000)*outerDiagonal^2 := by
  dsimp [V,RoleLabel.outer,RoleLabel.eval,VLabel]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  ring

lemma V_diagonal_bounds : (648/1000:ℝ)<V outerDiagonal ∧
    V outerDiagonal<6481/10000 := by
  rw [V_diagonal]
  have hh := diagonal_fine
  have hlo : (89921406510940/100000000000000:ℝ)^2<outerDiagonal^2 := by
    nlinarith [hh.1]
  have hhi : outerDiagonal^2<(89921406510941/100000000000000:ℝ)^2 := by
    nlinarith [hh.1,hh.2]
  constructor <;> nlinarith [hh.1,hh.2]

lemma V_chord {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    V 0+(92/125)*b≤V b := by
  have hc : ConcaveOn ℝ (Icc 0 outerDiagonal)
      (fun t => V t-V 0-(92/125)*t) :=
    concave_of_deriv2 (f' := fun t => VLabel.d1 t-92/125)
      (fun t ht => (((VLabel.outer_hasDerivAt (outer_domain ht)).sub_const (V 0)).sub
        ((hasDerivAt_id' t).const_mul (92/125))).congr_deriv (by ring))
      (fun t ht => (VLabel.d1_hasDerivAt (outer_domain ht)).sub_const (92/125))
      (fun t ht => by linarith [V_second_upper ht])
  have hr : 0<V outerDiagonal-V 0-(92/125)*outerDiagonal := by
    linarith [V_diagonal_bounds.1,V_zero_bounds.2,diagonal_fine.2]
  have hh := hc.min_le_of_mem_Icc outer_zero_mem
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩) hb
  have hz : V 0-V 0-(92/125)*0=0 := by ring
  rw [hz,min_eq_left hr.le] at hh
  linarith

lemma V_short_mem : (7/20:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma V_short_chord_end : V 0+(49/50)*(7/20)<V (7/20) := by
  have hu := shifted_chart_reference (outer_domain V_short_mem)
    (l := (178692473260627/100000000000000:ℝ))
    (u := (178692473260628/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have he : V (7/20)= -(41/4000)*(U (7/20)-1/2)+
      (16031/100000)*(7/20)+(63457/100000)*(U (7/20)-1/2)*(7/20) := by
    dsimp [V,RoleLabel.outer,RoleLabel.eval,VLabel,U]
    ring
  rw [he]
  linarith [hu.1,V_zero_bounds.2]

lemma V_chord_short {b : ℝ} (hb : b∈Icc 0 (7/20)) :
    V 0+(49/50)*b≤V b := by
  have hdom : Icc (0:ℝ) (7/20)⊆Icc 0 outerDiagonal := by
    intro t ht
    exact ⟨ht.1,ht.2.trans V_short_mem.2⟩
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (7/20))
      (fun t => V t-V 0-(49/50)*t) :=
    concave_of_deriv2 (f' := fun t => VLabel.d1 t-49/50)
      (fun t ht => (((VLabel.outer_hasDerivAt (outer_domain (hdom ht))).sub_const (V 0)).sub
        ((hasDerivAt_id' t).const_mul (49/50))).congr_deriv (by ring))
      (fun t ht => (VLabel.d1_hasDerivAt (outer_domain (hdom ht))).sub_const (49/50))
      (fun t ht => by linarith [V_second_upper (hdom ht)])
  have hh := hc.min_le_of_mem_Icc (by norm_num) (by norm_num) hb
  have hz : V 0-V 0-(49/50)*0=0 := by ring
  have hr : 0<V (7/20)-V 0-(49/50)*(7/20) := by linarith [V_short_chord_end]
  rw [hz,min_eq_left hr.le] at hh
  linarith

lemma V_zero_first_lower : (1303/1250:ℝ)<VLabel.d1 0 := by
  have hr := (outer_ratio_bounds outer_zero_mem).1
  norm_num [RoleLabel.d1,VLabel,ShortOuterOne.SameContact.arc_zero]
  linarith [fine_outer_endpoint_bounds.1]

lemma V_short_first_upper : VLabel.d1 (7/20)<(877/1000:ℝ) := by
  have hh := VLabel.first_chart_reference (outer_domain V_short_mem)
    (l := (178692473260627/100000000000000:ℝ))
    (u := (178692473260628/100000000000000:ℝ))
    (dlo := (0:ℝ)) (dhi := (877/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [VLabel,W,Q0]) (by norm_num [VLabel,W,Q0])
  exact hh.2

lemma V_six_first_lower : (639/1000:ℝ)<VLabel.d1 (3/5) := by
  have hh := VLabel.first_chart_reference
    (outer_domain (Asymmetric.rational_outer_mem (show (3/5:ℝ)∈Icc 0 (899/1000) by norm_num)))
    (l := (164487081559616/100000000000000:ℝ))
    (u := (164487081559617/100000000000000:ℝ))
    (dlo := (639/1000:ℝ)) (dhi := (1:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [VLabel,W,Q0]) (by norm_num [VLabel,W,Q0])
  exact hh.1

lemma V_tenth_second_upper : VLabel.d2 (1/10)<(-217/500:ℝ) := by
  have hh := VLabel.second_chart_reference
    (outer_domain (Asymmetric.rational_outer_mem (show (1/10:ℝ)∈Icc 0 (899/1000) by norm_num)))
    (l := (188562986824031/100000000000000:ℝ))
    (u := (188562986824032/100000000000000:ℝ))
    (dlo := (-1:ℝ)) (dhi := (-217/500:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [VLabel,W,Q0]) (by norm_num [VLabel,W,Q0])
  exact hh.2

lemma V_second_late {b : ℝ} (hb : b∈Icc (1/10) outerDiagonal) :
    VLabel.d2 b<(-217/500:ℝ) :=
  (V_second_antitone
    (Asymmetric.rational_outer_mem (show (1/10:ℝ)∈Icc 0 (899/1000) by norm_num))
    ⟨by linarith [hb.1],hb.2⟩ hb.1).trans_lt V_tenth_second_upper

lemma outer_ratioDD_comparison {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    ratioDD b<(43/20)*ratioD b := by
  have hu := U_positive (outer_domain hb)
  have hd := (outer_ratio_bounds hb).2.2.1
  have hh := UW_bounds hb
  have hquot : 3*W b/(U b)^2<(43/20:ℝ) := by
    apply (div_lt_iff₀ (sq_pos_of_pos hu)).2
    have hsq : (1399/1000:ℝ)^2<(U b)^2 := by nlinarith [hh.1]
    nlinarith [hh.2.2.2]
  rw [ratioDD_formula hb]
  exact mul_lt_mul_of_pos_right hquot hd

end SquaresInCircles.Eight.TableFree.SecondWord
