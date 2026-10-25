module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameData
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroPositiveSpeeds

/-!
# The one positive-primary-coefficient favorable zero row

Uncompiled transcription of Section 2 of the favorable same-sign proof.
The written constant multiplier is retained on the entire feasible angle
interval. Both original circle functionals attain their lower support at
the axial endpoint. One initial value and one derivative bound suffice.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.PositiveCoefficient
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open SecondWord (outer_domain outer_zero_mem)

abbrev multiplier : ℝ := 45181/50000

def axialValue (x : ℝ) : ℝ := x+c 2+p 2*outerAxial+multiplier/2+
  (multiplier/2)*Real.cos x+multiplier*(1/2-outerAxial)*Real.sin x
def axialFirst (x : ℝ) : ℝ :=
  1-multiplier*((1/2)*Real.sin x+(outerAxial-1/2)*Real.cos x)
def rho : ℝ := 1/(2*(outerAxial+1/2))
def targetSlope (x : ℝ) : ℝ := multiplier*(Real.cos x+rho*Real.sin x)-t 2

lemma rho_bounds : (5223/20000:ℝ)<rho ∧ rho<(131/500:ℝ) := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hp : 0<2*(outerAxial+1/2) := by linarith
  constructor
  · apply (lt_div_iff₀ hp).2
    linarith
  · apply (div_lt_iff₀ hp).2
    linarith

lemma initial_contact : outerDiagonal<contact 0 (107/1000) := by
  have hs := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤107/1000 by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤107/1000 by norm_num)
  have tr := positive_trig (show (107/1000:ℝ)∈Icc 0 (7/10) by norm_num)
  have ha := ShortOuterZero.fine_axial_bounds
  have hm := mul_le_mul
    (show outerAxial-1/2≤(914575672/1000000000:ℝ) by linarith) hs tr.2.2.1
    (by norm_num : (0:ℝ)≤914575672/1000000000)
  dsimp [contact,SecondWord.SameZero.b]
  rw [ShortOuterOne.SameContact.arc_zero]
  norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7,
    HighOrderTaylor.C14,HighOrderTaylor.C12,cos10,cos8] at hc hm
  linarith [ShortMixedZero.fine_diagonal_bounds.2]

lemma original_angle {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : |x|≤7/10) (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    x∈Icc (107/1000:ℝ) (7/10) := by
  obtain ⟨hd,hcut⟩ := SecondWord.SameZero.original_contact hs ht hx hm
  have hz := SecondWord.SameZero.b_target_monotone hd.2.1 outer_zero_mem hd.1 hd.1.1
  have hlarge : (107/1000:ℝ)<x := by
    by_contra! hn
    have hh := SecondWord.SameZero.b_angle_antitone outer_zero_mem hd.2.1
      (by norm_num) hn
    linarith [initial_contact,hd.2.2.2]
  exact ⟨hlarge.le,hd.2.1.2⟩

lemma source_support {a b : ℝ} (hs : OuterState a b) :
    p 2*outerAxial≤p 2*a+(q 2-multiplier)*b := by
  apply outer_endpoints_lower hs
  · norm_num [q,multiplier]
  · exact le_rfl
  · have ha := ShortOuterZero.fine_axial_bounds
    have hd := ShortMixedZero.fine_diagonal_bounds
    norm_num [p,q,multiplier]
    linarith

lemma targetSlope_positive {x : ℝ} (hx : x∈Icc (107/1000:ℝ) (7/10)) :
    0<targetSlope x := by
  have hdom {y : ℝ} (hy : y∈Icc (107/1000:ℝ) (7/10)) : y∈Icc 0 (7/10) :=
    ⟨by linarith [hy.1],hy.2⟩
  have hc : ConcaveOn ℝ (Icc (107/1000:ℝ) (7/10)) targetSlope :=
    concave_of_deriv2
      (f' := fun y => multiplier*(-Real.sin y+rho*Real.cos y))
      (f'' := fun y => -multiplier*(Real.cos y+rho*Real.sin y))
      (fun y _ => by
        have h := (((Real.hasDerivAt_cos y).fun_add
          ((Real.hasDerivAt_sin y).const_mul rho)).const_mul multiplier).sub_const (t 2)
        convert h using 1
        funext z
        simp only [targetSlope])
      (fun y _ => by
        have h := (((Real.hasDerivAt_sin y).fun_neg).fun_add
          ((Real.hasDerivAt_cos y).const_mul rho)).const_mul multiplier
        convert h using 1
        ring)
      (fun y hy => by
        have tr := positive_trig (hdom hy)
        have hr : 0≤rho := by linarith [rho_bounds.1]
        have hp := mul_nonneg hr tr.2.2.1
        exact mul_nonpos_of_nonpos_of_nonneg (by norm_num [multiplier])
          (by linarith [tr.1]))
  apply concave_gt_of_endpoints hc hx
  · have hs := sin_lower_seven (show (0:ℝ)≤107/1000 by norm_num)
    have hc := cos_lower_six (show (0:ℝ)≤107/1000 by norm_num)
    have hp := mul_le_mul rho_bounds.1.le hs (by norm_num)
      (by linarith [rho_bounds.1] : 0≤rho)
    norm_num [targetSlope,multiplier,t] at hs hc hp ⊢
    linarith
  · have tr := CommonQuarter.cap_trig
    have hp := mul_le_mul rho_bounds.1.le tr.1.le (by norm_num)
      (by linarith [rho_bounds.1] : 0≤rho)
    norm_num [targetSlope,multiplier,t]
    linarith [tr.2.2.1]

/-- A linear functional with nonpositive primary coefficient whose tangential
derivative at the axial endpoint is nonnegative is smallest there. -/
private lemma r63_outer_axial_lower {A B X Y : ℝ} (ht : OuterState A B) (hX : X≤0)
    (hd : 0≤-X/2+Y*(outerAxial+1/2)) : X*outerAxial≤X*A+Y*B := by
  have hc := ht.2.2
  have ha := axial_circle
  have hden : 0<outerAxial+1/2 := by linarith [outer_endpoint_bounds.1]
  have h1 := mul_nonneg hd ht.1
  have h2 := mul_nonneg (neg_nonneg.mpr hX)
    (add_nonneg (sq_nonneg (A-outerAxial)) (sq_nonneg B))
  have hid : (outerAxial+1/2)*(X*A+Y*B-X*outerAxial)=
      (-X/2+Y*(outerAxial+1/2))*B+(-X)*((A-outerAxial)^2+B^2)/2 := by
    linear_combination (X/2)*(hc-ha)
  have key : 0≤(outerAxial+1/2)*(X*A+Y*B-X*outerAxial) := by
    rw [hid]
    linarith
  have := nonneg_of_mul_nonneg_right key hden
  linarith

lemma target_support {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc (107/1000:ℝ) (7/10)) :
    -multiplier*Real.sin x*outerAxial≤
      -multiplier*Real.sin x*A+(multiplier*Real.cos x-t 2)*B := by
  have tr := positive_trig (show x∈Icc 0 (7/10) from ⟨by linarith [hx.1],hx.2⟩)
  have hs := targetSlope_positive hx
  have hden : 0<outerAxial+1/2 := by linarith [outer_endpoint_bounds.1]
  have he : rho*(outerAxial+1/2)=(1/2:ℝ) := by
    have h2 : 2*(outerAxial+1/2)≠0 := by linarith
    dsimp [rho]
    rw [div_mul_eq_mul_div,one_mul,div_eq_iff h2]
    ring
  apply r63_outer_axial_lower ht
  · exact mul_nonpos_of_nonpos_of_nonneg (by norm_num [multiplier]) tr.2.2.1
  · have hp := mul_pos hs hden
    have hid : targetSlope x*(outerAxial+1/2)=
        -(-multiplier*Real.sin x)/2+(multiplier*Real.cos x-t 2)*(outerAxial+1/2) := by
      dsimp [targetSlope]
      linear_combination (multiplier*Real.sin x)*he
    linarith

lemma axial_hasDerivAt (x : ℝ) : HasDerivAt axialValue (axialFirst x) x := by
  have h := (((hasDerivAt_id x).add_const (c 2+p 2*outerAxial+multiplier/2)).fun_add
    ((Real.hasDerivAt_cos x).const_mul (multiplier/2))).fun_add
      ((Real.hasDerivAt_sin x).const_mul (multiplier*(1/2-outerAxial)))
  convert h using 1
  · funext y
    simp only [axialValue,id]
    ring
  · simp only [axialFirst]
    ring

lemma axialFirst_positive {x : ℝ} (hx : x∈Icc (107/1000:ℝ) (7/10)) : 0<axialFirst x := by
  have hspeed := SecondWord.OppositeZero.PositivePJ.speed_upper outer_zero_mem
    (show x∈Icc 0 (7/10) from ⟨by linarith [hx.1],hx.2⟩)
  norm_num [SecondWord.OppositeZero.plusSpeed,ShortOuterOne.SameContact.arc_zero] at hspeed
  dsimp [axialFirst]
  norm_num [multiplier]
  linarith

lemma axial_initial : (898077/1000000:ℝ)<axialValue (107/1000) := by
  have hs := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤107/1000 by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤107/1000 by norm_num)
  have tr := positive_trig (show (107/1000:ℝ)∈Icc 0 (7/10) by norm_num)
  have ha := ShortOuterZero.fine_axial_bounds
  have hp := mul_le_mul
    (show outerAxial-1/2≤(914575672/1000000000:ℝ) by linarith) hs tr.2.2.1
    (by norm_num : (0:ℝ)≤914575672/1000000000)
  dsimp [axialValue]
  norm_num [c,p,multiplier,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7,
    HighOrderTaylor.C14,HighOrderTaylor.C12,cos10,cos8] at hc hp ⊢
  linarith

lemma axial_lower {x : ℝ} (hx : x∈Icc (107/1000:ℝ) (7/10)) :
    (449/500:ℝ)<axialValue x := by
  have hm : MonotoneOn axialValue (Icc (107/1000:ℝ) (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (axial_hasDerivAt x).continuousAt.continuousWithinAt)
      (fun x _ => axial_hasDerivAt x)
      (fun x hx => (axialFirst_positive (Ioo_subset_Icc_self hx)).le)
  have hh := hm (by norm_num) hx hx.1
  linarith [axial_initial]

/-- Row two, at every original feasible weak owner, with no contact premise. -/
theorem original {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : |x|≤7/10) (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    (449/500:ℝ)<x+c 2+p 2*a+q 2*b-P 2*A-t 2*B := by
  have ha := original_angle hs ht hx hm
  have hsource := source_support hs
  have htarget := target_support ht ha
  have hvalue := axial_lower ha
  have tr := positive_trig (show x∈Icc 0 (7/10) from ⟨by linarith [ha.1],ha.2⟩)
  have hw := signed_width hx
  rw [abs_of_nonneg tr.2.2.1] at hw
  norm_num [Eight.forwardMargin] at hm
  rw [hw] at hm
  have hsep := mul_nonneg (show 0 ≤ multiplier by norm_num [multiplier]) (sub_nonneg.mpr hm)
  dsimp [axialValue] at hvalue
  norm_num [P] at ⊢
  simp only [multiplier] at hsource htarget hvalue hsep
  linarith only [hsource,htarget,hvalue,hsep]

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.PositiveCoefficient
