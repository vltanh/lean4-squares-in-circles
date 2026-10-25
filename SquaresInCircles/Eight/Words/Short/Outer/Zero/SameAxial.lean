module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroPositiveSpeeds
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameEvent

/-!
# Eight squares: no target-axis minimum in the three coupled favorable zero rows

The speed bound `.9628` on the whole interval (`speed_lower`) gives the ratio slope `-.536`
(`ratio_decay`). The quadratic majorants `majorant` then have negative discriminant
(`majorant_negative`), so the target derivative is negative (`target_negative`).
-/

section
/-!
## The one positive-primary-coefficient favorable zero row

One constant multiplier serves the whole feasible angle interval. Both original circle
functionals attain their lower support at the axial endpoint (`source_support`,
`target_support`). One initial value (`axial_initial`) and one derivative bound
(`axialFirst_positive`) suffice (`original`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.PositiveCoefficient
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

end SquaresInCircles.Eight.ShortOuterZero.Same.PositiveCoefficient
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Axial
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open SecondWord (U W outer_domain outer_zero_mem outer_ratio_bounds U_positive UW_circle)

lemma zero_ratio : ratio 0=PositiveCoefficient.rho := by
  have ha := ShortOuterZero.fine_axial_bounds.1
  have hp : outerAxial+1/2≠0 := by linarith
  dsimp [ratio,PositiveCoefficient.rho]
  rw [ShortOuterOne.SameContact.arc_zero]
  field_simp
  norm_num

lemma source_domain {e x u : ℝ} (he : Event.IsEvent e)
    (hx : x∈Icc e (7/10)) (hu : u∈Icc e x) : Domain 0 u := by
  have hui : u∈Icc 0 (7/10) :=
    ⟨(Event.angle_mem he).1.trans hu.1,hu.2.trans hx.2⟩
  have hm := SecondWord.SameZero.b_angle_antitone outer_zero_mem
    (Event.angle_mem he) hui hu.1
  have hm' : SecondWord.SameZero.b 0 u≤outerDiagonal := hm.trans_eq he.2
  exact ⟨outer_zero_mem,hui,⟨by linarith [SecondWord.SameZero.b_lower outer_zero_mem hui],hm'⟩⟩

lemma final_speed : (2407/2500:ℝ)<speed 0 (7/10) := by
  have tr := CommonQuarter.cap_trig
  have ha := ShortOuterZero.fine_axial_bounds.1
  have hp := mul_le_mul
    (show (914/1000:ℝ)≤outerAxial-1/2 by linarith) tr.2.2.1.le
    (by norm_num) (by linarith : 0≤outerAxial-1/2)
  dsimp [speed,SecondWord.SameZero.v]
  rw [ShortOuterOne.SameContact.arc_zero]
  nlinarith [tr.1]

lemma speed_lower {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (7/10)) :
    (2407/2500:ℝ)<speed 0 x := by
  have hdom {u : ℝ} (hu : u∈Icc e (7/10)) : u∈Icc 0 (7/10) :=
    ⟨(Event.angle_mem he).1.trans hu.1,hu.2⟩
  have hc : ConcaveOn ℝ (Icc e (7/10)) (speed 0) :=
    concave_of_deriv2
      (fun u _ => SecondWord.SameZero.v_angle_hasDerivAt 0 u)
      (fun u _ => (SecondWord.SameZero.b_angle_hasDerivAt 0 u).sub_const (1/2))
      (fun u hu => neg_nonpos.mpr (SecondWord.SameZero.v_positive outer_zero_mem (hdom hu)).le)
  exact concave_gt_of_endpoints hc hx (Event.speed_corrected he).1 final_speed

lemma ratioD_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : (557/1000:ℝ)<ratioD b := by
  have hu := U_positive (outer_domain hb)
  have ha := (outer_bounds (ShortOuterOne.SameContact.arc_state hb)).2.1
  have hupper : U b<(383/200:ℝ) := by dsimp [U]; linarith [outer_endpoint_bounds.2.1]
  have hcube : (U b)^3≤(383/200:ℝ)^3 := pow_le_pow_left₀ hu.le hupper.le 3
  change (557/1000:ℝ)<Q0/(U b)^3
  apply (lt_div_iff₀ (pow_pos hu 3)).2
  norm_num [Q0] at hcube ⊢
  linarith

lemma ratio_decay {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (7/10)) :
    ratio (contact 0 x)<1-(67/125)*(x-1073/10000) := by
  have hdom {u : ℝ} (hu : u∈Icc e (7/10)) : Domain 0 u :=
    source_domain (x := 7/10) he ⟨(Event.angle_mem he).2,le_rfl⟩ hu
  have hm : AntitoneOn (fun u => ratio (contact 0 u)+(67/125)*u) (Icc e (7/10)) :=
    antiOn_of_hasDeriv_nonpos
      (fun u hu => (((ShortOuterOne.SameContact.ratio_hasDerivAt
        (outer_domain (hdom hu).2.2)).comp u (SecondWord.SameZero.b_angle_hasDerivAt 0 u)).add
          ((hasDerivAt_id u).const_mul (67/125))).continuousAt.continuousWithinAt)
      (fun u hu => ((ShortOuterOne.SameContact.ratio_hasDerivAt
        (outer_domain (hdom (Ioo_subset_Icc_self hu)).2.2)).comp u
          (SecondWord.SameZero.b_angle_hasDerivAt 0 u)).add
            ((hasDerivAt_id u).const_mul (67/125)))
      (fun u hu => by
        have h1 := ratioD_lower (hdom (Ioo_subset_Icc_self hu)).2.2
        have h2 := speed_lower he (Ioo_subset_Icc_self hu)
        have hp := mul_lt_mul'' h1 h2 (by norm_num) (by norm_num)
        have hr := Event.ratio_slope_reserve
        simp only [speed] at hp
        linarith)
  have hh : ratio (contact 0 x)+(67/125)*x≤ratio (contact 0 e)+(67/125)*e :=
    hm ⟨le_rfl,hx.1.trans hx.2⟩ ⟨hx.1,hx.2⟩ hx.1
  rw [he.2,SecondWord.ratio_diagonal] at hh
  have heU : e<(1073/10000:ℝ) := by
    have h := he.1.2
    simp only [Event.hi] at h
    linarith
  linarith

lemma projection_bound {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    projection 0 x≤1+(131/500)*x-(479/1000)*x^2 := by
  have tr := positive_trig hx
  have hc := cos_upper_four hx.1
  have hs := Real.sin_le hx.1
  have hr := PositiveCoefficient.rho_bounds.2
  have hprod := mul_le_mul hr.le hs tr.2.2.1 (by norm_num)
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hx4 := mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)
  dsimp [projection,SecondWord.SameZero.k]
  rw [zero_ratio]
  nlinarith

lemma projection_uniform {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    projection 0 x<(517/500:ℝ) := by
  have hr := PositiveCoefficient.rho_bounds
  have hp := SecondWord.SameZero.k_positive outer_zero_mem hx
  have he : (projection 0 x)^2+
      (Real.sin x-PositiveCoefficient.rho*Real.cos x)^2=1+PositiveCoefficient.rho^2 := by
    dsimp [projection,SecondWord.SameZero.k]
    rw [zero_ratio]
    linear_combination (1+PositiveCoefficient.rho^2)*(Real.sin_sq_add_cos_sq x)
  nlinarith [sq_nonneg (Real.sin x-PositiveCoefficient.rho*Real.cos x),hr.1,hr.2]

def D (r : Row) : ℝ := (67/125)*(-p r)
def M (r : Row) : ℝ := q r-p r+(1073/10000)*D r
def A (r : Row) : ℝ := (479/1000)*M r-(733/10000)*D r
def B (r : Row) : ℝ := (131/500)*M r-D r
def C (r : Row) : ℝ := M r+(131/500)*P r-t r

def majorant (r : Row) (x : ℝ) : ℝ := C r+B r*x-A r*x^2

lemma majorant_negative (r : Row) (hr : r=1 ∨ r=3) (x : ℝ) : majorant r x<0 := by
  have ha : 0<A r := by rcases hr with rfl | rfl <;> norm_num [A,M,D,p,q]
  have hdisc : 4*A r*C r+(B r)^2<0 := by
    rcases hr with rfl | rfl <;> norm_num [A,B,C,M,D,p,q,P,t]
  have hsq := sq_nonneg (2*A r*x-B r)
  dsimp [majorant]
  nlinarith

lemma curved_target_negative (r : Row) (hr : r=1 ∨ r=3) {x : ℝ}
    (hd : Domain 0 x) : targetFirst r 0 x<0 := by
  obtain ⟨e,he⟩ := Event.exists_event
  have hx : x∈Icc e (7/10) := ⟨Event.before_contact he hd,hd.2.1.2⟩
  have hdecay := ratio_decay he hx
  have hp : 0< -p r := by rcases hr with rfl | rfl <;> norm_num [p]
  have hP : 0≤P r := (coefficient_signs r).2.2
  have hl : l r (contact 0 x)<M r-D r*x := by
    have hh := mul_lt_mul_of_pos_left hdecay hp
    dsimp [l,M,D]
    nlinarith
  have hk := projection_bound hd.2.1
  have hk0 := (SecondWord.SameZero.k_positive hd.1 hd.2.1).le
  have hL0 : 0≤M r-D r*x := by linarith [l_positive r hd.2.2]
  have hprod := mul_le_mul hl.le hk hk0 hL0
  have hD0 : 0≤D r := by dsimp [D]; positivity
  have hcubic := mul_nonneg (show 0≤(7/10:ℝ)-x by linarith [hd.2.1.2])
    (mul_nonneg hD0 (sq_nonneg x))
  have hR := mul_le_mul_of_nonneg_left PositiveCoefficient.rho_bounds.2.le hP
  have hupper : targetFirst r 0 x≤ majorant r x := by
    dsimp [targetFirst]
    rw [zero_ratio]
    dsimp [majorant,A,B,C]
    nlinarith
  exact hupper.trans_lt (majorant_negative r hr x)

theorem target_negative (r : Row) (hr : Coupled r) {x : ℝ}
    (hd : Domain 0 x) : targetFirst r 0 x<0 := by
  by_cases hz : r=0
  · subst r
    have hk := projection_uniform hd.2.1
    norm_num [targetFirst,l,p,q,P,t]
    linarith
  · have hcurved : r=1 ∨ r=3 := by
      revert hr hz
      fin_cases r <;> simp [Coupled]
    exact curved_target_negative r hcurved hd

end SquaresInCircles.Eight.ShortOuterZero.Same.Axial
end
end
end
