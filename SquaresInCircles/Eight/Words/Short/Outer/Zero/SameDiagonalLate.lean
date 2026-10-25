module

public import SquaresInCircles.Eight.Words.Common.ZeroSame
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroOuter
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameAxial
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameDiagonalReferences

/-!
# Eight squares: the increasing target derivative on the source diagonal

Its derivative is positive on the whole rotated-circle branch (`targetSlopeD_positive`); the
negative-`Z` portion uses four bounds (`negative_Z_factor`). The comparison at `.3`
(`late_slope`) therefore excludes every later source-diagonal minimum by left descent
(`original_late_slope`).
-/

section
/-!
## Four unfavorable same-sign outer zero owners

One constant multiplier gives a strictly concave full-circle envelope.
Three families use its two endpoint values. The fourth uses the actual
diagonal support up to its intrinsic derivative zero and the same full
circle envelope afterwards. The supports agree exactly at that event.
Every original weak owner has cost greater than `1.03`.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortOuterZero.Unfavorable

open CommonQuarter CorePairGeometry WrongWordCircleSupport

abbrev Row := Fin 4
def c : Row → ℝ := ![-6130/100000,27086/100000,-75097/100000,74349/100000]
def p : Row → ℝ := ![0,-13422/100000,0,-33147/100000]
def q : Row → ℝ := ![99940/100000,103828/100000,71553/100000,113360/100000]
def P : Row → ℝ := ![0,9133/100000,-51554/100000,19335/100000]
def t : Row → ℝ := ![94766/100000,88074/100000,119909/100000,76744/100000]
def intercept (r : Row) : ℝ := c r+p r*outerAxial
def F (r : Row) : ℝ → ℝ := full (intercept r) (P r) (t r) 2
def D (r : Row) : ℝ → ℝ := diagonal (intercept r) (P r) (t r) 2
def initialCeiling : Row → ℝ := ![113/100,309/250,179/250,1387/1000]
def finalCeiling : Row → ℝ := ![707/500,61/40,841/1000,1667/1000]

lemma coefficients (r : Row) : p r≤0 ∧ q r<2 ∧ 0<t r ∧ (P r)^2+(t r)^2<4 := by
  fin_cases r <;> norm_num [p,q,P,t]

lemma initial_trig : (3694/12500:ℝ)<Real.sin (3/10:ℝ) ∧
    Real.sin (3/10:ℝ)<295521/1000000 ∧
    (119417/125000:ℝ)<Real.cos (3/10:ℝ) ∧ Real.cos (3/10:ℝ)<955337/1000000 := by
  have hs := sin_lower_seven (x := (3/10:ℝ)) (by norm_num)
  have hu := sin_upper_five (x := (3/10:ℝ)) (by norm_num)
  have hc := cos_lower_six (x := (3/10:ℝ)) (by norm_num)
  have hk := Arithmetic.cos_le_cos8 (x := (3/10:ℝ)) (by norm_num)
  norm_num [Arithmetic.cos8] at hs hu hc hk
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma norm_endpoints (r : Row) :
    N (P r) (t r) 2 (3/10)< initialCeiling r ∧
    N (P r) (t r) 2 (7/10)<finalCeiling r := by
  have hpq : (P r)^2+(t r)^2<(2:ℝ)^2 :=
    lt_of_lt_of_eq (coefficients r).2.2.2 (by norm_num)
  have h₀ := CircularNorm.norm_sq (energy_pos (p := P r) (q := t r)
    (l := (2:ℝ)) (x := (3/10:ℝ)) (by norm_num) hpq).le
  have h₁ := CircularNorm.norm_sq (energy_pos (p := P r) (q := t r)
    (l := (2:ℝ)) (x := (7/10:ℝ)) (by norm_num) hpq).le
  change (N (P r) (t r) 2 (3/10))^2=_ at h₀
  change (N (P r) (t r) 2 (7/10))^2=_ at h₁
  have ts := initial_trig
  have te := CommonQuarter.cap_trig
  dsimp [CircularNorm.energy,mass] at h₀ h₁
  constructor
  · apply lt_of_pow_lt_pow_left₀ 2 (by fin_cases r <;> norm_num [initialCeiling])
    rw [h₀]
    fin_cases r <;> norm_num [P,t,initialCeiling] <;>
      linarith only [ts.1,ts.2.1,ts.2.2.1,ts.2.2.2]
  · apply lt_of_pow_lt_pow_left₀ 2 (by fin_cases r <;> norm_num [finalCeiling])
    rw [h₁]
    fin_cases r <;> norm_num [P,t,finalCeiling] <;>
      linarith only [te.1,te.2.1,te.2.2.1,te.2.2.2]

lemma F_initial (r : Row) (h2 : r≠2) : (103/100:ℝ)<F r (3/10) := by
  have hn := mul_lt_mul_of_pos_left (norm_endpoints r).1
    (show 0<CommonQuarter.radius by linarith [radius_bounds.1])
  have hceiling : 0 < initialCeiling r := by fin_cases r <;> norm_num [initialCeiling]
  have hR := mul_lt_mul_of_pos_right radius_bounds.2 hceiling
  have ha := mul_le_mul_of_nonpos_left outer_endpoint_bounds.2.1.le (coefficients r).1
  have ht := initial_trig
  rw [F,full_expression]
  dsimp [intercept]
  fin_cases r
  · norm_num [c,p,P,t,initialCeiling] at hn hR ha ⊢; linarith [ht.1,ht.2.2.1]
  · norm_num [c,p,P,t,initialCeiling] at hn hR ha ⊢; linarith [ht.1,ht.2.2.1]
  · exact absurd rfl h2
  · norm_num [c,p,P,t,initialCeiling] at hn hR ha ⊢; linarith [ht.1,ht.2.2.1]

lemma F_final (r : Row) : (103/100:ℝ)<F r (7/10) := by
  have hn := mul_lt_mul_of_pos_left (norm_endpoints r).2
    (show 0<CommonQuarter.radius by linarith [radius_bounds.1])
  have hceiling : 0<finalCeiling r := by fin_cases r <;> norm_num [finalCeiling]
  have hR := mul_lt_mul_of_pos_right radius_bounds.2 hceiling
  have ha := mul_le_mul_of_nonpos_left outer_endpoint_bounds.2.1.le (coefficients r).1
  have ht := CommonQuarter.cap_trig
  rw [F,full_expression]
  dsimp [intercept]
  fin_cases r <;> norm_num [c,p,P,t,finalCeiling] at hn hR ha ⊢ <;>
    linarith [ht.1,ht.2.2.1]

lemma F_concave (r : Row) : ConcaveOn ℝ (Icc 0 (7/10)) (F r) :=
  full_concave (by norm_num) (lt_of_lt_of_eq (coefficients r).2.2.2 (by norm_num))

lemma F_lower (r : Row) (h2 : r≠2) {x : ℝ} (hx : x∈Icc (3/10) (7/10)) :
    (103/100:ℝ)<F r x :=
  concave_gt_of_endpoints
    ((F_concave r).subset (Icc_subset_Icc (by norm_num) le_rfl) (convex_Icc _ _))
    hx (F_initial r h2) (F_final r)

lemma D_hasDerivAt (r : Row) (x : ℝ) :
    HasDerivAt (D r) (1-2*(outerDiagonal-1/2)*(Real.cos x-Real.sin x)) x := by
  have hh : HasDerivAt (fun y => y+(intercept r+1+(t r-P r)*outerDiagonal)-
      2*(outerDiagonal-1/2)*(Real.sin y+Real.cos y))
      (1-2*(outerDiagonal-1/2)*(Real.cos x+-Real.sin x)) x :=
    ((hasDerivAt_id' x).add_const (intercept r+1+(t r-P r)*outerDiagonal)).sub
      (((Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)).const_mul
        (2*(outerDiagonal-1/2)))
  have hfun : D r=fun y => y+(intercept r+1+(t r-P r)*outerDiagonal)-
      2*(outerDiagonal-1/2)*(Real.sin y+Real.cos y) := by
    funext y
    simp only [D,WrongWordCircleSupport.diagonal,base,X,Y]
    ring
  rw [hfun]
  exact hh.congr_deriv (by ring)

lemma D_monotone (r : Row) : MonotoneOn (D r) (Icc 0 (7/10)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (D_hasDerivAt r x).continuousAt.continuousWithinAt
  · exact fun x _ => D_hasDerivAt r x
  · intro x hx
    have ht := positive_trig (Ioo_subset_Icc_self hx)
    have hp := mul_le_mul_of_nonneg_left
      (show Real.cos x-Real.sin x≤1 by linarith [ht.2.1,ht.2.2.1])
      (show 0≤2*(outerDiagonal-1/2) by linarith [outer_endpoint_bounds.2.2.1])
    linarith [outer_endpoint_bounds.2.2.2]

lemma D_third_initial : (103/100:ℝ)<D 2 (3/10) := by
  have ht := initial_trig
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hm : Real.sin (3/10:ℝ)+Real.cos (3/10:ℝ)<(1251/1000:ℝ) := by
    linarith [ht.2.1,ht.2.2.2]
  have hp := mul_le_mul_of_nonpos_left hm.le
    (show 1-2*outerDiagonal≤0 by linarith [hd.1])
  norm_num [D,WrongWordCircleSupport.diagonal,base,X,Y,intercept,c,p,P,t]
  nlinarith [hd.1,hd.2]

lemma D_third_lower {x : ℝ} (hx : x∈Icc (3/10) (7/10)) : (103/100:ℝ)<D 2 x :=
  D_third_initial.trans_le (D_monotone 2 (by norm_num) ⟨by linarith [hx.1],hx.2⟩ hx.1)

lemma third_initial_slope : diagonalSlope (P 2) (t 2) 2 (3/10)<0 := by
  have ht := initial_trig
  norm_num [diagonalSlope,X,Y,P,t]
  linarith [ht.2.1,ht.2.2.1]

lemma third_primary_neg {x : ℝ} (hx : x∈Icc (3/10) (7/10)) : X (P 2) 2 x<0 := by
  have hs := sin_mono (by norm_num) ⟨by linarith [hx.1],hx.2⟩ hx.1
  norm_num [X,P]
  linarith [initial_trig.1]

lemma F_third_after_event {x : ℝ} (hx : x∈Icc (3/10) (7/10))
    (hd : 0<diagonalSlope (P 2) (t 2) 2 x) : (103/100:ℝ)<F 2 x := by
  have hc : Continuous (diagonalSlope (P 2) (t 2) 2) := by
    unfold diagonalSlope X Y
    fun_prop
  obtain ⟨v,hv,he⟩ := intermediate_value_Icc hx.1 hc.continuousOn
    (show (0:ℝ)∈Icc (diagonalSlope (P 2) (t 2) 2 (3/10))
      (diagonalSlope (P 2) (t 2) 2 x) from ⟨third_initial_slope.le,hd.le⟩)
  have hv' : v∈Icc 0 (7/10) := ⟨by linarith [hv.1],hv.2.trans hx.2⟩
  have heq : F 2 v=D 2 v :=
    full_at_diagonal_event (by norm_num) (by norm_num [P,t]) hv' he
  have hleft : (103/100:ℝ)<F 2 v := by
    rw [heq]
    exact D_third_lower ⟨hv.1,hv.2.trans hx.2⟩
  have hconc := (F_concave 2).subset (Icc_subset_Icc hv'.1 le_rfl) (convex_Icc _ _)
  exact concave_gt_of_endpoints hconc ⟨hv.2,hx.2⟩ hleft (F_final 2)

lemma original_angle {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B (-1) (-1) φ) : (3/10:ℝ)<φ := by
  have hs' : State .outer a b := by simpa [State] using hs
  have hp := negative_secondary_positive_angle (Or.inl hs') ht hφ hm
  have hx : φ∈Icc 0 (7/10) := ⟨hp.le,(abs_le.mp hφ).2⟩
  have tr := positive_trig hx
  have hproj := outer_diagonal_upper ht tr.2.2.1
    (show Real.sin φ≤Real.cos φ by linarith [tr.1,tr.2.2.2.1])
  have hw : pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
    ring
  norm_num [forwardMargin] at hm
  rw [hw] at hm
  have hcut : 0≤ShortMixedZero.NegativeContact.cut φ := by
    dsimp [ShortMixedZero.NegativeContact.cut,ShortMixedZero.NegativeContact.m]
    nlinarith [hs.1]
  by_contra! hn
  have hsmall : φ≤ShortMixedZero.NegativeContact.start := by
    linarith [show (3/10:ℝ)<ShortMixedZero.NegativeContact.start by norm_num [ShortMixedZero.NegativeContact.start]]
  have hmono := ShortMixedZero.NegativeContact.m_monotone hx
    (by norm_num [ShortMixedZero.NegativeContact.start]) hsmall
  have hh := mul_le_mul_of_nonneg_left hmono
    (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1])
  have hneg := ShortMixedZero.NegativeContact.cut_start_neg
  dsimp [ShortMixedZero.NegativeContact.cut] at hcut hneg
  linarith

lemma actual_target_support (r : Row) {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc (3/10) (7/10)) :
    (103/100:ℝ)<base (intercept r) 2 x+X (P r) 2 x*A+Y (t r) 2 x*B := by
  have hpq : (P r)^2+(t r)^2<(2:ℝ)^2 :=
    lt_of_lt_of_eq (coefficients r).2.2.2 (by norm_num)
  have hfull : F r x≤base (intercept r) 2 x+X (P r) 2 x*A+Y (t r) 2 x*B := by
    have hh := outer_circle_lower (X := X (P r) 2 x) (Y := Y (t r) 2 x) ht
    rw [← N_eq_sqrt (by norm_num) hpq] at hh
    dsimp [F,full]
    linarith
  by_cases h2 : r=2
  · subst r
    by_cases hd : 0<diagonalSlope (P 2) (t 2) 2 x
    · exact (F_third_after_event hx hd).trans_le hfull
    · have hdiag := outer_diagonal_lower ht (third_primary_neg hx).le
        (show Y (t 2) 2 x-X (P 2) 2 x≤0 from le_of_not_gt hd)
      have hh := D_third_lower hx
      dsimp [D,WrongWordCircleSupport.diagonal] at hh
      linarith
  · exact (F_lower r h2 hx).trans_le hfull

theorem original_cost (r : Row) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B (-1) (-1) φ) :
    (103/100:ℝ)<φ+c r+p r*a-q r*b-P r*A+t r*B := by
  have hx : φ∈Icc (3/10) (7/10) :=
    ⟨(original_angle hs ht hφ hm).le,(abs_le.mp hφ).2⟩
  have hc := coefficients r
  have hsource := outer_axial_lower hs hc.1
    (show 0≤(outerAxial+1/2)*(2-q r)-p r/2 by
      have hh := mul_nonneg (show 0≤outerAxial+1/2 by linarith [outer_endpoint_bounds.1])
        (show 0≤2-q r by linarith [hc.2.1])
      linarith)
  have htarget := actual_target_support r ht hx
  have tr := positive_trig (show φ∈Icc 0 (7/10) from ⟨by linarith [hx.1],hx.2⟩)
  have hw : pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
    ring
  norm_num [forwardMargin] at hm
  rw [hw] at hm
  dsimp [base,intercept,X,Y] at htarget
  nlinarith only [hsource,htarget,hm]

end SquaresInCircles.Eight.ShortOuterZero.Unfavorable
end
end
end

section
/-!
## The full early source-diagonal geometry

The actual rotated circle
is used from its initial event through .3. Its support-factor derivative
increases on that complete interval, giving B' > .91 and B'' < .2.
The initial speed is bounded by .942 at the actual event.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open SecondWord.SameZero.PJ.Diagonal (z₀)

lemma early_angle {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    x∈Icc start (7/10) := by
  have hge := (event_geometry he).1.1
  exact ⟨hge.1.trans hx.1,by linarith [hx.2]⟩

lemma early_geometry {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) : Geometry x := by
  have heG := event_geometry he
  have hxa := early_angle he hx
  have hm := SecondWord.SameZero.PJ.Diagonal.height_monotone heG.1.1 hxa hx.1
  have h0 : SecondWord.SameZero.PJ.Diagonal.height e=0 := heG.2
  rw [h0] at hm
  exact ⟨hxa,hm⟩

lemma early_Z {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    0<Z x ∧ Z x<(293/1000:ℝ) := by
  have hr := SecondWord.SameZero.PJ.Diagonal.radical_data (early_angle he hx)
  have hs := Real.sin_le (show 0≤x from (Event.angle_mem he).1.trans hx.1)
  have hz : 0<Z x := by
    dsimp [Z,SecondWord.SameZero.PJ.Diagonal.Z,z₀]
    linarith [ShortMixedZero.fine_diagonal_bounds.1,hx.2]
  exact ⟨hz,hr.2.1⟩

lemma early_Y {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    (1957/1000:ℝ)<Y x := by
  have hinit : (1957/1000:ℝ)<Y e := by
    have hbox : (1957/1000:ℝ)<(eventY he).lo := by
      dsimp [eventY,eventRad,eventZ,Event.eventSin]
      diagonal_reference_arithmetic
    exact hbox.trans_le (eventY he).mem.1
  have hm : MonotoneOn Y (Icc e (3/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun u hu => (SecondWord.SameZero.PJ.Diagonal.Y_hasDerivAt
        (early_angle he hu)).continuousAt.continuousWithinAt)
      (fun u hu => SecondWord.SameZero.PJ.Diagonal.Y_hasDerivAt
        (early_angle he (Ioo_subset_Icc_self hu)))
      (fun u hu => by
        have hz := (early_Z he (Ioo_subset_Icc_self hu)).1
        have hy := (SecondWord.SameZero.PJ.Diagonal.radical_data
          (early_angle he (Ioo_subset_Icc_self hu))).2.2.1
        have hc := (positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem
          (early_angle he (Ioo_subset_Icc_self hu)))).1
        exact div_nonneg (mul_nonneg hz.le (by linarith)) (by linarith))
  exact hinit.trans_le (hm ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1)

lemma early_coordinates {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    (37/20:ℝ)<horizontal x ∧ horizontal x<383/200 ∧
      (1/2:ℝ)≤vertical x ∧ (4919/10000:ℝ)<factor x := by
  have hxa := early_angle he hx
  have hg := early_geometry he hx
  have hU := SecondWord.SameZero.PJ.Diagonal.horizontal_antitone hxa
    (by norm_num [start,SecondWord.SameZero.PJ.Diagonal.start]) hx.2
  have hUl := three_tenths.1.trans_le hU
  have hUu := (SecondWord.SameZero.PJ.Diagonal.whole_bounds hxa).2.1
  have hV : (1/2:ℝ)≤vertical x := by
    have hg2 : 0≤SecondWord.SameZero.PJ.Diagonal.height x := hg.2
    simp only [SecondWord.SameZero.PJ.Diagonal.height] at hg2
    show (1/2:ℝ)≤SecondWord.SameZero.PJ.Diagonal.vertical x
    linarith
  have hcos : Real.cos x<(9943/10000:ℝ) := by
    have helo : Event.lo≤x := he.1.1.le.trans hx.1
    have hh := cos_anti (by norm_num [Event.lo])
      (SecondWord.SameZero.PJ.Diagonal.angle_mem hxa) helo
    have ht := HighOrderTaylor.cos_le_C16 (show 0≤Event.lo by norm_num [Event.lo])
    have href : HighOrderTaylor.C16 Event.lo<(9943/10000:ℝ) := by
      norm_num [Event.lo,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,cos10,cos8]
    exact hh.trans_lt (ht.trans_lt href)
  have hy := early_Y he hx
  have hratio : Real.cos x/Y x<(5081/10000:ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0<Y x)).2
    linarith
  refine ⟨hUl,hUu,hV,?_⟩
  show (4919/10000:ℝ)<SecondWord.SameZero.PJ.Diagonal.factor x
  simp only [SecondWord.SameZero.PJ.Diagonal.factor]
  have hr : Real.cos x/SecondWord.SameZero.PJ.Diagonal.Y x<(5081/10000:ℝ) := hratio
  linarith

def factorDD (x : ℝ) : ℝ := Real.cos x/(Y x)^5*
  ((Y x)^4-((Real.cos x)^2+3*Z x*Real.sin x)*(Y x)^2-3*(Z x)^2*(Real.cos x)^2)

lemma factorD_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt factorD (factorDD x) x := by
  have hY := SecondWord.SameZero.PJ.Diagonal.Y_hasDerivAt hx
  have hy : 0<Y x := by linarith [(SecondWord.SameZero.PJ.Diagonal.radical_data hx).2.2.1]
  have hc := (SecondWord.SameZero.PJ.Diagonal.radical_data hx).2.2.2.2
  have ht := Real.sin_sq_add_cos_sq x
  have hn : HasDerivAt (fun y => Real.sin y*(Q0-1-z₀^2)+z₀*(1+(Real.sin y)^2))
      (Real.cos x*(Q0-1-z₀^2+2*z₀*Real.sin x)) x := by
    have h := ((Real.hasDerivAt_sin x).mul_const (Q0-1-z₀^2)).fun_add
      ((((Real.hasDerivAt_sin x).fun_pow 2).const_add 1).const_mul z₀)
    convert h using 1
    push_cast
    ring
  have key : Real.cos x*(Q0-1-z₀^2+2*z₀*Real.sin x)*(Y x)^2-
      3*(Real.sin x*(Q0-1-z₀^2)+z₀*(1+(Real.sin x)^2))*Z x*Real.cos x=
      Real.cos x*((Y x)^4-((Real.cos x)^2+3*Z x*Real.sin x)*(Y x)^2-
        3*(Z x)^2*(Real.cos x)^2) := by
    simp only [Z,SecondWord.SameZero.PJ.Diagonal.Z] at hc ⊢
    linear_combination Real.cos x*((Y x)^2+3*(z₀-Real.sin x)^2)*ht+
      Real.cos x*(3*(z₀-Real.sin x)*Real.sin x-(Y x)^2)*hc
  refine (hn.fun_div (hY.fun_pow 3) (pow_ne_zero 3 hy.ne')).congr_deriv ?_
  have hY0 : SecondWord.SameZero.PJ.Diagonal.Y x≠0 := hy.ne'
  rw [show ∀ a : ℝ, (a*SecondWord.SameZero.PJ.Diagonal.Y x^3-
      (Real.sin x*(Q0-1-z₀^2)+z₀*(1+(Real.sin x)^2))*
        (((3:ℕ):ℝ)*SecondWord.SameZero.PJ.Diagonal.Y x^(3-1)*
          (SecondWord.SameZero.PJ.Diagonal.Z x*Real.cos x/SecondWord.SameZero.PJ.Diagonal.Y x)))/
      (SecondWord.SameZero.PJ.Diagonal.Y x^3)^2=
      (a*(Y x)^2-3*(Real.sin x*(Q0-1-z₀^2)+z₀*(1+(Real.sin x)^2))*Z x*Real.cos x)/(Y x)^5
    from fun a => by field_simp; push_cast; ring]
  rw [key]
  simp only [factorDD]
  ring

lemma factorDD_positive {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    0<factorDD x := by
  have hxa := early_angle he hx
  have hz := early_Z he hx
  have hy := early_Y he hx
  have tr := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hxa)
  have hs : Real.sin x<(37/125:ℝ) := by
    have hm := sin_mono (SecondWord.SameZero.PJ.Diagonal.angle_mem hxa) (by norm_num) hx.2
    linarith [Unfavorable.initial_trig.2.1]
  have hz2 : (Z x)^2<(43/500:ℝ) := by nlinarith [hz.1,hz.2]
  have hc2 : (Real.cos x)^2≤1 := by nlinarith [tr.1,tr.2.1]
  have hzc := mul_le_mul hz2.le hc2 (sq_nonneg (Real.cos x)) (by norm_num)
  have hzs := mul_le_mul hz.2.le hs.le tr.2.2.1 (by norm_num)
  have hcoef : (Real.cos x)^2+3*Z x*Real.sin x<(1261/1000:ℝ) := by nlinarith
  have hY2 : (3829/1000:ℝ)<(Y x)^2 := by nlinarith
  have hupper := mul_le_mul_of_nonneg_right hcoef.le (sq_nonneg (Y x))
  have hproduct := mul_nonneg
    (show 0≤(Y x)^2-3829/1000 by linarith)
    (show 0≤(Y x)^2+3829/1000-1261/1000 by nlinarith)
  have hbrace : 0<(Y x)^4-((Real.cos x)^2+3*Z x*Real.sin x)*(Y x)^2-
      3*(Z x)^2*(Real.cos x)^2 := by nlinarith
  dsimp [factorDD]
  exact mul_pos (div_pos (by linarith [tr.1]) (pow_pos (by linarith : 0<Y x) 5)) hbrace

lemma early_factorD_upper {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    factorD x<(81/500:ℝ) := by
  have hm : MonotoneOn factorD (Icc e (3/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun u hu => (factorD_hasDerivAt (early_angle he hu)).continuousAt.continuousWithinAt)
      (fun u hu => factorD_hasDerivAt (early_angle he (Ioo_subset_Icc_self hu)))
      (fun u hu => (factorDD_positive he (Ioo_subset_Icc_self hu)).le)
  exact (hm hx ⟨hx.1.trans hx.2,le_rfl⟩ hx.2).trans_lt three_tenths.2.1

lemma factorD_positive {x : ℝ} (hx : x∈Icc start (7/10)) : 0<factorD x := by
  have hr := SecondWord.SameZero.PJ.Diagonal.radical_data hx
  have tr := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx)
  have hz : 0<z₀ ∧ z₀<(2/5:ℝ) := by
    dsimp [z₀]
    constructor <;> linarith [ShortMixedZero.fine_diagonal_bounds.1,ShortMixedZero.fine_diagonal_bounds.2]
  have hcoef : 0<Q0-1-z₀^2 := by norm_num [Q0]; nlinarith
  have h1 := mul_nonneg tr.2.2.1 hcoef.le
  have h2 := mul_pos hz.1 (show 0<1+(Real.sin x)^2 by nlinarith [sq_nonneg (Real.sin x)])
  exact div_pos (by linarith) (pow_pos (by linarith [hr.2.2.1]) 3)

lemma early_speed_acceleration {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    (91/100:ℝ)<speed x ∧ acceleration x<(1/5:ℝ) := by
  have hc := early_coordinates he hx
  have hfd := early_factorD_upper he hx
  have hfd0 := factorD_positive (early_angle he hx)
  have hp := mul_lt_mul'' hc.1 hc.2.2.2 (by norm_num) (by norm_num)
  have hf2 : (4919/10000:ℝ)^2≤(factor x)^2 := by nlinarith [hc.2.2.2]
  have hneg := mul_le_mul hc.2.2.1 hf2 (by norm_num) (by linarith [hc.2.2.1])
  have hpos := mul_le_mul hc.2.1.le hfd.le hfd0.le (by norm_num)
  show (91/100:ℝ)<SecondWord.SameZero.PJ.Diagonal.speed x ∧
    SecondWord.SameZero.PJ.Diagonal.acceleration x<(1/5:ℝ)
  simp only [SecondWord.SameZero.PJ.Diagonal.speed,
    SecondWord.SameZero.PJ.Diagonal.acceleration]
  exact ⟨by linarith,by linarith⟩

end SquaresInCircles.Eight.ShortOuterZero.Same.Diagonal
end
end
end

section
/-!
## The integrated early diagonal cost

The .91 lower speed,
.942 initial upper speed, and .2 upper acceleration are integrated on
one complete interval. The target-label tangent then yields exactly the
quadratic in the written proof, whose increment is nonnegative in every
coupled row.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open SecondWord (outer_domain outer_zero_mem)

lemma early_height_bounds {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    (91/100)*(x-e)≤height x ∧ height x≤(471/500)*(x-e)+(1/10)*(x-e)^2 := by
  have hm : MonotoneOn (fun u => height u-(91/100)*u) (Icc e (3/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun u hu => ((SecondWord.SameZero.PJ.Diagonal.height_hasDerivAt
        (early_angle he hu)).fun_sub ((hasDerivAt_id' u).const_mul (91/100))).continuousAt.continuousWithinAt)
      (fun u hu => (SecondWord.SameZero.PJ.Diagonal.height_hasDerivAt
        (early_angle he (Ioo_subset_Icc_self hu))).fun_sub ((hasDerivAt_id' u).const_mul (91/100)))
      (fun u hu => by
        have h := (early_speed_acceleration he (Ioo_subset_Icc_self hu)).1
        simp only [mul_one]
        linarith)
  have hmono : height e-(91/100)*e≤height x-(91/100)*x := hm ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1
  have ht : -height e+(-speed e)*(x-e)+(-(1/5:ℝ))/2*(x-e)^2≤-height x :=
    curvature_tangent (f := fun u => -height u) (d := fun u => -speed u)
      (dd := fun u => -acceleration u) (κ := -(1/5:ℝ)) hx ⟨le_rfl,hx.1.trans hx.2⟩
      (fun u hu => (SecondWord.SameZero.PJ.Diagonal.height_hasDerivAt (early_angle he hu)).fun_neg)
      (fun u hu => (SecondWord.SameZero.PJ.Diagonal.speed_hasDerivAt (early_angle he hu)).fun_neg)
      (fun u hu => by linarith [(early_speed_acceleration he hu).2])
  have h0 : height e=0 := (event_geometry he).2
  rw [h0] at hmono ht
  have hs := mul_le_mul_of_nonneg_right (initial_speed he).le (sub_nonneg.mpr hx.1)
  exact ⟨by linarith,by linarith⟩

def initialTargetSlope (r : Row) : ℝ := t r-P r*ratio 0
def upperTargetSlope (r : Row) : ℝ := t r-(5223/20000)*P r

def linearGain (r : Row) : ℝ := 1-(471/500)*upperTargetSlope r
def quadraticGain (r : Row) : ℝ :=
  (557/2000)*P r*(91/100)^2-(1/10)*upperTargetSlope r

lemma target_slope_bounds (r : Row) (hr : Coupled r) :
    0< initialTargetSlope r ∧ initialTargetSlope r≤upperTargetSlope r := by
  have hp := (coefficient_signs r).2.2
  have hlo := mul_le_mul_of_nonneg_left PositiveCoefficient.rho_bounds.1.le hp
  have hhi := mul_le_mul_of_nonneg_left PositiveCoefficient.rho_bounds.2.le hp
  dsimp [initialTargetSlope,upperTargetSlope]
  rw [Axial.zero_ratio]
  constructor
  · fin_cases r <;> norm_num [Coupled] at hr <;> norm_num [P,t] at hhi ⊢ <;> linarith
  · linarith

lemma gain_coefficients (r : Row) (hr : Coupled r) :
    quadraticGain r≤0 ∧ 0<linearGain r+(193/1000)*quadraticGain r := by
  fin_cases r <;> norm_num [Coupled] at hr <;>
    norm_num [linearGain,quadraticGain,upperTargetSlope,P,t]

lemma gain_nonnegative (r : Row) (hr : Coupled r) {u : ℝ}
    (hu : u∈Icc (0:ℝ) (193/1000)) : 0≤linearGain r*u+quadraticGain r*u^2 := by
  have hc := gain_coefficients r hr
  have hs := mul_nonneg hu.1 (sub_nonneg.mpr hu.2)
  have hq := mul_le_mul_of_nonpos_left
    (show u^2≤(193/1000)*u by nlinarith) hc.1
  have hl := mul_nonneg hc.2.le hu.1
  nlinarith

lemma target_tangent (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    -P r*outerAxial-initialTargetSlope r*B+(557/2000)*P r*B^2≤
      -P r*arc B-t r*B := by
  have ht := curvature_tangent
    (f := fun u => -P r*arc u-t r*u)
    (d := fun u => P r*ratio u-t r)
    (dd := fun u => P r*ShortOuterOne.SameContact.ratioD u)
    (κ := (557/1000)*P r) hB outer_zero_mem
    (fun u hu => by
      have h := ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hu)).const_mul
        (-P r)).fun_sub ((hasDerivAt_id' u).const_mul (t r))
      convert h using 1
      ring)
    (fun u hu => ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hu)).const_mul
      (P r)).sub_const (t r))
    (fun u hu => by
      have hh := mul_le_mul_of_nonneg_left (Axial.ratioD_lower hu).le (coefficient_signs r).2.2
      linarith)
  rw [ShortOuterOne.SameContact.arc_zero] at ht
  dsimp [initialTargetSlope]
  linarith

/-- All three coupled rows, including the closed initial point. -/
theorem early_lower (r : Row) (hr : Coupled r) {e x : ℝ}
    (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    (11226/12500:ℝ)<cost r x := by
  obtain ⟨u,hu_def⟩ : ∃ u, u=x-e := ⟨_,rfl⟩
  have hu : u∈Icc (0:ℝ) (193/1000) := by
    rw [hu_def]
    constructor
    · exact sub_nonneg.mpr hx.1
    · have hl : (107/1000:ℝ)<e := by
        have h := he.1.1
        simp only [Event.lo] at h
        linarith
      linarith [hx.2]
  have hB := SecondWord.SameZero.PJ.Diagonal.target_mem (early_geometry he hx)
  have hs := early_height_bounds he hx
  rw [← hu_def] at hs
  have hs0 : 0≤(91/100)*u := mul_nonneg (by norm_num) hu.1
  have hBsquare : ((91/100)*u)^2≤(height x)^2 :=
    pow_le_pow_left₀ hs0 hs.1 2
  have hm := target_slope_bounds r hr
  have hupper : 0≤(471/500)*u+(1/10)*u^2 :=
    add_nonneg (mul_nonneg (by norm_num) hu.1) (by positivity)
  have hneg := mul_le_mul_of_nonneg_left hs.2 hm.1.le
  have hnegU := mul_le_mul_of_nonneg_right hm.2 hupper
  have hquad := mul_le_mul_of_nonneg_left hBsquare
    (show 0≤(557/2000)*P r by exact mul_nonneg (by norm_num) (coefficient_signs r).2.2)
  have htarget := target_tangent r hB
  have hinitial := Event.initial_cost r hr he
  have hgain := gain_nonnegative r hr hu
  dsimp [linearGain,quadraticGain] at hgain
  dsimp [cost]
  linarith [htarget,hinitial,hgain,hneg,hnegU,hquad]

end SquaresInCircles.Eight.ShortOuterZero.Same.Diagonal
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open SecondWord.SameZero.PJ.Diagonal (z₀)

def targetSlopeD (r : Row) (x : ℝ) : ℝ :=
  (q r-p r)*Z x/horizontal x+
    ((q r-p r)*Real.sin x+P r)*Q0*factor x/(horizontal x)^2

lemma targetSlope_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt (targetSlope r) (targetSlopeD r x) x := by
  have hU := SecondWord.SameZero.PJ.Diagonal.horizontal_hasDerivAt hx
  have hV : HasDerivAt vertical (horizontal x*factor x) x := by
    convert (SecondWord.SameZero.PJ.Diagonal.height_hasDerivAt hx).add_const (1/2) using 1
    · funext y
      simp only [SecondWord.SameZero.PJ.Diagonal.height]
      ring
    · rfl
  have hu : 0<horizontal x := by linarith [(SecondWord.SameZero.PJ.Diagonal.whole_bounds hx).1]
  have hd := (((Real.hasDerivAt_cos x).const_mul (q r-p r)).add
    (((((Real.hasDerivAt_sin x).const_mul (q r-p r)).add_const (P r)).mul hV).div
      hU hu.ne')).sub_const (t r)
  have hc := SecondWord.SameZero.PJ.Diagonal.circle hx
  have hrotation : vertical x*Real.cos x-horizontal x*Real.sin x=Z x := by
    dsimp [vertical,horizontal,SecondWord.SameZero.PJ.Diagonal.vertical,
      SecondWord.SameZero.PJ.Diagonal.horizontal]
    linear_combination (SecondWord.SameZero.PJ.Diagonal.Z x)*(Real.sin_sq_add_cos_sq x)
  convert hd using 1
  · rfl
  · dsimp [targetSlopeD]
    field_simp
    linear_combination (-(q r-p r)*horizontal x)*hrotation-
      (((q r-p r)*Real.sin x+P r)*factor x)*hc

lemma negative_Z_factor {x : ℝ} (hx : x∈Icc start (7/10)) (hz : Z x<0) :
    (665/1250:ℝ)<factor x := by
  have hr := SecondWord.SameZero.PJ.Diagonal.radical_data hx
  have tr := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx)
  have hs : (499/1250:ℝ)<Real.sin x := by
    dsimp [Z,SecondWord.SameZero.PJ.Diagonal.Z,z₀] at hz
    linarith [ShortMixedZero.fine_diagonal_bounds.1]
  have hc : Real.cos x<(917/1000:ℝ) := by
    nlinarith [Real.sin_sq_add_cos_sq x,tr.1]
  have hy : (1963/1000:ℝ)<Y x := by
    have hn := hr.2.2.2.2
    norm_num [Q0] at hn
    nlinarith [hr.1,hr.2.2.1,hz]
  have hratio : Real.cos x/Y x<(117/250:ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0<Y x)).2
    nlinarith
  dsimp [factor,SecondWord.SameZero.PJ.Diagonal.factor]
  linarith

lemma targetSlopeD_positive (r : Row) (hr : Coupled r) {x : ℝ}
    (hx : x∈Icc start (7/10)) : 0<targetSlopeD r x := by
  have hL : 0<q r-p r := by
    have hp := (coupled_signs r hr).1
    linarith [(coefficient_signs r).1]
  have hP := (coefficient_signs r).2.2
  have hcoord := SecondWord.SameZero.PJ.Diagonal.whole_bounds hx
  have hbase := SecondWord.SameZero.PJ.Diagonal.coordinates_positive hx
  have hu : 0<horizontal x := by linarith [hcoord.1]
  have hf : 0<factor x := by linarith [hbase.2.2]
  have hxi := SecondWord.SameZero.PJ.Diagonal.angle_mem hx
  have hsin : 0<Real.sin x := Real.sin_pos_of_pos_of_lt_pi
    (by norm_num [start,SecondWord.SameZero.PJ.Diagonal.start] at hx; linarith [hx.1])
    (by linarith [hxi.2,Real.pi_gt_three])
  have hF : 0<(q r-p r)*Real.sin x+P r := by
    have := mul_pos hL hsin
    linarith
  by_cases hz : 0≤Z x
  · have h1 := div_nonneg (mul_nonneg hL.le hz) hu.le
    have h2 := div_pos
      (mul_pos (mul_pos hF (show (0:ℝ)<Q0 by norm_num [Q0])) hf) (sq_pos_of_pos hu)
    dsimp [targetSlopeD]
    linarith
  · have hz' : Z x<0 := lt_of_not_ge hz
    have hfL := negative_Z_factor hx hz'
    have hs : (499/1250:ℝ)<Real.sin x := by
      dsimp [Z,SecondWord.SameZero.PJ.Diagonal.Z,z₀] at hz'
      linarith [ShortMixedZero.fine_diagonal_bounds.1]
    have hZ := (SecondWord.SameZero.PJ.Diagonal.radical_data hx).1
    have h1 := mul_le_mul_of_nonneg_right hZ.le hu.le
    have h2 := mul_le_mul_of_nonpos_left hcoord.2.1.le (by norm_num : (-123/500:ℝ)≤0)
    have hnegative : -(123/500)*(383/200)≤Z x*horizontal x := by linarith
    have hnegativeL := mul_le_mul_of_nonneg_left hnegative hL.le
    have hsinL := mul_le_mul_of_nonneg_left hs.le hL.le
    have hpositive := mul_le_mul
      (show (q r-p r)*(499/1250)≤(q r-p r)*Real.sin x+P r by linarith)
      hfL.le (by norm_num : (0:ℝ)≤665/1250) hF.le
    have hpositiveQ := mul_le_mul_of_nonneg_left hpositive (by norm_num [Q0] : (0:ℝ)≤Q0)
    have href : 0 < -(123/500)*(383/200)+(499/1250)*Q0*(665/1250) := by norm_num [Q0]
    have hreserve := mul_pos hL href
    have hnum : 0<(q r-p r)*Z x*horizontal x+
        ((q r-p r)*Real.sin x+P r)*Q0*factor x := by
      norm_num [Q0] at hpositiveQ hreserve ⊢
      linarith
    have he : targetSlopeD r x=
        ((q r-p r)*Z x*horizontal x+((q r-p r)*Real.sin x+P r)*Q0*factor x)/
          (horizontal x)^2 := by
      dsimp [targetSlopeD]
      field_simp
    rw [he]
    exact div_pos hnum (sq_pos_of_pos hu)

lemma targetSlope_monotone (r : Row) (hr : Coupled r) :
    MonotoneOn (targetSlope r) (Icc start (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hx => (targetSlope_hasDerivAt r hx).continuousAt.continuousWithinAt)
    (fun _ hx => targetSlope_hasDerivAt r (Ioo_subset_Icc_self hx))
    (fun _ hx => (targetSlopeD_positive r hr (Ioo_subset_Icc_self hx)).le)

lemma late_slope (r : Row) (hr : Coupled r) {x : ℝ} (hx : x∈Icc (3/10:ℝ) (7/10)) :
    0<targetSlope r x := by
  have hh := targetSlope_monotone r hr
    (by norm_num [start,SecondWord.SameZero.PJ.Diagonal.start])
    ⟨by norm_num [start,SecondWord.SameZero.PJ.Diagonal.start]; linarith [hx.1],hx.2⟩ hx.1
  linarith [(three_tenths.2.2 r hr)]

lemma actual_targetSlope (r : Row) {B x : ℝ} (hd : Domain B x)
    (hb : contact B x=outerDiagonal) :
    Same.targetFirst r B x=targetSlope r x := by
  obtain ⟨hx,hB⟩ := SecondWord.SameZero.PJ.Diagonal.original_coordinates hd hb
  have hU := (SecondWord.SameZero.PJ.Diagonal.actual_coordinates hx).1
  have hV := (SecondWord.SameZero.PJ.Diagonal.actual_coordinates hx).2
  rw [hB] at hU hV
  dsimp [Same.targetFirst,l,projection,SecondWord.SameZero.k]
  rw [hb,SecondWord.ratio_diagonal]
  change (q r-p r*1)*(Real.cos x+(SecondWord.W B/SecondWord.U B)*Real.sin x)+
    P r*(SecondWord.W B/SecondWord.U B)-t r=targetSlope r x
  rw [hU,hV]
  dsimp [targetSlope]
  ring

lemma original_early_lower (r : Row) (hr : Coupled r) {B x : ℝ}
    (hd : Domain B x) (hb : contact B x=outerDiagonal) (hx : x≤3/10) :
    (11226/12500:ℝ)<Same.cost r B x := by
  obtain ⟨e,he⟩ := Event.exists_event
  obtain ⟨hG,hB⟩ := SecondWord.SameZero.PJ.Diagonal.original_coordinates hd hb
  have hl := early_lower r hr he ⟨Event.before_contact he hd,hx⟩
  have hB' : height x=B := hB
  simp only [cost] at hl
  rw [hB'] at hl
  simp only [Same.cost]
  rw [hb,ShortOuterOne.SameContact.arc_diagonal]
  linarith

lemma original_late_slope (r : Row) (hr : Coupled r) {B x : ℝ}
    (hd : Domain B x) (hb : contact B x=outerDiagonal) (hx : 3/10≤x) :
    0<Same.targetFirst r B x := by
  rw [actual_targetSlope r hd hb]
  exact late_slope r hr ⟨hx,hd.2.1.2⟩

end SquaresInCircles.Eight.ShortOuterZero.Same.Diagonal
end
end
end
