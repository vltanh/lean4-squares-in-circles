module

public import SquaresInCircles.Eight.Words.Common.ZeroSame
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroNegativeContact

/-!
# Eight squares: four unfavorable same-sign outer zero owners

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
