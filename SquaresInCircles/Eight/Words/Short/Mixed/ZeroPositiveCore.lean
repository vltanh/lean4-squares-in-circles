module

public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroPositive

/-!
# Eight squares: positive core source and positive outer target on a zero edge

The original owner forces the angle above `.4`. For three role families
an exact rotating-vector norm has a uniform speed bound, so the original
circle support loses less than `.081` after its initial value above `.98`.
The last family uses the actual axial support and its derivative bound.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero.PositiveCore

open CommonQuarter CorePairGeometry

abbrev Row := Fin 4
def c : Row → ℝ := ![-2953/100000,12783/100000,46969/100000,-2145/100000]
def p : Row → ℝ := ![0,13422/100000,33147/100000,0]
def q : Row → ℝ := ![99940/100000,103828/100000,113360/100000,71553/100000]
def g : Row → ℝ := ![108816/100000,113855/100000,104073/100000,104729/100000]
def rate : Row → ℝ := ![1,1047/1000,104073/100000,104729/100000]
def ceiling : Row → ℝ := ![53/125,289/500,379/500,1]

lemma coefficients (r : Row) : 0≤p r ∧ 0<q r ∧ 0<g r ∧ 0<rate r ∧
    (rate r=g r ∨ (p r)^2+(q r)^2≤(rate r)^2) := by
  fin_cases r <;> norm_num [p,q,g,rate]

lemma initial_trig : (194709/500000:ℝ)<Real.sin (2/5:ℝ) ∧
    Real.sin (2/5:ℝ)<389419/1000000 ∧ (46053/50000:ℝ)<Real.cos (2/5:ℝ) := by
  have hs := sin_lower_seven (x := (2/5:ℝ)) (by norm_num)
  have hu := sin_upper_five (x := (2/5:ℝ)) (by norm_num)
  have hc := cos_lower_six (x := (2/5:ℝ)) (by norm_num)
  norm_num at hs hu hc
  exact ⟨by linarith,by linarith,by linarith⟩

lemma angle_trig {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    (389/1000:ℝ)<Real.sin x ∧ (191/250:ℝ)<Real.cos x := by
  have hs := sin_mono (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num)
    ⟨by linarith [hx.1],hx.2⟩ hx.1
  exact ⟨by linarith [initial_trig.1],by
    linarith [(positive_trig (show x∈Icc 0 (7/10) from ⟨by linarith [hx.1],hx.2⟩)).1]⟩

/-- The positivity half of `CommonQuarter.zero_positive_secondary_angle` (not imported here):
the original weak separator forces a positive angle. -/
private lemma zero_positive_angle_pos {source target : RadialKind}
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) : 0<φ := by
  have hs' := state_bounds hs
  have ht' := state_bounds ht
  have hc : 0<Real.cos φ := by linarith [(signed_cos hφ).1]
  have hw : 1≤pairWidth φ := by
    have h := one_le_abs_cos_add_abs_sin φ
    dsimp [pairWidth]
    linarith
  by_contra! hn
  have hsin : Real.sin φ≤0 := by
    have hp := positive_trig (x := -φ) ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
    simpa only [Real.sin_neg,neg_nonneg] using hp.2.2.1
  have hAs := mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ)≤A by linarith [ht'.1]) hsin
  have hBc := mul_nonneg ht'.2.2.1 hc.le
  norm_num [forwardMargin] at hm
  nlinarith [hs'.2.2.2.2]

lemma original_angle {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) : (2/5:ℝ)<φ := by
  have hs' : State .coreSide a b := by simpa [State] using hs
  have ht' : State .outer A B := by simpa [State] using ht
  have hp := zero_positive_angle_pos hs' ht' hφ hm
  have hx : φ∈Icc 0 (7/10) := ⟨by linarith,(abs_le.mp hφ).2⟩
  have tr := positive_trig hx
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.2.2
  have hA := mul_le_mul_of_nonneg_right (outer_bounds ht).2.1 tr.2.2.1
  have hB := mul_nonneg ht.1 (by linarith [tr.1] : 0≤Real.cos φ)
  have hw : pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
    ring
  norm_num [forwardMargin] at hm
  rw [hw] at hm
  by_contra! hn
  have hc := Real.one_sub_sq_div_two_le_cos (x := φ)
  have hsine := Real.sin_le hx.1
  have hs2 := pow_le_pow_left₀ hx.1 hn 2
  have hprim := mul_le_mul_of_nonneg_right outer_endpoint_bounds.2.1.le tr.2.2.1
  nlinarith [CoreAngleEndpoint.diagonal_bounds.2]

def N (r : Row) (x : ℝ) : ℝ := WrongWordCircleSupport.N (p r) (q r) (g r) x
def Nd (r : Row) (x : ℝ) : ℝ := g r*(p r*Real.cos x+q r*Real.sin x)/N r x
def F (r : Row) (x : ℝ) : ℝ := x+c r+(g r+p r+q r)/2+g r*Real.sin x-CommonQuarter.radius*N r x
def Fd (r : Row) (x : ℝ) : ℝ := 1+g r*Real.cos x-CommonQuarter.radius*Nd r x

lemma norm_energy_pos (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    0<CircularNorm.energy (WrongWordCircleSupport.mass (p r) (q r) (g r))
      (-2*g r*q r) (2*g r*p r) x := by
  rw [WrongWordCircleSupport.energy_eq]
  have hc := coefficients r
  have hs := mul_pos hc.2.2.1 (show 0<Real.sin x by linarith [(angle_trig hx).1])
  have hX : WrongWordCircleSupport.X (p r) (g r) x<0 := by
    dsimp [WrongWordCircleSupport.X]
    linarith [hc.1]
  nlinarith [sq_nonneg (WrongWordCircleSupport.Y (q r) (g r) x)]

lemma N_pos (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) : 0<N r x :=
  CircularNorm.norm_pos (norm_energy_pos r hx)

lemma N_sq (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    (N r x)^2=(p r)^2+(q r)^2+(g r)^2+
      2*g r*(p r*Real.sin x-q r*Real.cos x) := by
  have hh := CircularNorm.norm_sq (norm_energy_pos r hx).le
  change (N r x)^2=_ at hh
  dsimp [CircularNorm.energy,WrongWordCircleSupport.mass] at hh
  nlinarith only [hh]

lemma N_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    HasDerivAt (N r) (Nd r x) x := by
  have hh := CircularNorm.norm_hasDerivAt (norm_energy_pos r hx)
  convert hh using 1
  · rfl
  · dsimp [Nd,CircularNorm.d1,CircularNorm.slope,N,WrongWordCircleSupport.N]
    ring

/-- The two squared identities give both rotating-vector speed bounds.
The exact role chooses the smaller useful bound without approximation
of the norm or division by a merely assumed positive quantity. -/
lemma Nd_le_rate (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) : Nd r x≤rate r := by
  let s := p r*Real.sin x-q r*Real.cos x
  let t := p r*Real.cos x+q r*Real.sin x
  have hpj : t^2+s^2=(p r)^2+(q r)^2 := by
    dsimp [s,t]
    linear_combination ((p r)^2+(q r)^2)*(Real.sin_sq_add_cos_sq x)
  have hn := N_sq r hx
  change (N r x)^2=(p r)^2+(q r)^2+(g r)^2+2*g r*s at hn
  have hsq : (g r*t)^2≤(rate r*N r x)^2 := by
    rcases (coefficients r).2.2.2.2 with he | he
    · rw [he]
      have hid : (g r*t)^2+(g r*(g r+s))^2=(g r*N r x)^2 := by
        linear_combination (g r)^2*hpj-(g r)^2*hn
      nlinarith only [hid,sq_nonneg (g r*(g r+s))]
    · have hid : (g r*t)^2+((p r)^2+(q r)^2+g r*s)^2=
          ((p r)^2+(q r)^2)*(N r x)^2 := by
        linear_combination (g r)^2*hpj-((p r)^2+(q r)^2)*hn
      have hcoef := mul_le_mul_of_nonneg_right he (sq_nonneg (N r x))
      nlinarith only [hid,hcoef,sq_nonneg ((p r)^2+(q r)^2+g r*s)]
  have hprod := mul_pos (coefficients r).2.2.2.1 (N_pos r hx)
  have hle : g r*t≤rate r*N r x := by
    by_contra! hbad
    have hh := mul_pos (sub_pos.mpr hbad)
      (show 0<g r*t+rate r*N r x by linarith)
    nlinarith only [hsq,hh]
  exact (div_le_iff₀ (N_pos r hx)).2 hle

lemma F_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    HasDerivAt (F r) (Fd r x) x :=
  ((((hasDerivAt_id' x).add_const (c r)).add_const ((g r+p r+q r)/2)).add
    ((Real.hasDerivAt_sin x).const_mul (g r))).sub ((N_hasDerivAt r hx).const_mul CommonQuarter.radius)

lemma Fd_lower (r : Row) (h3 : r≠3) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    -(27/100:ℝ)<Fd r x := by
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hn := mul_le_mul_of_nonneg_left (Nd_le_rate r hx) hR.le
  have hRu := mul_lt_mul_of_pos_right radius_bounds.2 (coefficients r).2.2.2.1
  have hc := mul_lt_mul_of_pos_left (angle_trig hx).2 (coefficients r).2.2.1
  dsimp [Fd]
  fin_cases r
  · norm_num [g,rate] at hn hRu hc ⊢; linarith
  · norm_num [g,rate] at hn hRu hc ⊢; linarith
  · norm_num [g,rate] at hn hRu hc ⊢; linarith
  · exact absurd rfl h3

lemma N_initial_upper (r : Row) : N r (2/5)<ceiling r := by
  have hx : (2/5:ℝ)∈Icc (2/5) (7/10) := by norm_num
  have hn := N_sq r hx
  have hp := N_pos r hx
  have hc := coefficients r
  have hs := mul_le_mul_of_nonneg_left initial_trig.2.1.le
    (mul_nonneg (by linarith [hc.2.2.1] : 0≤2*g r) hc.1)
  have hk := mul_le_mul_of_nonneg_left initial_trig.2.2.le
    (mul_nonneg (by linarith [hc.2.2.1] : 0≤2*g r) hc.2.1.le)
  fin_cases r <;> norm_num [p,q,g,ceiling] at hn hs hk ⊢ <;> nlinarith

lemma F_initial (r : Row) (h3 : r≠3) : (49/50:ℝ)<F r (2/5) := by
  have hn := mul_lt_mul_of_pos_left (N_initial_upper r)
    (show 0<CommonQuarter.radius by linarith [radius_bounds.1])
  have hceiling : 0<ceiling r := by fin_cases r <;> norm_num [ceiling]
  have hR := mul_lt_mul_of_pos_right radius_bounds.2 hceiling
  have hs := mul_lt_mul_of_pos_left initial_trig.1 (coefficients r).2.2.1
  dsimp [F]
  fin_cases r
  · norm_num [c,p,q,g,ceiling] at hn hR hs ⊢; linarith
  · norm_num [c,p,q,g,ceiling] at hn hR hs ⊢; linarith
  · norm_num [c,p,q,g,ceiling] at hn hR hs ⊢; linarith
  · exact absurd rfl h3

lemma F_lower (r : Row) (h3 : r≠3) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    (449/500:ℝ)<F r x := by
  let f : ℝ → ℝ := fun z => F r z+(27/100)*z
  have hd {z : ℝ} (hz : z∈Icc (2/5) (7/10)) :
      HasDerivAt f (Fd r z+27/100) z := by
    have h : HasDerivAt (fun y => F r y+(27/100)*y) (Fd r z+27/100*1) z :=
      (F_hasDerivAt r hz).add ((hasDerivAt_id' z).const_mul (27/100))
    exact h.congr_deriv (by ring)
  have hm : MonotoneOn f (Icc (2/5) (7/10)) :=
    monoOn_of_hasDeriv_nonneg (fun z hz => (hd hz).continuousAt.continuousWithinAt)
      (fun z hz => hd (Ioo_subset_Icc_self hz))
      (fun z hz => by linarith [Fd_lower r h3 (Ioo_subset_Icc_self hz)])
  have hh := hm (by norm_num) hx hx.1
  dsimp [f] at hh
  linarith [F_initial r h3,hx.2]

def axial (x : ℝ) : ℝ := x+c 3+g 3/2+(g 3/2)*Real.cos x-
  g 3*(outerAxial-1/2)*Real.sin x
def axialD (x : ℝ) : ℝ := 1-g 3*(Real.sin x/2+(outerAxial-1/2)*Real.cos x)

lemma axial_hasDerivAt (x : ℝ) : HasDerivAt axial (axialD x) x := by
  have hh : HasDerivAt (fun y => y+c 3+g 3/2+(g 3/2)*Real.cos y-
      g 3*(outerAxial-1/2)*Real.sin y)
      (1+(g 3/2)*(-Real.sin x)-g 3*(outerAxial-1/2)*Real.cos x) x :=
    ((((hasDerivAt_id' x).add_const (c 3)).add_const (g 3/2)).add
      ((Real.hasDerivAt_cos x).const_mul (g 3/2))).sub
        ((Real.hasDerivAt_sin x).const_mul (g 3*(outerAxial-1/2)))
  exact hh.congr_deriv (by dsimp [axialD]; ring)

lemma axialD_lower (x : ℝ) : -(1/10:ℝ)<axialD x := by
  have hp := mul_lt_mul_of_pos_left (axial_projection_bound x) (coefficients 3).2.2.1
  norm_num [axialD,g] at hp ⊢
  linarith

lemma axial_initial : (101/100:ℝ)<axial (2/5) := by
  have hs := mul_le_mul_of_nonneg_left initial_trig.2.1.le
    (show 0≤outerAxial-1/2 by linarith [outer_endpoint_bounds.1])
  have hu := mul_le_mul_of_nonneg_right outer_endpoint_bounds.2.1.le
    (show (0:ℝ)≤389419/1000000 by norm_num)
  norm_num [axial,c,g]
  nlinarith [initial_trig.2.2]

lemma axial_lower {x : ℝ} (hx : x∈Icc (2/5) (7/10)) : (449/500:ℝ)<axial x := by
  let f : ℝ → ℝ := fun z => axial z+z/10
  have hd (z : ℝ) : HasDerivAt f (axialD z+1/10) z :=
    (axial_hasDerivAt z).add ((hasDerivAt_id z).div_const 10)
  have hm : MonotoneOn f (Icc (2/5) (7/10)) :=
    monoOn_of_hasDeriv_nonneg (fun z _ => (hd z).continuousAt.continuousWithinAt)
      (fun z _ => hd z) (fun z _ => by linarith [axialD_lower z])
  have hh := hm (by norm_num) hx hx.1
  dsimp [f] at hh
  linarith [axial_initial,hx.2]

theorem original_cost (r : Row) {a b A B φ : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (449/500:ℝ)<φ+c r+g r*b-p r*A-q r*B := by
  have hx : φ∈Icc (2/5) (7/10) :=
    ⟨(original_angle hs ht hφ hm).le,(abs_le.mp hφ).2⟩
  have tr := positive_trig (show φ∈Icc 0 (7/10) from ⟨by linarith [hx.1],hx.2⟩)
  have hw : pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
    ring
  have hmargin := mul_nonneg (coefficients r).2.2.1.le hm
  norm_num [forwardMargin] at hmargin
  rw [hw] at hmargin
  by_cases h3 : r=3
  · subst r
    have hX : -p 3-g 3*Real.sin φ≤0 := by norm_num [p,g]; nlinarith [tr.2.2.1]
    have hY : 0≤g 3*Real.cos φ-q 3 := by norm_num [g,q]; linarith [(angle_trig hx).2]
    have hd := mul_nonneg
      (show 0≤outerAxial+1/2 by linarith [outer_endpoint_bounds.1]) hY
    have hsupp := WrongWordCircleSupport.outer_axial_lower ht hX
      (show 0≤(outerAxial+1/2)*(g 3*Real.cos φ-q 3)-(-p 3-g 3*Real.sin φ)/2 by linarith)
    have hlow := axial_lower hx
    norm_num [p] at hsupp ⊢
    dsimp [axial] at hlow
    nlinarith only [hmargin,hsupp,hlow]
  · have hsupp := outer_circle_lower (X := -p r-g r*Real.sin φ)
      (Y := g r*Real.cos φ-q r) ht
    have he := WrongWordCircleSupport.energy_eq (p r) (q r) (g r) φ
    have hn : N r φ=Real.sqrt ((-p r-g r*Real.sin φ)^2+(g r*Real.cos φ-q r)^2) := by
      unfold N WrongWordCircleSupport.N CircularNorm.norm
      rw [he]
      congr 1
      dsimp [WrongWordCircleSupport.X,WrongWordCircleSupport.Y]
      ring
    rw [← hn] at hsupp
    have hf := F_lower r h3 hx
    dsimp [F] at hf
    nlinarith only [hmargin,hsupp,hf]

end SquaresInCircles.Eight.ShortMixedZero.PositiveCore
