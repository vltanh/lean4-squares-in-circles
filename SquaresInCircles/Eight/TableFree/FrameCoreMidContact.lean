module

public import SquaresInCircles.Eight.TableFree.FrameCoreMidContactData

/-!
# A single touching support for the whole core/middle cancellation interval

The radical has second derivative below `1/10` on its complete required
domain.  Its tangent quadratic at the actual angle `27/25` gives a
global lower support.  After the cotangent substitution that support
has second derivative above `1/200`, proved by one concave degree-six
polynomial on the whole enlarged interval `[3/8,147/100]`.
The exact contact data then give the strict reserve `.900591`.
Uncompiled source draft of HAND_FOUR_TYPE_SCALAR_REPLACEMENTS §3.2.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreMidContact
open FramePair FrameCircleArc FrameMidArc

theorem w_bounds {t : ℝ} (ht : t∈Icc (3/8:ℝ) (147/100)) :
    (267/250:ℝ)<w t ∧ w t<9/5 := by
  have he := w_sq t
  have hn := w_pos t
  have ht0 : 0≤t := by linarith [ht.1]
  have hlo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/8) ht.1 2
  have hhi := pow_le_pow_left₀ ht0 ht.2 2
  constructor <;> norm_num at hlo hhi ⊢ <;> nlinarith

theorem N_lower {z : ℝ} (hz : (267/250:ℝ)≤z) : (123/40:ℝ)<N z := by
  have he := N_sq z
  have hn := N_pos z
  have hxl : p+g*(267/250)≤p+g*z := by dsimp [g]; nlinarith
  have hs := pow_le_pow_left₀
    (show 0≤p+g*(267/250) by norm_num [p,g]) hxl 2
  have hnum : (123/40:ℝ)^2<(p+g*(267/250))^2+q^2 := by norm_num [p,g,q]
  nlinarith

theorem Ndd_upper {z : ℝ} (hz : (267/250:ℝ)≤z) : Ndd z<(1/10:ℝ) := by
  have hn := N_lower hz
  have hcube := pow_le_pow_left₀ (show (0:ℝ)≤123/40 by norm_num) hn.le 3
  have hnum : g^2*q^2<(123/40:ℝ)^3/10 := by norm_num [g,q]
  apply (div_lt_iff₀ (pow_pos (N_pos z) 3)).2
  dsimp [Ndd]
  nlinarith

theorem cotangent_bounds {x : ℝ} (hx : x∈Icc (3/5:ℝ) (6/5)) :
    0<Real.sin x ∧ Real.cos x/Real.sin x∈Icc (3/8:ℝ) (147/100) := by
  have hπ : (6/5:ℝ)≤Real.pi/2 := by linarith [FrameLowPair.pi_lower]
  have hsL := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(3/5:ℝ))
    (hx.2.trans hπ) hx.1
  have hsU := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx.1,Real.pi_pos] : -(Real.pi/2)≤x) hπ hx.2
  have hcL := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hx.2
  have hcU := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤3/5) (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  have hsinL := Real.sin_ge_sub_cube (show (0:ℝ)≤3/5 by norm_num)
  have hsinU := sin_upper_five (show (0:ℝ)≤6/5 by norm_num)
  have hcosL := cos_lower_six (show (0:ℝ)≤6/5 by norm_num)
  have hcosU := cos_upper_four (show (0:ℝ)≤3/5 by norm_num)
  norm_num at hsinL hsinU hcosL hcosU
  have hs : 0<Real.sin x := by linarith
  refine ⟨hs,?_,?_⟩
  · apply (le_div_iff₀ hs).2
    linarith
  · apply (div_le_iff₀ hs).2
    linarith

theorem cotangent_identity {x : ℝ} (hx : x∈Icc (3/5:ℝ) (6/5)) :
    w (Real.cos x/Real.sin x)=1/Real.sin x ∧
      Real.pi/2-Real.arctan (Real.cos x/Real.sin x)=x := by
  have hs := (cotangent_bounds hx).1
  have he := Real.sin_sq_add_cos_sq x
  have hrad : 1+(Real.cos x/Real.sin x)^2=(1/Real.sin x)^2 := by
    field_simp [hs.ne']
    nlinarith only [he]
  constructor
  · dsimp [w]
    rw [hrad,Real.sqrt_sq (one_div_pos.mpr hs).le]
  · have ha := Real.arctan_tan
      (show -(Real.pi/2)<Real.pi/2-x by linarith [hx.2,FrameLowPair.pi_lower])
      (show Real.pi/2-x<Real.pi/2 by linarith [hx.1])
    rw [Real.tan_eq_sin_div_cos,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] at ha
    linarith

theorem contact_t_mem : t0∈Icc (3/8:ℝ) (147/100) := by
  simpa [t0,s0,c0] using (cotangent_bounds
    (show x0∈Icc (3/5:ℝ) (6/5) by norm_num [x0])).2

theorem contact_w_identity : w t0=w0 := by
  simpa [t0,s0,c0,w0] using (cotangent_identity
    (show x0∈Icc (3/5:ℝ) (6/5) by norm_num [x0])).1

theorem contact_arctan : Real.pi/2-Real.arctan t0=x0 := by
  simpa [t0,s0,c0] using (cotangent_identity
    (show x0∈Icc (3/5:ℝ) (6/5) by norm_num [x0])).2

theorem contact_w_mem : w0∈Icc (267/250:ℝ) (9/5) := by
  have hh := w_bounds contact_t_mem
  rw [contact_w_identity] at hh
  exact ⟨hh.1.le,hh.2.le⟩

/-- The upper tangent quadratic uses the actual contact norm and slope. -/
theorem norm_tangent_upper {z : ℝ} (hz : z∈Icc (267/250:ℝ) (9/5)) :
    N z≤N0+Nd w0*(z-w0)+(z-w0)^2/20 := by
  have hh := curvature_tangent (f := fun z => -N z) (d := fun z => -Nd z)
    (dd := fun z => -Ndd z) (κ := -(1/10:ℝ)) hz contact_w_mem
    (fun z _ => (N_deriv z).neg) (fun z _ => (Nd_deriv z).neg)
    (fun z hz => by linarith [Ndd_upper hz.1])
  dsimp [N0]
  nlinarith

def constant0 : ℝ :=
  9/100-cM+(p+q+g)/2-R*N0+R*Nd w0*w0-(R/20)*(1+w0^2)

def transformed (t : ℝ) : ℝ :=
  Real.pi/2-Real.arctan t-(9/100)*(1+t)/w t+
    9/100-cM+(p+q+g)/2+g*w t+(13*g/12)*t-R*N (w t)

def model (t : ℝ) : ℝ :=
  Real.pi/2-Real.arctan t-(9/100)*(1+t)/w t+constant0+
    a*w t+(13*g/12)*t-(R/20)*t^2

def modelD (t : ℝ) : ℝ :=
  -1/(w t)^2-(9/100)*(1-t)/(w t)^3+a*t/w t+13*g/12-(R/10)*t

def modelDD (t : ℝ) : ℝ :=
  2*t/(w t)^4+(9/100)*(1+3*t-2*t^2)/(w t)^5+a/(w t)^3-R/10

theorem model_deriv (t : ℝ) : HasDerivAt model (modelD t) t := by
  have hn := (w_pos t).ne'
  have har := (Real.hasDerivAt_arctan t).const_sub (Real.pi/2)
  have hquot := (((hasDerivAt_id t).const_add 1).const_mul (9/100)).div (w_deriv t) hn
  have hh := (((((har.sub hquot).add_const constant0).add ((w_deriv t).const_mul a)).add
    ((hasDerivAt_id t).const_mul (13*g/12))).sub
      (((hasDerivAt_id t).pow 2).const_mul (R/20)))
  convert hh using 1
  · rfl
  · dsimp [modelD,wd]
    rw [← w_sq t]
    field_simp [hn]
    ring_nf
    simp only [w_power t 0,w_power t 1,w_power t 2,w_power t 3,w_power t 4,
      w_power t 5,w_power t 6,pow_zero,pow_one]
    ring

theorem modelD_deriv (t : ℝ) : HasDerivAt modelD (modelDD t) t := by
  have hn := (w_pos t).ne'
  have hfirst := (hasDerivAt_const t (-1:ℝ)).div ((w_deriv t).pow 2) (pow_ne_zero 2 hn)
  have hsecond := (((hasDerivAt_id t).const_sub 1).const_mul (9/100)).div
    ((w_deriv t).pow 3) (pow_ne_zero 3 hn)
  have hthird := ((hasDerivAt_id t).const_mul a).div (w_deriv t) hn
  have hh := ((((hfirst.sub hsecond).add hthird).add_const (13*g/12)).sub
    ((hasDerivAt_id t).const_mul (R/10)))
  convert hh using 1
  · rfl
  · dsimp [modelDD,wd]
    field_simp [hn]
    ring_nf
    simp only [w_power t 0,w_power t 1,w_power t 2,w_power t 3,w_power t 4,
      w_power t 5,w_power t 6,w_power t 7,w_power t 8,w_power t 9,
      w_power t 10,w_power t 11,w_power t 12,pow_zero,pow_one]
    ring

def B (t : ℝ) : ℝ := 2*t-(203/1000)*(1+t^2)^2
def Bd (t : ℝ) : ℝ := 2-(203/250)*t*(1+t^2)
def Bdd (t : ℝ) : ℝ := -(203/250)-(609/250)*t^2

theorem B_deriv (t : ℝ) : HasDerivAt B (Bd t) t := by
  convert ((hasDerivAt_id t).const_mul 2).sub
    (((((hasDerivAt_id t).pow 2).const_add 1).pow 2).const_mul (203/1000))
    using 1 <;> dsimp [B,Bd] <;> ring

theorem Bd_deriv (t : ℝ) : HasDerivAt Bd (Bdd t) t := by
  convert ((((hasDerivAt_id t).mul (((hasDerivAt_id t).pow 2).const_add 1)).const_mul
    (203/250)).const_sub 2) using 1 <;> dsimp [Bd,Bdd] <;> ring

theorem B_positive {t : ℝ} (ht : t∈Icc (3/8:ℝ) (147/100)) : (2/5:ℝ)<B t := by
  apply concave_gt_of_endpoints (concave_of_deriv2
    (fun t _ => B_deriv t) (fun t _ => Bd_deriv t)
    (fun t _ => by dsimp [Bdd]; nlinarith [sq_nonneg t])) ht
  · norm_num [B]
  · norm_num [B]

def P (t : ℝ) : ℝ :=
  -327/500+(227/100)*t-(2399/2000)*t^2+(5/7)*t^3-(87/250)*t^4-(29/400)*t^6
def Pd (t : ℝ) : ℝ :=
  227/100-(2399/1000)*t+(15/7)*t^2-(174/125)*t^3-(87/200)*t^5
def Pdd (t : ℝ) : ℝ :=
  -2399/1000+(30/7)*t-(522/125)*t^2-(87/40)*t^4

theorem P_deriv (t : ℝ) : HasDerivAt P (Pd t) t := by
  have hd : Differentiable ℝ P := by dsimp [P]; fun_prop
  have he : deriv P t=Pd t := by
    simp (disch := fun_prop) [P,Pd]
    ring
  rw [← he]
  exact (hd t).hasDerivAt

theorem Pd_deriv (t : ℝ) : HasDerivAt Pd (Pdd t) t := by
  have hd : Differentiable ℝ Pd := by dsimp [Pd]; fun_prop
  have he : deriv Pd t=Pdd t := by
    simp (disch := fun_prop) [Pd,Pdd]
    ring
  rw [← he]
  exact (hd t).hasDerivAt

theorem Pdd_negative (t : ℝ) : Pdd t<0 := by
  have hquad := sq_nonneg ((1044/125)*t-30/7)
  have hfour := sq_nonneg (t^2)
  dsimp [Pdd]
  nlinarith

theorem P_positive {t : ℝ} (ht : t∈Icc (3/8:ℝ) (147/100)) : 0<P t := by
  apply concave_gt_of_endpoints (concave_of_deriv2
    (fun t _ => P_deriv t) (fun t _ => Pd_deriv t)
    (fun t _ => (Pdd_negative t).le)) ht
  · norm_num [P]
  · norm_num [P]

theorem w_chord_lower {t : ℝ} (ht : t∈Icc (3/8:ℝ) (147/100)) :
    1+(5/14)*t^2<w t := by
  have hw := w_bounds ht
  have he := w_sq t
  have hwp : 0<w t-1 := by linarith [hw.1]
  have hp := mul_pos hwp (show 0<14/5-(w t+1) by linarith [hw.2])
  nlinarith

theorem modelDD_lower {t : ℝ} (ht : t∈Icc (3/8:ℝ) (147/100)) :
    (1/200:ℝ)<modelDD t := by
  have hw := w_pos t
  have he := w_sq t
  have hpow3 : (w t)^3=(w t)*(1+t^2) := by rw [w_power t 1,pow_one]
  have hpow5 : (w t)^5=w t*(1+t^2)^2 := by
    rw [w_power t 3,hpow3]
    ring
  have hscaled :
      w t*B t+(27/100)*t-451/1000-(721/1000)*t^2<
        (w t)^5*(modelDD t-1/200) := by
    have ha := mul_lt_mul_of_pos_right a_lower (pow_pos hw 2)
    have hR : R<(99/50:ℝ) := by linarith [contact_radius.2,show rHi<(99/50:ℝ) by norm_num [rHi]]
    have hr := mul_lt_mul_of_pos_right hR (show 0<(w t)^5/10 by positivity)
    have hid : (w t)^5*(modelDD t-1/200)=
        2*t*w t+(9/100)*(1+3*t-2*t^2)+a*(w t)^2-
          (R/10+1/200)*(w t)^5 := by
      dsimp [modelDD]
      field_simp [hw.ne']
      ring
    rw [hid]
    dsimp [B]
    simp only [he,hpow5] at ha hr ⊢
    nlinarith
  have hb : 0<B t := by linarith [B_positive ht]
  have hwB := mul_lt_mul_of_pos_right (w_chord_lower ht) hb
  have hidentity : (1+(5/14)*t^2)*B t+(27/100)*t-451/1000-(721/1000)*t^2=P t := by
    dsimp [B,P]
    ring
  have hP := P_positive ht
  have hpos : 0<(w t)^5*(modelDD t-1/200) := by nlinarith
  by_contra! hbad
  have hn := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hw.le 5) (by linarith : modelDD t-1/200≤0)
  linarith

theorem model_le_transformed {t : ℝ} (ht : t∈Icc (3/8:ℝ) (147/100)) :
    model t≤transformed t := by
  have hb := w_bounds ht
  have hn := norm_tangent_upper ⟨hb.1.le,hb.2.le⟩
  have hr := mul_le_mul_of_nonneg_left hn R_pos.le
  have he := w_sq t
  dsimp [model,transformed,constant0,a]
  nlinarith

theorem scalar_eq_transformed {x : ℝ} (hx : x∈Icc (3/5:ℝ) (6/5)) :
    scalar x=transformed (Real.cos x/Real.sin x) := by
  have hs := (cotangent_bounds hx).1
  have hi := cotangent_identity hx
  dsimp [scalar,transformed]
  rw [hi.1,hi.2]
  field_simp [hs.ne']
  ring

theorem model_contact_value : model t0=scalar x0 := by
  have he := w_sq t0
  rw [contact_w_identity] at he
  have hh : model t0=transformed t0 := by
    dsimp [model,transformed,constant0,a]
    rw [contact_w_identity]
    change _=Real.pi/2-Real.arctan t0-(9/100)*(1+t0)/w0+
      9/100-cM+(p+q+g)/2+g*w0+(13*g/12)*t0-R*N0
    nlinarith
  rw [hh]
  symm
  simpa [t0,s0,c0] using scalar_eq_transformed
    (show x0∈Icc (3/5:ℝ) (6/5) by norm_num [x0])

theorem model_contact_derivative : modelD t0= -(s0^2)*scalarD x0 := by
  have hs := contact_signs.1.ne'
  have hn := contact_signs.2.2.2.ne'
  dsimp [modelD]
  rw [contact_w_identity]
  dsimp [a,Nd,scalarD,t0,w0,s0,c0,N0]
  field_simp [hs,hn]
  ring

theorem model_lower {t : ℝ} (ht : t∈Icc (3/8:ℝ) (147/100)) :
    (900591/1000000:ℝ)<model t := by
  have hvalue : (4503/5000:ℝ)<model t0 := by rw [model_contact_value]; exact contact_value
  have hd : |modelD t0|<(3/10000:ℝ) := by
    rw [model_contact_derivative,abs_mul,abs_neg,abs_sq]
    have hs : s0≤1 := Real.sin_le_one x0
    have hs0 := contact_signs.1
    have hs2 : s0^2≤1 := by nlinarith
    have hd := contact_derivative
    have hm := mul_le_mul_of_nonneg_right hs2 (abs_nonneg (scalarD x0))
    nlinarith
  have hd2 : (modelD t0)^2<(3/10000:ℝ)^2 := by
    obtain ⟨hdL,hdU⟩ := abs_lt.mp hd
    nlinarith
  have hh := curvature_tangent (κ := (1/200:ℝ)) ht contact_t_mem
    (fun t _ => model_deriv t) (fun t _ => modelD_deriv t)
    (fun t ht => (modelDD_lower ht).le)
  nlinarith [sq_nonneg ((t-t0)+200*modelD t0)]

/-- The actual original trigonometric/radical cancellation expression,
on its entire required interval and with its original exact radius. -/
theorem scalar_lower {x : ℝ} (hx : x∈Icc (3/5:ℝ) (6/5)) :
    (900591/1000000:ℝ)<scalar x := by
  rw [scalar_eq_transformed hx]
  exact (model_lower (cotangent_bounds hx).2).trans_le
    (model_le_transformed (cotangent_bounds hx).2)

end SquaresInCircles.Eight.TableFree.FrameCoreMidContact
