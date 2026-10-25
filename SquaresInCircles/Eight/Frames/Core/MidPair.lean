module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Frames.Core.MidContactData
public import SquaresInCircles.Eight.Frames.Core.HighHighSecondaryScalars
public import SquaresInCircles.Eight.Frames.Low.Pair

/-!
# Eight squares: the complete original core/middle frame-pair inequality

Both orientations, both signs at each actual point and all four weak
forward witnesses are included.  Reflection reverses an edge without
changing its original cost.  The only angular premise is the already
proved original exterior gap, not a concentrated frame interval.
-/

section
/-!
## A single touching support for the whole core/middle cancellation interval

The radical has second derivative below `1/10` on its complete required
domain.  Its tangent quadratic at the actual angle `27/25` gives a
global lower support.  After the cotangent substitution that support
has second derivative above `1/200`, proved by one concave degree-six
polynomial on the whole enlarged interval `[3/8,147/100]`.
The exact contact data then give the strict reserve `.900591`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreMidContact
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
  have hquot := (((hasDerivAt_id' t).const_add 1).const_mul (9/100)).fun_div (w_deriv t) hn
  have hh := (((((har.fun_sub hquot).add_const constant0).fun_add
    ((w_deriv t).const_mul a)).fun_add ((hasDerivAt_id' t).const_mul (13*g/12))).fun_sub
      (((hasDerivAt_id' t).fun_pow 2).const_mul (R/20)))
  convert hh using 1
  · rfl
  · have he := w_sq t
    dsimp [modelD,wd]
    rw [← w_sq t]
    field_simp
    linear_combination 21600*he

theorem modelD_deriv (t : ℝ) : HasDerivAt modelD (modelDD t) t := by
  have hn := (w_pos t).ne'
  have hfirst := (hasDerivAt_const t (-1:ℝ)).fun_div ((w_deriv t).fun_pow 2) (pow_ne_zero 2 hn)
  have hsecond := (((hasDerivAt_id' t).const_sub 1).const_mul (9/100)).fun_div
    ((w_deriv t).fun_pow 3) (pow_ne_zero 3 hn)
  have hthird := ((hasDerivAt_id' t).const_mul a).fun_div (w_deriv t) hn
  have hh := ((((hfirst.fun_sub hsecond).fun_add hthird).add_const (13*g/12)).fun_sub
    ((hasDerivAt_id' t).const_mul (R/10)))
  convert hh using 1
  · rfl
  · have he := w_sq t
    dsimp [modelDD,wd]
    field_simp
    linear_combination (-10*(9+100*a*w t^2))*he

def B (t : ℝ) : ℝ := 2*t-(203/1000)*(1+t^2)^2
def Bd (t : ℝ) : ℝ := 2-(203/250)*t*(1+t^2)
def Bdd (t : ℝ) : ℝ := -(203/250)-(609/250)*t^2

theorem B_deriv (t : ℝ) : HasDerivAt B (Bd t) t := by
  have hh := ((hasDerivAt_id' t).const_mul 2).fun_sub
    (((((hasDerivAt_id' t).fun_pow 2).const_add 1).fun_pow 2).const_mul (203/1000))
  convert hh using 1
  · rfl
  · dsimp [Bd]
    norm_num
    ring

theorem Bd_deriv (t : ℝ) : HasDerivAt Bd (Bdd t) t := by
  have hh := ((((hasDerivAt_id' t).fun_mul (((hasDerivAt_id' t).fun_pow 2).const_add 1)).const_mul
    (203/250)).const_sub 2)
  convert hh using 1
  · funext y
    dsimp [Bd]
    ring
  · dsimp [Bdd]
    norm_num
    ring

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
  have hh := ((((((hasDerivAt_id' t).const_mul (227/100)).const_add (-327/500)).fun_sub
    (((hasDerivAt_id' t).fun_pow 2).const_mul (2399/2000))).fun_add
      (((hasDerivAt_id' t).fun_pow 3).const_mul (5/7))).fun_sub
        (((hasDerivAt_id' t).fun_pow 4).const_mul (87/250))).fun_sub
          (((hasDerivAt_id' t).fun_pow 6).const_mul (29/400))
  convert hh using 1
  · rfl
  · dsimp [Pd]
    norm_num
    ring

theorem Pd_deriv (t : ℝ) : HasDerivAt Pd (Pdd t) t := by
  have hh := (((((hasDerivAt_id' t).const_mul (2399/1000)).const_sub (227/100)).fun_add
    (((hasDerivAt_id' t).fun_pow 2).const_mul (15/7))).fun_sub
      (((hasDerivAt_id' t).fun_pow 3).const_mul (174/125))).fun_sub
        (((hasDerivAt_id' t).fun_pow 5).const_mul (87/200))
  convert hh using 1
  · rfl
  · dsimp [Pdd]
    norm_num
    ring

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
    (1/200:ℝ)< modelDD t := by
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
  have hid : transformed t-model t=
      R*(N0+Nd w0*(w t-w0)+(w t-w0)^2/20)-R*N (w t) := by
    dsimp [model,transformed,constant0,a]
    linear_combination (-(R/20))*he
  linarith

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
    linear_combination (R/20)*he
  rw [hh]
  symm
  simpa [t0,s0,c0] using scalar_eq_transformed
    (show x0∈Icc (3/5:ℝ) (6/5) by norm_num [x0])

theorem model_contact_derivative : modelD t0= -(s0^2)*scalarD x0 := by
  have hs := contact_signs.1.ne'
  have hn := contact_signs.2.2.2.ne'
  have hD : scalarD x0=1+(9/100)*(s0-c0)+g/s0^2*(c0*(R*(p+g/s0)/N0-1)-13/12) := rfl
  have ha : a=g-R*(g*(p+g*w0)/N0)+(R/10)*w0 := rfl
  have ht : t0=c0/s0 := rfl
  have hw : w0=1/s0 := rfl
  rw [hD]
  dsimp only [modelD]
  rw [contact_w_identity,ha,ht,hw]
  field_simp
  ring

theorem model_lower {t : ℝ} (ht : t∈Icc (3/8:ℝ) (147/100)) :
    (900591/1000000:ℝ)< model t := by
  have hvalue : (4503/5000:ℝ)< model t0 := by rw [model_contact_value]; exact contact_value
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

end SquaresInCircles.Eight.FrameCoreMidContact
end
end
end

section
/-!
## Both orientations of the original core/middle primary axis

The contact estimate cancels the actual core tangent.  Its circle
support is followed by a whole-arc endpoint support.  A positive rounded
core target is handled directly from its original separating inequality.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreMidPrimary
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidScalars FrameCoreMidGeometry

theorem core_primary (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (-(54/125:ℝ)) (109/50))
    (hm : 0≤coreMidPrimary k a B x) :
    (1801/2000:ℝ)<coreMidCost i k a b B x := by
  have hcut := core_primary_cut k hc hB hx.1 hm
  cases k with
  | false =>
      have hs := (FrameCoreArc.signed_label_bounds i hc).1
      have ht := (M_bounds hB).1
      have hch := CorePairGeometry.charge_upper x
      dsimp only [coreMidCost]
      rw [show sign false=-1 from rfl]
      linarith [M_endpoints.1]
  | true => exact False.elim (core_primary_positive_false hc hB ⟨hcut.le,hx.2⟩ hm)

/-- This is the geometric case distinction on the original target:
its sign is negative, or its point is on the straight core side. -/
def CancellationSide (k : Bool) (a B : ℝ) : Prop :=
  k=false ∨ (a=7/12 ∧ B≤1/2)

theorem cancellation_sine {x : ℝ} (hx : x∈Icc (3/5:ℝ) (97/50)) :
    (14/25:ℝ)<Real.sin x := by
  apply sin_endpoint_lower (by norm_num : (0:ℝ)≤3/5)
    (by linarith [FrameLowPair.pi_lower] : (97/50:ℝ)≤Real.pi) hx
  · have hh := Real.sin_ge_sub_cube (show (0:ℝ)≤3/5 by norm_num)
    norm_num at hh
    linarith
  · linarith [trig_primary_cut.1]

theorem cancellation_target (k : Bool) {a B x : ℝ}
    (hc : CoreState a B) (hside : CancellationSide k a B)
    (hx : x∈Icc (3/5:ℝ) (97/50)) :
    (g/Real.sin x)*(7/12)*Real.cos x≤
      -sign k*coreLabel a B+(g/Real.sin x)*a*Real.cos x+
        (g/Real.sin x)*sign k*B*Real.sin x := by
  have hs := cancellation_sine hx
  have hs0 : 0<Real.sin x := by linarith
  have hlam0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) hs0.le
  have hlamU : g/Real.sin x<2 := (div_lt_iff₀ hs0).2 (by dsimp [g]; linarith)
  have hclam := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hlam0
  have hcan : (g/Real.sin x)*Real.sin x=g := div_mul_cancel₀ _ hs0.ne'
  cases k with
  | false =>
      have ht := positive_support (r := -(g/Real.sin x)*Real.cos x)
        (z := (g/Real.sin x)*Real.sin x) hc
        (by dsimp [K]; nlinarith) (by rw [hcan])
      rw [show sign false=-1 from rfl]
      linarith
  | true =>
      have ha : a=7/12 := by
        rcases hside with h | h
        · cases h
        · exact h.1
      subst a
      have hcB : (g/Real.sin x)*1*B*Real.sin x=g*B := by
        rw [mul_one,mul_right_comm,hcan]
      dsimp [coreLabel,sign]
      linarith

theorem cancellation_target_tail (k : Bool) {a B : ℝ}
    (hc : CoreState a B) (hside : CancellationSide k a B) :
    -(g/2)≤ -sign k*coreLabel a B := by
  cases k with
  | false =>
      have hh := (label_bounds hc).1
      simp only [sign]
      dsimp [g]
      linarith
  | true =>
      have hh : a=7/12 ∧ B≤1/2 := by
        rcases hside with h | h
        · cases h
        · exact h
      dsimp [sign,coreLabel]
      rw [hh.1]
      have hb := mul_le_mul_of_nonneg_left hh.2 (show (0:ℝ)≤g by norm_num [g])
      nlinarith

theorem cancellation_circle_support (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hside : CancellationSide k a B) (hx : x∈Icc (3/5:ℝ) (6/5))
    (hm : 0≤ midCorePrimary k b a B x) :
    FrameCoreMidContact.scalar x≤ midCoreCost i k b a B x := by
  have hdom : x∈Icc (3/5:ℝ) (97/50) := ⟨hx.1,by linarith [hx.2]⟩
  have hs0 : 0<Real.sin x := by linarith [cancellation_sine hdom]
  have hlam0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) hs0.le
  have hscaled := mul_nonneg hlam0 hm
  have hsource := middle_minus_label i hb
  have htarget := cancellation_target k hc hside hdom
  have hcircle := circle_linear_lower
    (A_circle ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩)
    (-p-g/Real.sin x) (-q)
  have hn : Real.sqrt ((-p-g/Real.sin x)^2+(-q)^2)=
      FrameCoreMidContact.N (1/Real.sin x) := by
    unfold FrameCoreMidContact.N
    congr 1
    ring
  rw [hn] at hcircle
  have hcan : (g/Real.sin x)*Real.sin x=g := div_mul_cancel₀ _ hs0.ne'
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hw := first_width hxq
  have he : (13*g/12)*(Real.cos x/Real.sin x)=
      (13/12)*(g/Real.sin x)*Real.cos x := by ring
  dsimp [midCorePrimary] at hscaled
  rw [hw.1] at hscaled
  dsimp [midCoreCost,FrameCoreMidContact.scalar,M]
  rw [hw.2,he]
  dsimp [M] at hsource
  nlinarith

theorem cancellation_source_antitone {x : ℝ}
    (hx : x∈Icc (6/5:ℝ) (97/50)) :
    AntitoneOn (linear (-p-g/Real.sin x) (-q)) (Icc b1 b2) := by
  have hs := FrameCoreMidPrimaryContinuation.interval_sine hx
  have hs0 : 0<Real.sin x := by linarith
  have hlam0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) hs0.le
  have hlamU : g/Real.sin x<g/(233/250) := by
    apply (div_lt_iff₀ hs0).2
    dsimp [g] at *
    nlinarith
  have hp : 0≤p+g/Real.sin x := by dsimp [p]; linarith
  apply antiOn_of_hasDeriv_nonpos
  · intro b hb
    exact (linear_hasDerivAt ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩ _
      _).continuousAt.continuousWithinAt
  · intro b hb
    exact linear_hasDerivAt ⟨b1_mem.1.trans hb.1.le,hb.2.le.trans b2_mem.2⟩ _ _
  · intro b hb
    have hr := slope_mid_bounds (Ioo_subset_Icc_self hb)
    have hh := mul_le_mul_of_nonneg_left hr.2.le hp
    have hAd : Ad b=-FrameLowArc.slope b := by
      simp only [Ad,FrameLowArc.slope,neg_div]
    rw [hAd]
    dsimp only [p,q,g] at hh hlamU ⊢
    linarith

theorem cancellation_endpoint_support (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hside : CancellationSide k a B) (hx : x∈Icc (6/5:ℝ) (97/50))
    (hm : 0≤ midCorePrimary k b a B x) :
    FrameCoreMidPrimaryContinuation.G x≤ midCoreCost i k b a B x := by
  have hdom : x∈Icc (3/5:ℝ) (97/50) := ⟨by linarith [hx.1],hx.2⟩
  have hs0 : 0<Real.sin x := by linarith [cancellation_sine hdom]
  have hscaled := mul_nonneg
    (div_nonneg (show (0:ℝ)≤g by norm_num [g]) hs0.le) hm
  have hsource := middle_minus_label i hb
  have htarget := cancellation_target k hc hside hdom
  have hend := cancellation_source_antitone hx hb ⟨b1_lt_b2.le,le_rfl⟩ hb.2
  dsimp [linear] at hend
  rw [A_b2] at hend
  dsimp [FrameCoreMidPrimaryContinuation.G,midCoreCost,midCorePrimary,M,M2,ac] at *
  nlinarith

theorem cancellation_large (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hside : CancellationSide k a B) (hx : (97/50:ℝ)≤x) :
    (1801/2000:ℝ)< midCoreCost i k b a B x := by
  have hsource := (signed_middle_bounds i hb).1
  have htarget := cancellation_target_tail k hc hside
  have hch := CorePairGeometry.charge_upper x
  dsimp [midCoreCost,g] at *
  linarith [M_endpoints.2.2.2]

theorem cancellation_primary (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hside : CancellationSide k a B) (hx : (3/5:ℝ)≤x)
    (hm : 0≤ midCorePrimary k b a B x) :
    (1801/2000:ℝ)< midCoreCost i k b a B x := by
  by_cases hlarge : (97/50:ℝ)≤x
  · exact cancellation_large i k hb hc hside hlarge
  · by_cases hsmall : x≤6/5
    · have hdom : x∈Icc (3/5:ℝ) (6/5) := ⟨hx,hsmall⟩
      exact (lt_trans (by norm_num) (FrameCoreMidContact.scalar_lower hdom)).trans_le
        (cancellation_circle_support i k hb hc hside hdom hm)
    · have hdom : x∈Icc (6/5:ℝ) (97/50) :=
        ⟨(lt_of_not_ge hsmall).le,(lt_of_not_ge hlarge).le⟩
      exact (lt_trans (by norm_num) (FrameCoreMidPrimaryContinuation.G_lower hdom)).trans_le
        (cancellation_endpoint_support i k hb hc hside hdom hm)

theorem rounded_primary_quadrant_false {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤ midCorePrimary true b a B x) : False := by
  have hcore := core_bounds hc
  have hmid := middle_bounds hb
  have ht := FrameLowPair.quadrant hx
  have hA := mul_le_mul_of_nonneg_right
    (show (1/2:ℝ)≤a by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]) ht.2.2.1
  have hB' := mul_le_mul_of_nonneg_right hB ht.1
  have hw := (first_width hx).1
  have hsc : 1≤Real.sin x+Real.cos x := by linarith [width_one_le x]
  dsimp [midCorePrimary,sign] at hm
  rw [hw] at hm
  nlinarith

theorem rounded_primary_cap {b a B x : ℝ}
    (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (Real.pi/2) Real.pi)
    (hm : 0≤ midCorePrimary true b a B x) :
    1/2+Real.sin x+(1/12)*Real.cos x≤A b := by
  have hcore := core_bounds hc
  have ht := second_signs hx
  have hA := mul_le_mul_of_nonpos_right hcore.2.1 ht.2
  have hB' := mul_le_mul_of_nonneg_right hB ht.1
  dsimp [midCorePrimary,sign] at hm
  rw [(second_width hx).1] at hm
  nlinarith

theorem rounded_primary_cut {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (3/5:ℝ) (109/50))
    (hm : 0≤ midCorePrimary true b a B x) : (213/100:ℝ)<x := by
  by_contra! hsmall
  by_cases hfirst : x≤Real.pi/2
  · exact rounded_primary_quadrant_false hb hc hB ⟨by linarith [hx.1],hfirst⟩ hm
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hfirst).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
    have hcap := rounded_primary_cap hc hB hxq hm
    have hs := sin_endpoint_lower (by positivity : (0:ℝ)≤Real.pi/2)
      (by linarith [FrameLowPair.pi_lower] : (213/100:ℝ)≤Real.pi)
      (show x∈Icc (Real.pi/2) (213/100:ℝ) from ⟨hxq.1,hsmall⟩)
      (by norm_num : (847/1000:ℝ)<Real.sin (Real.pi/2)) trig_corner_cut.1
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hsmall
    have ha := (A_mid_bounds hb).2
    linarith [trig_corner_cut.2,a1_precise.2]

theorem rounded_primary_marker {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (213/100:ℝ) (109/50))
    (hm : 0≤ midCorePrimary true b a B x) : M b<(197/500:ℝ) := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hcap := rounded_primary_cap hc hB hxq hm
  have hs := (high_angle_trig ⟨by linarith [hx.1],hx.2⟩).1
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hx.2
  have haL : (5089/4000:ℝ)<A b := by linarith [trig_last.2]
  have hcircle := A_circle ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩
  have hb0 := b1_mem.1.trans hb.1
  have hbU : b<(381/1000:ℝ) := by
    by_contra! hbad
    have ha2 := pow_le_pow_left₀ (show (0:ℝ)≤5089/4000+1/2 by norm_num)
      (show (5089/4000:ℝ)+1/2≤A b+1/2 by linarith) 2
    have hb2 := pow_le_pow_left₀ (show (0:ℝ)≤381/1000+1/2 by norm_num)
      (show (381/1000:ℝ)+1/2≤b+1/2 by linarith) 2
    norm_num [Q0] at hcircle
    nlinarith
  have haU := (A_mid_bounds hb).2.trans a1_precise.2.le
  dsimp [M,p,q,cM]
  linarith

theorem rounded_primary (i : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (3/5:ℝ) (109/50))
    (hm : 0≤ midCorePrimary true b a B x) :
    (1801/2000:ℝ)< midCoreCost i true b a B x := by
  have hcut := rounded_primary_cut hb hc hB hx hm
  have hmark := rounded_primary_marker hb hc hB ⟨hcut.le,hx.2⟩ hm
  have hsource := middle_minus_label i hb
  have htarget := (label_bounds hc).2
  have hch := CorePairGeometry.charge_upper x
  dsimp only [midCoreCost]
  rw [show sign true=1 from rfl]
  linarith

theorem middle_primary (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hx : x∈Icc (-(54/125:ℝ)) (109/50))
    (hm : 0≤ midCorePrimary k b a B x) :
    (1801/2000:ℝ)< midCoreCost i k b a B x := by
  have hcut := middle_primary_cut k hb hc hx.1 hm
  cases k with
  | false => exact cancellation_primary i false hb hc (Or.inl rfl) hcut.le hm
  | true =>
      by_cases hB : B<1/2
      · have hside : CancellationSide true a B := Or.inr ⟨(label_side hc hB).1,hB.le⟩
        exact cancellation_primary i true hb hc hside hcut.le hm
      · exact rounded_primary i hb hc (le_of_not_gt hB) ⟨hcut.le,hx.2⟩ hm

end SquaresInCircles.Eight.FrameCoreMidPrimary
end
end
end

section
/-!
## The secondary axes of the core/middle pairs

A core state and a middle state `B ∈ [b1, b2]` separated along the secondary axis of either square,
at a frame angle in `[-54/125, 109/50]`, have the cost of the pair above `1801/2000`
(`core_secondary`, `middle_secondary`), for both signs of the core tangent, zero included. The
weak margin, times a nonnegative multiplier, is added to the cost, and the support of the middle
state is bounded on the whole middle arc: for a positive target by the support of the whole
circle up to the angle `153/100` (`core_secondary_full_circle`), and beyond, where it decreases
along the arc, by its value at the end `b2` (`positive_target_antitone`,
`core_secondary_endpoint`, `positiveMidEndpoint_lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreMidTransverse
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidScalars FrameCoreMidGeometry

theorem core_secondary_negative (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (-(54/125:ℝ)) Real.pi)
    (hm : 0≤coreMidSecondary i false a b B x) :
    (1801/2000:ℝ)<coreMidCost i false a b B x := by
  have hs := core_secondary_source_floor i false hc hB hm
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have hh : negativeMid B x≤coreMidCost i false a b B x := by
    dsimp only [negativeMid,coreMidCost,coreMidSecondary] at hscaled ⊢
    rw [show sign false=-1 from rfl] at hscaled ⊢
    linarith
  exact (lt_trans (by norm_num) (negativeMid_lower hB hx)).trans_le hh

theorem core_secondary_full_circle (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : x∈Icc 0 (153/100:ℝ))
    (hm : 0≤coreMidSecondary i true a b B x) :
    FrameCoreMidFullCircle.F x≤coreMidCost i true a b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := core_secondary_source_floor i true hc hB hm
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have ht := circle_linear_lower
    (A_circle ⟨b1_mem.1.trans hB.1,hB.2.trans b2_mem.2⟩)
    (-p-g*Real.sin x) (g*Real.cos x-q)
  have hn : Real.sqrt ((-p-g*Real.sin x)^2+(g*Real.cos x-q)^2)=
      FrameCoreMidFullCircle.N x := by
    unfold FrameCoreMidFullCircle.N
    congr 1
    linear_combination g^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  have hw := first_width hxq
  dsimp [coreMidSecondary,coreMidCost,FrameCoreMidFullCircle.F,M] at *
  simp only [sign,ite_true,one_mul] at *
  rw [hw.1] at hscaled
  rw [hw.2]
  nlinarith

theorem positive_target_antitone {x : ℝ}
    (hx : x∈Icc (153/100:ℝ) (109/50)) :
    AntitoneOn (linear (-p-g*Real.sin x) (g*Real.cos x-q)) (Icc b1 b2) := by
  have htrig := high_angle_trig hx
  have hp : 0≤p+g*Real.sin x := by
    have hm := mul_nonneg (show (0:ℝ)≤g by norm_num [g])
      (show 0≤Real.sin x by linarith [htrig.1])
    dsimp [p] at *
    linarith
  apply antiOn_of_hasDeriv_nonpos
  · intro B hB
    exact (linear_hasDerivAt ⟨b1_mem.1.trans hB.1,hB.2.trans b2_mem.2⟩ _
      _).continuousAt.continuousWithinAt
  · intro B hB
    exact linear_hasDerivAt
      ⟨b1_mem.1.trans hB.1.le,hB.2.le.trans b2_mem.2⟩ _ _
  · intro B hB
    have hr := slope_mid_bounds (Ioo_subset_Icc_self hB)
    have hm := mul_le_mul_of_nonneg_left hr.2.le hp
    have hs := mul_le_mul_of_nonneg_left (Real.sin_le_one x)
      (show (0:ℝ)≤(597/1000)*g by norm_num [g])
    have hcos := mul_le_mul_of_nonneg_left htrig.2.le
      (show (0:ℝ)≤g by norm_num [g])
    have hAd : Ad B=-FrameLowArc.slope B := by
      simp only [Ad,FrameLowArc.slope,neg_div]
    rw [hAd]
    dsimp only [p,q,g] at hm hs hcos ⊢
    linarith

def positiveMidEndpoint (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x-M2-g*a2*Real.sin x+g*b2*Real.cos x+g*pairWidth x

theorem core_secondary_endpoint (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (153/100:ℝ) (109/50))
    (hm : 0≤coreMidSecondary i true a b B x) :
    positiveMidEndpoint x≤coreMidCost i true a b B x := by
  have hs := core_secondary_source_floor i true hc hB hm
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have ht := positive_target_antitone hx hB ⟨b1_lt_b2.le,le_rfl⟩ hB.2
  dsimp [linear] at ht
  rw [A_b2] at ht
  dsimp [positiveMidEndpoint,coreMidCost,coreMidSecondary,M,M2] at *
  simp only [sign,ite_true,one_mul] at *
  nlinarith

theorem positiveMidEndpoint_lower {x : ℝ}
    (hx : x∈Icc (153/100:ℝ) (109/50)) :
    (4503/5000:ℝ)<positiveMidEndpoint x := by
  by_cases hq : x≤Real.pi/2
  · have hwidth := first_width
      (show x∈Icc 0 (Real.pi/2) from ⟨by linarith [hx.1],hq⟩)
    have he : positiveMidEndpoint x=positiveMidFirst x := by
      dsimp [positiveMidEndpoint,positiveMidFirst,trigAffine,ap,cp]
      rw [hwidth.1,hwidth.2]
      ring
    rw [he]
    exact positiveMidFirst_lower ⟨hx.1,hq⟩
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hq).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
    have hwidth := second_width hxq
    have he : positiveMidEndpoint x=positiveMidSecond x := by
      dsimp [positiveMidEndpoint,positiveMidSecond,trigAffine,ap,cp]
      rw [hwidth.1,hwidth.2]
      ring
    rw [he]
    exact positiveMidSecond_lower hxq

theorem core_secondary_positive (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (-(54/125:ℝ)) (109/50))
    (hm : 0≤coreMidSecondary i true a b B x) :
    (1801/2000:ℝ)<coreMidCost i true a b B x := by
  have hx0 := core_secondary_positive_cut i hc hB hx.1 hm
  by_cases hcut : x≤153/100
  · have hdom : x∈Icc 0 (153/100:ℝ) := ⟨by linarith,hcut⟩
    exact (lt_trans (by norm_num) (FrameCoreMidFullCircle.lower hdom)).trans_le
      (core_secondary_full_circle i hc hB hdom hm)
  · have hdom : x∈Icc (153/100:ℝ) (109/50) := ⟨(lt_of_not_ge hcut).le,hx.2⟩
    exact (lt_trans (by norm_num) (positiveMidEndpoint_lower hdom)).trans_le
      (core_secondary_endpoint i hc hB hdom hm)

theorem core_secondary (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (-(54/125:ℝ)) (109/50))
    (hm : 0≤coreMidSecondary i k a b B x) :
    (1801/2000:ℝ)<coreMidCost i k a b B x := by
  cases k with
  | false =>
    exact core_secondary_negative i hc hB
      ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩ hm
  | true => exact core_secondary_positive i hc hB hx hm

theorem middle_secondary_negative {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hx : x∈Icc (-(54/125:ℝ)) Real.pi)
    (hm : 0≤ midCoreSecondary true false b a B x) :
    (1801/2000:ℝ)< midCoreCost true false b a B x := by
  have hs := loss_antitone (show (449/500:ℝ)≤g by norm_num [g])
    hb ⟨b1_lt_b2.le,le_rfl⟩ hb.2
  simp only [M_b2] at hs
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have hsin := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin x)
    (show (0:ℝ)≤g by norm_num [g])
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one x)
    (show (0:ℝ)≤g by norm_num [g])
  have ht := positive_support (r := g*Real.sin x) (z := g*Real.cos x) hc
    (by dsimp only [K,g] at hsin ⊢; linarith) (by linarith)
  have hh : negativeCore x≤ midCoreCost true false b a B x := by
    dsimp only [negativeCore,midCoreCost,midCoreSecondary,ac] at hscaled ⊢
    rw [show sign true=1 from rfl,show sign false=-1 from rfl] at hscaled ⊢
    linarith
  exact (lt_trans (by norm_num) (negativeCore_lower hx)).trans_le hh

theorem middle_secondary_positive {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hx : x∈Icc (-(54/125:ℝ)) (109/50))
    (hm : 0≤ midCoreSecondary true true b a B x) :
    (1801/2000:ℝ)< midCoreCost true true b a B x := by
  have hcut := mid_secondary_positive_cut hb hc hx.1 hm
  have hs := loss_antitone (show (449/500:ℝ)≤1 by norm_num)
    hb ⟨b1_lt_b2.le,le_rfl⟩ hb.2
  simp only [M_b2,one_mul] at hs
  have ht := negative_support (x := x) hc
  have hh : positiveCore x≤ midCoreCost true true b a B x := by
    dsimp only [positiveCore,midCoreCost,midCoreSecondary] at hm ⊢
    rw [show sign true=1 from rfl] at hm ⊢
    linarith
  have hdom : x∈Icc (6/5:ℝ) Real.pi :=
    ⟨hcut.le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  exact (lt_trans (by norm_num) (positiveCore_lower hdom)).trans_le hh

theorem middle_secondary (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hx : x∈Icc (-(54/125:ℝ)) (109/50))
    (hm : 0≤ midCoreSecondary i k b a B x) :
    (1801/2000:ℝ)< midCoreCost i k b a B x := by
  have hi := mid_secondary_source_positive i k hb hc hm
  subst i
  cases k with
  | false =>
    exact middle_secondary_negative hb hc
      ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩ hm
  | true => exact middle_secondary_positive hb hc hx hm

end SquaresInCircles.Eight.FrameCoreMidTransverse
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreMidPair
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FrameCoreMidGeometry FrameCoreMidTransverse FrameCoreMidPrimary

theorem core_mid_angle (s t : FramePair.State)
    (ht : t.branch=.middle) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    -(54/125:ℝ)<x := by
  have hs := s.offset_range
  have hh := middle_offset_bounds t ht
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem mid_core_angle (s t : FramePair.State)
    (hs : s.branch=.middle) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    -(54/125:ℝ)<x := by
  have ht := t.offset_range
  have hh := middle_offset_bounds s hs
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem state_core_mid_cost (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.middle) (x : ℝ) :
    s.cost t x=coreMidCost s.positive t.positive s.a s.b t.b x := by
  rw [State.cost,state_core_label s hs,state_mid_label t ht]
  rfl

theorem state_mid_core_cost (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch.type=0) (x : ℝ) :
    s.cost t x=midCoreCost s.positive t.positive s.b t.a t.b x := by
  rw [State.cost,state_mid_label s hs,state_core_label t ht]
  rfl

theorem state_core_mid_secondary (s t : FramePair.State)
    (ht : t.branch=.middle) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤coreMidSecondary s.positive t.positive s.a s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,(state_mid_chart t ht).1]
  rfl

theorem state_core_mid_primary (s t : FramePair.State)
    (ht : t.branch=.middle) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤coreMidPrimary t.positive s.a t.b x := by
  simp only [State.Feasible,forwardMargin,
    (state_mid_chart t ht).1]
  rfl

theorem state_mid_core_secondary (s t : FramePair.State) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤ midCoreSecondary s.positive t.positive s.b t.a t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero]
  rfl

theorem state_mid_core_primary (s t : FramePair.State)
    (hs : s.branch=.middle) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤ midCorePrimary t.positive s.b t.a t.b x := by
  simp only [State.Feasible,forwardMargin,
    (state_mid_chart s hs).1]
  rfl

theorem source_core_secondary (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.middle) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hcore := state_core_chart s hs
  have hmid := (state_mid_chart t ht).2
  rw [state_core_mid_cost s t hs ht]
  by_cases hlarge : (109/50:ℝ)≤x
  · exact core_mid_tail s.positive t.positive hcore hmid hlarge
  · exact core_secondary s.positive t.positive hcore hmid
      ⟨(core_mid_angle s t ht hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_core_mid_secondary s t ht x).mp hm)

theorem source_core_primary (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.middle) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hcore := state_core_chart s hs
  have hmid := (state_mid_chart t ht).2
  rw [state_core_mid_cost s t hs ht]
  by_cases hlarge : (109/50:ℝ)≤x
  · exact core_mid_tail s.positive t.positive hcore hmid hlarge
  · exact core_primary s.positive t.positive hcore hmid
      ⟨(core_mid_angle s t ht hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_core_mid_primary s t ht x).mp hm)

theorem source_middle_secondary (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch.type=0) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hmid := (state_mid_chart s hs).2
  have hcore := state_core_chart t ht
  rw [state_mid_core_cost s t hs ht]
  by_cases hlarge : (109/50:ℝ)≤x
  · exact mid_core_tail s.positive t.positive hmid hcore hlarge
  · exact middle_secondary s.positive t.positive hmid hcore
      ⟨(mid_core_angle s t hs hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_mid_core_secondary s t x).mp hm)

theorem source_middle_primary (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch.type=0) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hmid := (state_mid_chart s hs).2
  have hcore := state_core_chart t ht
  rw [state_mid_core_cost s t hs ht]
  by_cases hlarge : (109/50:ℝ)≤x
  · exact mid_core_tail s.positive t.positive hmid hcore hlarge
  · exact middle_primary s.positive t.positive hmid hcore
      ⟨(mid_core_angle s t hs hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_mid_core_primary s t hs x).mp hm)

/-- All original weak witnesses in the core-to-middle orientation. -/
theorem core_mid_pair (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.middle) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(1801/2000:ℝ) := by
    rw [hs,ht]
    norm_num [Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_core_secondary s t hs ht hgap hm
  · have hh := source_middle_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_middle_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_core_primary s t hs ht hgap hm

/-- All original weak witnesses in the middle-to-core orientation. -/
theorem mid_core_pair (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch.type=0) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(1801/2000:ℝ) := by
    rw [hs,ht]
    norm_num [Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_middle_secondary s t hs ht hgap hm
  · have hh := source_core_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_core_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_middle_primary s t hs ht hgap hm

theorem core_mid_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : (branchOf C i).type=0) (hj : branchOf C (next i)=.middle)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact core_mid_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

theorem mid_core_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.middle) (hj : (branchOf C (next i)).type=0)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact mid_core_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.FrameCoreMidPair
end
end
end
