module

public import SquaresInCircles.Eight.TableFree.FrameCoreMidFullCircle

/-!
# Exact contact data for the core/middle cancellation support

All numbers refer to the single intrinsic contact angle `27/25`.
The sine and cosine bounds are alternating Taylor inequalities; both
radical bounds follow by squaring.  The support and its derivative are
then enclosed by sign-aware rational substitutions.  No sample of a
continuous curvature or covering interval is used.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreMidContact
open FramePair FrameCircleArc FrameMidArc

def w (t : ℝ) : ℝ := Real.sqrt (1+t^2)
def wd (t : ℝ) : ℝ := t/w t
def wdd (t : ℝ) : ℝ := 1/(w t)^3
def N (z : ℝ) : ℝ := Real.sqrt ((p+g*z)^2+q^2)
def Nd (z : ℝ) : ℝ := g*(p+g*z)/N z
def Ndd (z : ℝ) : ℝ := g^2*q^2/(N z)^3

theorem w_pos (t : ℝ) : 0<w t := Real.sqrt_pos.mpr (by positivity)
theorem w_sq (t : ℝ) : (w t)^2=1+t^2 := Real.sq_sqrt (by positivity)
theorem w_power (t : ℝ) (n : ℕ) : (w t)^(n+2)=(w t)^n*(1+t^2) := by
  rw [pow_add,w_sq]

theorem w_deriv (t : ℝ) : HasDerivAt w (wd t) t := by
  have hh := ((hasDerivAt_const t (1:ℝ)).fun_add ((hasDerivAt_id' t).fun_pow 2)).sqrt
    (show 1+t^2≠0 by positivity)
  show HasDerivAt (fun y => Real.sqrt (1+y^2)) _ t
  convert hh using 1
  have hn : Real.sqrt (1+t^2)≠0 := (w_pos t).ne'
  dsimp [wd,w]
  field_simp
  ring

theorem wd_deriv (t : ℝ) : HasDerivAt wd (wdd t) t := by
  have hn := (w_pos t).ne'
  convert (hasDerivAt_id t).div (w_deriv t) hn using 1
  · rfl
  · dsimp [wd,wdd]
    field_simp [hn]
    nlinarith only [w_sq t]

theorem N_pos (z : ℝ) : 0<N z := by
  apply Real.sqrt_pos.mpr
  have hq : 0<q^2 := by norm_num [q]
  linarith [sq_nonneg (p+g*z)]

theorem N_sq (z : ℝ) : (N z)^2=(p+g*z)^2+q^2 := Real.sq_sqrt (by positivity)
theorem N_power (z : ℝ) (n : ℕ) :
    (N z)^(n+2)=(N z)^n*((p+g*z)^2+q^2) := by rw [pow_add,N_sq]

theorem N_deriv (z : ℝ) : HasDerivAt N (Nd z) z := by
  have hpos : (p+g*z)^2+q^2≠0 := by
    have hq : 0<q^2 := by norm_num [q]
    nlinarith [sq_nonneg (p+g*z)]
  have hh := (((((hasDerivAt_id' z).const_mul g).const_add p).fun_pow 2).add_const
    (q^2)).sqrt hpos
  show HasDerivAt (fun y => Real.sqrt ((p+g*y)^2+q^2)) _ z
  convert hh using 1
  have hn : Real.sqrt ((p+g*z)^2+q^2)≠0 := (N_pos z).ne'
  dsimp [Nd,N]
  field_simp

theorem Nd_deriv (z : ℝ) : HasDerivAt Nd (Ndd z) z := by
  have hn := (N_pos z).ne'
  have hh := ((((hasDerivAt_id' z).const_mul g).const_add p).const_mul g).fun_div
    (N_deriv z) hn
  convert hh using 1
  · rfl
  · have hN2 := N_sq z
    dsimp [Nd,Ndd]
    field_simp
    rw [hN2]
    ring

def x0 : ℝ := 27/25
def s0 : ℝ := Real.sin x0
def c0 : ℝ := Real.cos x0
def t0 : ℝ := c0/s0
def w0 : ℝ := 1/s0
def N0 : ℝ := N w0
def a : ℝ := g-R*Nd w0+(R/10)*w0

def sLo : ℝ := 440978903/500000000
def sHi : ℝ := 881957807/1000000000
def cLo : ℝ := 117832091/250000000
def cHi : ℝ := 94265673/200000000
def rLo : ℝ := 1978787507/1000000000
def rHi : ℝ := 494696877/250000000
def nLo : ℝ := 784517747/250000000
def nHi : ℝ := 3138070991/1000000000

theorem contact_trig : sLo<s0 ∧ s0<sHi ∧ cLo<c0 ∧ c0<cHi := by
  have hsL := HighOrderTaylor.S15_le_sin (show 0≤x0 by norm_num [x0])
  have hsU := HighOrderTaylor.sin_le_S17 (show 0≤x0 by norm_num [x0])
  have hcL := HighOrderTaylor.C18_le_cos (show 0≤x0 by norm_num [x0])
  have hcU := HighOrderTaylor.cos_le_C16 (show 0≤x0 by norm_num [x0])
  norm_num [x0,HighOrderTaylor.S17,HighOrderTaylor.S15,HighOrderTaylor.S13,
    HighOrderTaylor.S11,HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,
    HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,
    Arithmetic.cos8] at hsL hsU hcL hcU
  dsimp [s0,c0,x0,sLo,sHi,cLo,cHi]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem contact_signs : 0<s0 ∧ 0<c0 ∧ 0<w0 ∧ 0<N0 := by
  have hs : 0<s0 := by linarith [contact_trig.1,show (0:ℝ)<sLo by norm_num [sLo]]
  have hc : 0<c0 := by linarith [contact_trig.2.2.1,show (0:ℝ)<cLo by norm_num [cLo]]
  exact ⟨hs,hc,one_div_pos.mpr hs,N_pos w0⟩

theorem contact_radius : rLo<R ∧ R<rHi := by
  have he := R_sq
  have hn := R_pos
  dsimp [rLo,rHi,Q0] at *
  constructor <;> nlinarith

theorem contact_w_bounds : 1/sHi<w0 ∧ w0<1/sLo := by
  have hs := contact_signs.1
  dsimp [w0]
  constructor
  · apply (div_lt_div_iff₀ (by norm_num [sHi] : 0<sHi) hs).2
    nlinarith [contact_trig.2.1]
  · apply (div_lt_div_iff₀ hs (by norm_num [sLo] : 0<sLo)).2
    nlinarith [contact_trig.1]

theorem contact_norm : nLo<N0 ∧ N0<nHi := by
  have hw := contact_w_bounds
  have he := N_sq w0
  change N0^2=(p+g*w0)^2+q^2 at he
  have hx0 : 0<p+g*w0 := by dsimp [p,g]; linarith [contact_signs.2.2.1]
  have hxL : p+g/sHi<p+g*w0 := by
    have hm := mul_lt_mul_of_pos_left hw.1 (show 0<g by norm_num [g])
    rw [mul_one_div] at hm
    linarith
  have hxU : p+g*w0<p+g/sLo := by
    have hm := mul_lt_mul_of_pos_left hw.2 (show 0<g by norm_num [g])
    rw [mul_one_div] at hm
    linarith
  have hsL := pow_le_pow_left₀ (show 0≤p+g/sHi by norm_num [p,g,sHi]) hxL.le 2
  have hsU := pow_le_pow_left₀ hx0.le hxU.le 2
  have hnumL : nLo^2<(p+g/sHi)^2+q^2 := by norm_num [nLo,p,g,sHi,q]
  have hnumU : (p+g/sLo)^2+q^2<nHi^2 := by norm_num [nHi,p,g,sLo,q]
  have hn := contact_signs.2.2.2
  constructor <;> dsimp [nLo,nHi] at * <;> nlinarith

def zLo : ℝ := rLo*(p+g/sHi)/nHi
def zHi : ℝ := rHi*(p+g/sLo)/nLo
def Z0 : ℝ := R*(p+g*w0)/N0

theorem contact_Z : zLo<Z0 ∧ Z0<zHi := by
  have hr := contact_radius
  have hn := contact_norm
  have hw := contact_w_bounds
  have hR := R_pos
  have hN := contact_signs.2.2.2
  have hx : 0<p+g*w0 := by dsimp [p,g]; linarith [contact_signs.2.2.1]
  have hxL : p+g/sHi≤p+g*w0 := by
    have hm := mul_lt_mul_of_pos_left hw.1 (show 0<g by norm_num [g])
    rw [mul_one_div] at hm
    linarith
  have hxU : p+g*w0≤p+g/sLo := by
    have hm := mul_lt_mul_of_pos_left hw.2 (show 0<g by norm_num [g])
    rw [mul_one_div] at hm
    linarith
  have hpL := mul_le_mul hxL hr.1.le
    (show 0≤rLo by norm_num [rLo]) hx.le
  have hpU := mul_le_mul hxU hr.2.le hR.le
    (show 0≤p+g/sLo by norm_num [p,g,sLo])
  constructor
  · apply (div_lt_div_iff₀ (by norm_num [nHi] : 0<nHi) hN).2
    have hmul := mul_lt_mul_of_pos_left hn.2
      (show 0<rLo*(p+g/sHi) by norm_num [rLo,p,g,sHi])
    have hscaled := mul_le_mul_of_nonneg_left hpL (show 0≤nHi by norm_num [nHi])
    nlinarith
  · apply (div_lt_div_iff₀ hN (by norm_num [nLo] : 0<nLo)).2
    have hmul := mul_lt_mul_of_pos_left hn.1
      (show 0<rHi*(p+g/sLo) by norm_num [rHi,p,g,sLo])
    have hscaled := mul_le_mul_of_nonneg_left hpU (show 0≤nLo by norm_num [nLo])
    nlinarith

theorem a_lower : -(541/1000:ℝ)<a := by
  have hz := contact_Z.2
  have hw := contact_w_bounds.1
  have hr := contact_radius.1
  have hmul := mul_le_mul hw.le hr.le
    (show 0≤rLo by norm_num [rLo]) contact_signs.2.2.1.le
  have hscaled := mul_lt_mul_of_pos_left hz (show 0<g by norm_num [g])
  have hnum : -(541/1000:ℝ)<g-g*zHi+rLo/(10*sHi) := by
    norm_num [g,zHi,rLo,rHi,p,sLo,sHi,nLo]
  have hid : a=g-g*Z0+(R/10)*w0 := by
    dsimp [a,Nd,Z0,N0]
    ring
  have hRw : rLo/(10*sHi)≤(R/10)*w0 := by
    have h1 : rLo/(10*sHi)=(1/sHi*rLo)/10 := by ring
    have h2 : (R/10)*w0=(w0*R)/10 := by ring
    rw [h1,h2]
    linarith
  rw [hid]
  linarith

def scalar (x : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x+Real.cos x-1)-cM+(p+q+g)/2+
    g/Real.sin x+(13*g/12)*(Real.cos x/Real.sin x)-R*N (1/Real.sin x)

def scalarD (x : ℝ) : ℝ :=
  1+(9/100)*(Real.sin x-Real.cos x)+
    g/(Real.sin x)^2*
      (Real.cos x*(R*(p+g/Real.sin x)/N (1/Real.sin x)-1)-13/12)

theorem contact_value : (4503/5000:ℝ)<scalar x0 := by
  have ht := contact_trig
  have hr := contact_radius
  have hn := contact_norm
  have hs := contact_signs.1
  have hc := contact_signs.2.1
  have hR := R_pos
  have hN := contact_signs.2.2.2
  have hw := contact_w_bounds.1
  have hratio : cLo/sHi<c0/s0 := by
    apply (div_lt_div_iff₀ (by norm_num [sHi] : 0<sHi) hs).2
    exact mul_lt_mul ht.2.2.1 ht.2.1.le hs hc.le
  have hroot := mul_le_mul hn.2.le hr.2.le hR.le
    (show 0≤nHi by norm_num [nHi])
  have hwg := mul_lt_mul_of_pos_left hw (show 0<g by norm_num [g])
  have hrc := mul_lt_mul_of_pos_left hratio (show 0<13*g/12 by norm_num [g])
  have hnum : (4503/5000:ℝ)<x0-(9/100)*(sHi+cHi-1)-cM+(p+q+g)/2+
      g/sHi+(13*g/12)*(cLo/sHi)-rHi*nHi := by
    norm_num [x0,sHi,cHi,cLo,cM,p,q,g,rHi,nHi]
  change (4503/5000:ℝ)<x0-(9/100)*(s0+c0-1)-cM+(p+q+g)/2+
    g/s0+(13*g/12)*(c0/s0)-R*N0
  dsimp [w0] at hwg
  rw [mul_one_div,mul_one_div] at hwg
  linarith [ht.2.1,ht.2.2.2]

def bracketLo : ℝ := cLo*(zLo-1)-13/12
def bracketHi : ℝ := cHi*(zHi-1)-13/12

theorem contact_bracket :
    bracketLo<c0*(Z0-1)-13/12 ∧ c0*(Z0-1)-13/12<bracketHi ∧ bracketHi<0 := by
  have hz := contact_Z
  have ht := contact_trig
  have hzL : 0<zLo-1 := by norm_num [zLo,rLo,p,g,sHi,nHi]
  have hzU : 0<zHi-1 := by norm_num [zHi,rHi,p,g,sLo,nLo]
  have hZ0 : 0<Z0-1 := by linarith [hz.1]
  have hlo := mul_lt_mul ht.2.2.1 (show zLo-1≤Z0-1 by linarith)
    hzL contact_signs.2.1.le
  have hhi := mul_lt_mul ht.2.2.2 (show Z0-1≤zHi-1 by linarith)
    hZ0 (by norm_num [cHi] : (0:ℝ)≤cHi)
  refine ⟨by dsimp [bracketLo]; linarith,by dsimp [bracketHi]; linarith,?_⟩
  norm_num [bracketHi,cHi,zHi,rHi,p,g,sLo,nLo]

theorem contact_derivative : |scalarD x0|<(3/10000:ℝ) := by
  have ht := contact_trig
  have hs := contact_signs.1
  have hb := contact_bracket
  have hsL := pow_le_pow_left₀ (show 0≤ sLo by norm_num [sLo]) ht.1.le 2
  have hsU := pow_le_pow_left₀ hs.le ht.2.1.le 2
  have hneg : c0*(Z0-1)-13/12<0 := hb.2.1.trans hb.2.2
  have hL : bracketLo/sLo^2<(c0*(Z0-1)-13/12)/s0^2 := by
    apply (div_lt_div_iff₀ (by norm_num [sLo] : (0:ℝ)<sLo^2) (sq_pos_of_pos hs)).2
    have hm := mul_le_mul_of_nonpos_left hsL (by linarith [hb.1,hneg] : bracketLo≤0)
    have hn := mul_lt_mul_of_pos_right hb.1 (by norm_num [sLo] : (0:ℝ)<sLo^2)
    nlinarith
  have hU : (c0*(Z0-1)-13/12)/s0^2<bracketHi/sHi^2 := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos hs) (by norm_num [sHi] : (0:ℝ)<sHi^2)).2
    have hm := mul_le_mul_of_nonpos_left hsU hneg.le
    have hn := mul_lt_mul_of_pos_right hb.2.1 (sq_pos_of_pos hs)
    nlinarith
  have hLg := mul_lt_mul_of_pos_left hL (show 0<g by norm_num [g])
  have hUg := mul_lt_mul_of_pos_left hU (show 0<g by norm_num [g])
  have hnumL : -(3/10000:ℝ)<1+(9/100)*(sLo-cHi)+g*(bracketLo/sLo^2) := by
    norm_num [sLo,cHi,g,bracketLo,cLo,zLo,rLo,p,sHi,nHi]
  have hnumU : 1+(9/100)*(sHi-cLo)+g*(bracketHi/sHi^2)<(3/10000:ℝ) := by
    norm_num [sHi,cLo,g,bracketHi,cHi,zHi,rHi,p,sLo,nLo]
  have hid : scalarD x0=1+(9/100)*(s0-c0)+g*((c0*(Z0-1)-13/12)/s0^2) := by
    dsimp [scalarD,s0,c0,Z0,N0,w0]
    ring
  rw [hid,abs_lt]
  constructor <;> nlinarith [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]

end SquaresInCircles.Eight.TableFree.FrameCoreMidContact
