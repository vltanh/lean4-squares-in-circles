module

public import SquaresInCircles.Eight.TableFree.FrameLowMidGeometry
public import SquaresInCircles.Eight.TableFree.CircularNorm
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor

/-!
# Both complete low/middle primary circle supports

The Boolean parameter distinguishes the middle target from the low
target.  Each actual norm has positive radicand on the whole real line.
The exact circular-norm identity gives concavity on each physical
quadrant; only the three actual endpoints are evaluated.
Uncompiled source draft of HAND_FOUR_TYPE_SCALAR_REPLACEMENTS §5.4.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowMidPrimaryScalars
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus

def p (i : Bool) : ℝ := if i then FrameMidArc.p else FrameLowArc.u
def q (i : Bool) : ℝ := if i then FrameMidArc.q else FrameLowArc.v
def lam (i : Bool) : ℝ := if i then 9/10 else 47/50
def start (i : Bool) : ℝ := if i then 3/2 else 13/10
def normCap (i : Bool) : ℝ := if i then 9/5 else 14/25
def determinantCap (i : Bool) : ℝ := if i then 15 else 21/100
def initialNorm (i : Bool) : ℝ := if i then 8/5 else 6/25
def middleNorm (i : Bool) : ℝ := if i then 5/3 else 431/1000
def finalNorm (i : Bool) : ℝ := if i then 9/5 else 279/500
def sourceFloor (i : Bool) : ℝ := if i then
  -(30683/100000)-(9/10)*(1298747249/1000000000) else
  -(455511/1000000)-(47/50)*(599628031/500000000)
def targetConstant (i : Bool) : ℝ := if i then cM else
  -FrameLowArc.u*(1414575670/1000000000)
def K (i : Bool) : ℝ := 9/100+sourceFloor i-targetConstant i+(p i+q i+lam i)/2
def N (i : Bool) (x : ℝ) : ℝ :=
  CircularNorm.norm ((p i)^2+(q i)^2+(lam i)^2) (-2*lam i*p i) (-2*lam i*q i) x
def Nd (i : Bool) (x : ℝ) : ℝ :=
  CircularNorm.d1 ((p i)^2+(q i)^2+(lam i)^2) (-2*lam i*p i) (-2*lam i*q i) x
def Ndd (i : Bool) (x : ℝ) : ℝ :=
  CircularNorm.d2 ((p i)^2+(q i)^2+(lam i)^2) (-2*lam i*p i) (-2*lam i*q i) x
def cosCoefficient (i second : Bool) : ℝ := if second then lam i-9/100 else 9/100
def F (i second : Bool) (x : ℝ) : ℝ :=
  x+K i-(9/100)*Real.sin x-cosCoefficient i second*Real.cos x-R*N i x
def Fd (i second : Bool) (x : ℝ) : ℝ :=
  1-(9/100)*Real.cos x+cosCoefficient i second*Real.sin x-R*Nd i x
def Fdd (i second : Bool) (x : ℝ) : ℝ :=
  (9/100)*Real.sin x+cosCoefficient i second*Real.cos x-R*Ndd i x
def left (i second : Bool) : ℝ := if second then Real.pi/2 else start i
def right (second : Bool) : ℝ := if second then 171/100 else Real.pi/2

theorem parameter_bounds (i : Bool) :
    0<p i ∧ 0<q i ∧ 0<lam i ∧
      (13/10:ℝ)≤start i ∧ start i≤3/2 ∧ 0<normCap i ∧
      0<determinantCap i ∧ determinantCap i<((p i)^2+(q i)^2-(lam i)^2)^2 := by
  cases i <;>
    norm_num [p,q,lam,start,normCap,determinantCap,FrameMidArc.p,FrameMidArc.q,
      FrameLowArc.u,FrameLowArc.v]

theorem energy_positive (i : Bool) (x : ℝ) :
    0<CircularNorm.energy ((p i)^2+(q i)^2+(lam i)^2)
      (-2*lam i*p i) (-2*lam i*q i) x := by
  have hid : CircularNorm.energy ((p i)^2+(q i)^2+(lam i)^2)
      (-2*lam i*p i) (-2*lam i*q i) x=
        (p i-lam i*Real.cos x)^2+(q i-lam i*Real.sin x)^2 := by
    dsimp [CircularNorm.energy]
    linear_combination -(lam i)^2*(Real.sin_sq_add_cos_sq x)
  have hp : 0<q i-lam i*Real.sin x := by
    have hs := Real.sin_le_one x
    cases i <;>
      dsimp [q,lam,FrameMidArc.q,FrameLowArc.v] <;> linarith
  rw [hid]
  nlinarith [sq_nonneg (p i-lam i*Real.cos x),sq_pos_of_pos hp]

theorem N_positive (i : Bool) (x : ℝ) : 0<N i x := CircularNorm.norm_pos (energy_positive i x)
theorem N_square (i : Bool) (x : ℝ) :
    (N i x)^2=(p i)^2+(q i)^2+(lam i)^2-
      2*lam i*(p i*Real.cos x+q i*Real.sin x) := by
  have hh := CircularNorm.norm_sq (energy_positive i x).le
  convert hh using 1 <;> dsimp [N,CircularNorm.energy] <;> ring
theorem N_deriv (i : Bool) (x : ℝ) : HasDerivAt (N i) (Nd i x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive i x)
theorem Nd_deriv (i : Bool) (x : ℝ) : HasDerivAt (Nd i) (Ndd i x) x :=
  CircularNorm.d1_hasDerivAt (energy_positive i x)

theorem trig_window {x : ℝ} (hx : x∈Icc (13/10:ℝ) (171/100)) :
    (24/25:ℝ)<Real.sin x ∧ Real.cos x<27/100 := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤13/10 by norm_num)
  have hsU := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤171/100 by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤13/10 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hsL hsU hcU
  have hs := sin_endpoint_lower (by norm_num : (0:ℝ)≤13/10)
    (by linarith [FrameLowPair.pi_lower] : (171/100:ℝ)≤Real.pi) hx
    (by linarith : (24/25:ℝ)<Real.sin (13/10:ℝ))
    (by linarith : (24/25:ℝ)<Real.sin (171/100:ℝ))
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤13/10) (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  exact ⟨hs,by linarith⟩

theorem N_monotone (i : Bool) : MonotoneOn (N i) (Icc (13/10:ℝ) (171/100)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (N_deriv i x).continuousAt.continuousWithinAt
  · exact fun x _ => N_deriv i x
  · intro x hx
    have ht := trig_window (Ioo_subset_Icc_self hx)
    have hn := N_positive i x
    have hforce : 0≤p i*Real.sin x-q i*Real.cos x := by
      cases i <;> dsimp [p,q,FrameMidArc.p,FrameMidArc.q,FrameLowArc.u,FrameLowArc.v]
      all_goals linarith
    have hλ := (parameter_bounds i).2.2.1
    dsimp [Nd,CircularNorm.d1,CircularNorm.slope]
    apply div_nonneg _ (by positivity)
    nlinarith

theorem endpoint_norms (i : Bool) :
    N i (start i)<initialNorm i ∧ N i (Real.pi/2)<middleNorm i ∧
      N i (171/100)<finalNorm i := by
  have hfirst := N_square i (start i)
  have hmiddle := N_square i (Real.pi/2)
  have hlast := N_square i (171/100)
  have h0 : 0≤start i := by linarith [(parameter_bounds i).2.2.2.1]
  have hs0 := HighOrderTaylor.S11_le_sin h0
  have hc0 := HighOrderTaylor.C14_le_cos h0
  have hs1 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤171/100 by norm_num)
  have hc1 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤171/100 by norm_num)
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_zero,mul_one,zero_add] at hmiddle
  have hn0 := N_positive i (start i)
  have hnm := N_positive i (Real.pi/2)
  have hn1 := N_positive i (171/100)
  cases i <;>
    norm_num [start,p,q,lam,initialNorm,middleNorm,finalNorm,
      FrameMidArc.p,FrameMidArc.q,FrameLowArc.u,FrameLowArc.v,
      HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  all_goals repeat' constructor <;> nlinarith

theorem N_upper (i : Bool) {x : ℝ} (hx : x∈Icc (start i) (171/100)) :
    N i x<normCap i := by
  have hh := N_monotone i
    ⟨(parameter_bounds i).2.2.2.1.trans hx.1,hx.2⟩ ⟨by norm_num,le_rfl⟩ hx.2
  have hend := (endpoint_norms i).2.2
  have hcap : finalNorm i≤normCap i := by cases i <;> norm_num [finalNorm,normCap]
  exact (hh.trans_lt hend).trans_le hcap

def curvatureFloor (i : Bool) : ℝ :=
  determinantCap i/(4*(normCap i)^3)-normCap i/4

theorem Ndd_lower (i : Bool) {x : ℝ} (hx : x∈Icc (start i) (171/100)) :
    curvatureFloor i≤Ndd i x := by
  have hp := parameter_bounds i
  have hn := N_positive i x
  have hbar : 0<normCap i := hp.2.2.2.2.2.1
  have hcap := N_upper i hx
  have hpow := pow_le_pow_left₀ hn.le hcap.le 3
  have hid := CircularNorm.curvature_identity (energy_positive i x)
  change Ndd i x+N i x/4=
    (((p i)^2+(q i)^2+(lam i)^2)^2-(-2*lam i*p i)^2-(-2*lam i*q i)^2)/
      (4*(N i x)^3) at hid
  have he : ((p i)^2+(q i)^2+(lam i)^2)^2-(-2*lam i*p i)^2-(-2*lam i*q i)^2=
      ((p i)^2+(q i)^2-(lam i)^2)^2 := by ring
  rw [he] at hid
  have hd : 0<4*(normCap i)^3 := by positivity
  have hden : 0<4*(N i x)^3 := by positivity
  have hquot : determinantCap i/(4*(normCap i)^3)≤
      ((p i)^2+(q i)^2-(lam i)^2)^2/(4*(N i x)^3) := by
    apply (div_le_div_iff₀ hd hden).2
    have h1 := mul_le_mul_of_nonneg_left hpow hp.2.2.2.2.2.2.1.le
    have h2 := mul_le_mul_of_nonneg_right hp.2.2.2.2.2.2.2.le
      (pow_nonneg hp.2.2.2.2.2.1.le 3)
    nlinarith
  dsimp [curvatureFloor]
  linarith

theorem F_deriv (i second : Bool) (x : ℝ) : HasDerivAt (F i second) (Fd i second x) x := by
  convert ((((hasDerivAt_id x).add_const (K i)).sub
    ((Real.hasDerivAt_sin x).const_mul (9/100))).sub
      ((Real.hasDerivAt_cos x).const_mul (cosCoefficient i second))).sub
        ((N_deriv i x).const_mul R) using 1 <;> dsimp [F,Fd] <;> ring

theorem Fd_deriv (i second : Bool) (x : ℝ) : HasDerivAt (Fd i second) (Fdd i second x) x := by
  convert ((((Real.hasDerivAt_cos x).const_mul (-(9/100:ℝ))).const_add 1).add
    ((Real.hasDerivAt_sin x).const_mul (cosCoefficient i second))).sub
      ((Nd_deriv i x).const_mul R) using 1 <;> dsimp [Fd,Fdd] <;> ring

theorem quadrant_domain (i second : Bool) {x : ℝ}
    (hx : x∈Icc (left i second) (right second)) : x∈Icc (start i) (171/100) := by
  have hp := Arithmetic.pi_hand_enclosure
  have hb := parameter_bounds i
  cases second <;> dsimp [left,right] at hx <;> constructor <;> linarith

theorem Fdd_negative (i second : Bool) {x : ℝ}
    (hx : x∈Icc (left i second) (right second)) : Fdd i second x<0 := by
  have hdom := quadrant_domain i second hx
  have hcurv := Ndd_lower i hdom
  have hbase : 0<curvatureFloor i := by
    cases i <;> norm_num [curvatureFloor,normCap,determinantCap]
  have hR : (197/100:ℝ)≤R := by linarith [radius_precise.1]
  have hN : 0≤Ndd i x := hbase.le.trans hcurv
  have hm1 := mul_le_mul_of_nonneg_left hcurv R_pos.le
  have hm2 := mul_le_mul_of_nonneg_right hR hbase.le
  have htrig : (9/100)*Real.sin x+cosCoefficient i second*Real.cos x≤9/50 := by
    cases second with
    | false =>
        dsimp [cosCoefficient]
        linarith [Real.sin_le_one x,Real.cos_le_one x]
    | true =>
        have hs := second_signs (show x∈Icc (Real.pi/2) Real.pi from
          ⟨by simpa [left] using hx.1,by linarith [hdom.2,FrameLowPair.pi_lower]⟩)
        have hk : 0≤cosCoefficient i true := by cases i <;> norm_num [cosCoefficient,lam]
        have hm := mul_nonpos_of_nonneg_of_nonpos hk hs.2
        linarith [Real.sin_le_one x]
  have hnum : (9/50:ℝ)-(197/100)*curvatureFloor i<0 := by
    cases i <;> norm_num [curvatureFloor,normCap,determinantCap]
  dsimp [Fdd]
  nlinarith

theorem F_concave (i second : Bool) :
    ConcaveOn ℝ (Icc (left i second) (right second)) (F i second) :=
  concave_of_deriv2 (fun x _ => F_deriv i second x)
    (fun x _ => Fd_deriv i second x) (fun x hx => (Fdd_negative i second hx).le)

theorem final_cos : Real.cos (171/100:ℝ)<-(69/500:ℝ) := by
  have hh := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤171/100 by norm_num)
  norm_num [HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8] at hh
  linarith

theorem sum_trig_upper (x : ℝ) : Real.sin x+Real.cos x<71/50 := by
  nlinarith [Real.sin_sq_add_cos_sq x,sq_nonneg (Real.sin x-Real.cos x)]

theorem endpoint_lower (i second : Bool) :
    (1801/2000:ℝ)<F i second (left i second) ∧
      (1801/2000:ℝ)<F i second (right second) := by
  have hn := endpoint_norms i
  have hR : R<(99/50:ℝ) := by linarith [radius_precise.2]
  have hp := Arithmetic.pi_hand_enclosure
  have hnorm0 := mul_le_mul hR.le hn.1.le (N_positive i (start i)).le (by norm_num : (0:ℝ)≤99/50)
  have hnormm := mul_le_mul hR.le hn.2.1.le (N_positive i (Real.pi/2)).le (by norm_num : (0:ℝ)≤99/50)
  have hnorm1 := mul_le_mul hR.le hn.2.2.le (N_positive i (171/100)).le (by norm_num : (0:ℝ)≤99/50)
  have hs0 := sum_trig_upper (start i)
  have hs1 := Real.sin_le_one (171/100:ℝ)
  have hc1 := final_cos
  cases i <;> cases second <;>
    norm_num [F,left,right,start,K,sourceFloor,targetConstant,p,q,lam,cosCoefficient,
      initialNorm,middleNorm,finalNorm,cM,FrameMidArc.p,FrameMidArc.q,
      FrameLowArc.u,FrameLowArc.v] at *
  all_goals constructor <;> linarith

theorem lower (i second : Bool) {x : ℝ}
    (hx : x∈Icc (left i second) (right second)) : (1801/2000:ℝ)<F i second x :=
  concave_gt_of_endpoints (F_concave i second) hx (endpoint_lower i second).1
    (endpoint_lower i second).2

end SquaresInCircles.Eight.TableFree.FrameLowMidPrimaryScalars
