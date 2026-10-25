module

public import SquaresInCircles.Eight.Frames.Low.HighParallelCalculus
public import SquaresInCircles.Eight.Frames.Low.HighGeometry
public import SquaresInCircles.Eight.Owners.CircularNorm

/-!
# Eight squares: the secondary axis with a negative target in the low/middle pairs

A low source and a negative middle target separated along the secondary axis of the source, at
angles from `FrameLowMidEndpointScalars.start i` to `π/2`, have the cost of the pair above
`1801/2000` (`low_mid_negative_target`), and so do a positive middle source and a negative low
target at angles in `[11/100, 16/25]` (`mid_low_positive_negative`). The supports of the source
hold on its whole arc; the support of the target is concave along its arc, or monotone when its
primary coefficient is negative, so it is at least the smaller of its values at the two ends
(`low_target_endpoint`). Ties of the weak separator are included.
-/

section
/-!
## The remaining negative-target endpoint scalar supports

The full circle arcs reduce to their two intrinsic endpoints.  Each
resulting function is a linear term plus one sine and one cosine.
Its derivative is controlled by a single exact Euclidean coefficient
norm, on the whole physical interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidEndpointScalars
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus

def midA (j : Bool) : ℝ := if j then a2 else a1
def midB (j : Bool) : ℝ := if j then b2 else b1
def midLabel (j : Bool) : ℝ := if j then M2 else M1
def lam (i : Bool) : ℝ := if i then 189/200 else 1
def error (i : Bool) : ℝ := if i then 1/100000 else 0
def start (i : Bool) : ℝ := if i then 11/100 else 7/20
def P (i j : Bool) : ℝ := lam i*midA j-(lam i-9/50)/2
def Q (i j : Bool) : ℝ := (lam i-9/50)/2-lam i*midB j
def F (i j : Bool) (x : ℝ) : ℝ :=
  x+(lam i+9/50)/2+midLabel j-error i-P i j*Real.sin x+Q i j*Real.cos x
def Pu (i j : Bool) : ℝ :=
  if i then (if j then 751/1000 else 169/200) else (if j then 79/100 else 889/1000)
def Ql (i j : Bool) : ℝ := if j then -(13/125) else (if i then 3/40 else 17/200)
def Ml (j : Bool) : ℝ := if j then 911/2000 else 1523/5000

theorem coefficient_bounds (i j : Bool) :
    0≤P i j ∧ P i j≤Pu i j ∧ Pu i j≤89/100 ∧
      Ql i j≤Q i j ∧ -(21/200:ℝ)≤Q i j ∧ Q i j≤21/200 ∧
      Ml j≤ midLabel j := by
  cases i <;> cases j <;>
    dsimp [P,Q,Pu,Ql,Ml,lam,midA,midB,midLabel] <;>
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;>
    linarith [a1_precise.1,a1_precise.2,a2_bounds.1,a2_bounds.2,
      FrameLowMidArc.b1_precise.1,FrameLowMidArc.b1_precise.2,
      FrameLowMidArc.b2_precise.1,FrameLowMidArc.b2_precise.2,
      M_endpoints.1,M_endpoints.2.2.1]

theorem coefficient_norm (i j : Bool) : (P i j)^2+(Q i j)^2<1 := by
  have hb := coefficient_bounds i j
  have hp := pow_le_pow_left₀ hb.1 (hb.2.1.trans hb.2.2.1) 2
  have hq := mul_nonneg (sub_nonneg.mpr hb.2.2.2.2.2.1)
    (show 0≤Q i j+21/200 by linarith [hb.2.2.2.2.1])
  nlinarith

theorem F_deriv (i j : Bool) (x : ℝ) :
    HasDerivAt (F i j) (1-P i j*Real.cos x-Q i j*Real.sin x) x := by
  unfold F
  have h1 := (((hasDerivAt_id' x).add_const ((lam i+9/50)/2)).add_const (midLabel j)).sub_const
    (error i)
  convert (h1.fun_sub ((Real.hasDerivAt_sin x).const_mul (P i j))).fun_add
    ((Real.hasDerivAt_cos x).const_mul (Q i j)) using 1
  ring

theorem F_monotone (i j : Bool) : MonotoneOn (F i j) (Icc (start i) (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (F_deriv i j x).continuousAt.continuousWithinAt
  · exact fun x _ => F_deriv i j x
  · intro x hx
    have hh := harmonic_projection_lt_one (A := Q i j) (B := P i j) (x := x)
      (by nlinarith [coefficient_norm i j])
    linarith

theorem F_endpoint (i j : Bool) : (1801/2000:ℝ)<F i j (start i) := by
  have hb := coefficient_bounds i j
  have hx0 : 0≤ start i := by cases i <;> norm_num [start]
  have hxU : start i≤Real.pi/2 := by
    cases i <;> dsimp [start] <;> linarith [FrameLowPair.pi_lower]
  have ht := FrameLowPair.quadrant ⟨hx0,hxU⟩
  have hs := Real.sin_le hx0
  have hc := Real.one_sub_sq_div_two_le_cos (x := start i)
  have hPu : 0≤Pu i j := hb.1.trans hb.2.1
  have hP := mul_le_mul hb.2.1 hs ht.1 hPu
  have hQ := mul_le_mul_of_nonneg_right hb.2.2.2.1 ht.2.2.1
  have hqe : (if j then Ql i j else Ql i j*(1-(start i)^2/2))≤
      Q i j*Real.cos (start i) := by
    cases j with
    | false =>
        have hq0 : 0≤Ql i false := by cases i <;> norm_num [Ql]
        have hh := mul_le_mul_of_nonneg_left hc hq0
        simpa using hh.trans hQ
    | true =>
        have hqn : Ql i true≤0 := by norm_num [Ql]
        have hh := mul_le_mul_of_nonpos_left ht.2.2.2 hqn
        simpa only [ite_true,mul_one] using hh.trans hQ
  dsimp [F]
  cases i <;> cases j <;> norm_num [start,lam,error,Pu,Ql,Ml] at * <;> linarith

theorem F_lower (i j : Bool) {x : ℝ} (hx : x∈Icc (start i) (Real.pi/2)) :
    (1801/2000:ℝ)<F i j x :=
  (F_endpoint i j).trans_le (F_monotone i j ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1)

def lowA (j : Bool) : ℝ := if j then a1 else a0
def lowB (j : Bool) : ℝ := if j then b1 else 0
def lowLabel (j : Bool) : ℝ := if j then L1 else 0
def reverseP (j : Bool) : ℝ := (189/200)*lowA j-153/400
def reverseQ (j : Bool) : ℝ := 153/400-(189/200)*lowB j
def reverseF (j : Bool) (x : ℝ) : ℝ :=
  x+9/16+M2-(189/200)*b2+lowLabel j-
    reverseP j*Real.sin x+reverseQ j*Real.cos x

theorem reverse_coefficients (j : Bool) :
    0≤reverseP j ∧ reverseP j≤(if j then 169/200 else 191/200) ∧
      0≤reverseQ j ∧ reverseQ j≤383/1000 ∧
      (if j then 189/2500 else 153/400)≤reverseQ j ∧
      (if j then 15341/50000 else 0)≤lowLabel j := by
  cases j <;> dsimp [reverseP,reverseQ,lowA,lowB,lowLabel] <;>
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>
    linarith [a0_precise.1,a0_precise.2,a1_precise.1,a1_precise.2,
      FrameLowMidArc.b1_precise.1,FrameLowMidArc.b1_precise.2,L1_precise.1]

theorem reverse_norm (j : Bool) :
    (reverseP j)^2+(reverseQ j)^2<(1029/1000:ℝ)^2 := by
  have hb := reverse_coefficients j
  have hpU : reverseP j≤191/200 := by cases j <;> norm_num at hb <;> linarith [hb.2.1]
  have hp := pow_le_pow_left₀ hb.1 hpU 2
  have hq := pow_le_pow_left₀ hb.2.2.1 hb.2.2.2.1 2
  nlinarith

theorem reverse_deriv (j : Bool) (x : ℝ) :
    HasDerivAt (reverseF j) (1-reverseP j*Real.cos x-reverseQ j*Real.sin x) x := by
  unfold reverseF
  have h1 := ((((hasDerivAt_id' x).add_const (9/16)).add_const M2).sub_const
    ((189/200)*b2)).add_const (lowLabel j)
  convert (h1.fun_sub ((Real.hasDerivAt_sin x).const_mul (reverseP j))).fun_add
    ((Real.hasDerivAt_cos x).const_mul (reverseQ j)) using 1
  ring

theorem reverse_corrected_monotone (j : Bool) :
    MonotoneOn (fun x => reverseF j x+(29/1000)*x) (Icc (11/100:ℝ) (16/25)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro x hx
    exact ((reverse_deriv j x).fun_add
      ((hasDerivAt_id' x).const_mul (29/1000))).continuousAt.continuousWithinAt
  · intro x hx
    exact (reverse_deriv j x).fun_add ((hasDerivAt_id' x).const_mul (29/1000))
  · intro x hx
    have hh := FrameCoreArc.projection_lt (a := reverseQ j) (b := reverseP j)
      (show (0:ℝ)<1029/1000 by norm_num)
      (by linarith [reverse_norm j]) x
    linarith

theorem reverse_endpoint (j : Bool) : (917/1000:ℝ)<reverseF j (11/100:ℝ) := by
  have hb := reverse_coefficients j
  have ht := FrameLowPair.quadrant (show (11/100:ℝ)∈Icc 0 (Real.pi/2) from
    ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩)
  have hs := Real.sin_le (show (0:ℝ)≤11/100 by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (11/100:ℝ))
  have hsrc : -(303/10000:ℝ)≤M2-(189/200)*b2 := by
    linarith [M_endpoints.2.2.1,FrameLowMidArc.b2_precise.2]
  have hPu : 0≤(if j then (169/200:ℝ) else 191/200) := by cases j <;> norm_num
  have hP := mul_le_mul hb.2.1 hs ht.1 hPu
  have hQl : 0≤(if j then (189/2500:ℝ) else 153/400) := by cases j <;> norm_num
  have hQ1 := mul_le_mul_of_nonneg_left hc hQl
  have hQ2 := mul_le_mul_of_nonneg_right hb.2.2.2.2.1 ht.2.2.1
  have hQ := hQ1.trans hQ2
  dsimp [reverseF]
  cases j <;> norm_num at * <;> linarith

theorem reverse_lower (j : Bool) {x : ℝ} (hx : x∈Icc (11/100:ℝ) (16/25)) :
    (1801/2000:ℝ)<reverseF j x := by
  have hh := reverse_corrected_monotone j ⟨le_rfl,by norm_num⟩ hx hx.1
  have he := reverse_endpoint j
  linarith [hx.2]

end SquaresInCircles.Eight.FrameLowMidEndpointScalars
end
end
end

section
/-!
## Both complete low/middle primary circle supports

The Boolean parameter distinguishes the middle target from the low
target.  Each actual norm has positive radicand on the whole real line.
The exact circular-norm identity gives concavity on each physical
quadrant; only the three actual endpoints are evaluated.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidPrimaryScalars
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
      (13/10:ℝ)≤ start i ∧ start i≤3/2 ∧ 0<normCap i ∧
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
  convert hh using 1 <;> dsimp [N,CircularNorm.energy]
  ring
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
    have hlam := (parameter_bounds i).2.2.1
    dsimp [Nd,CircularNorm.d1,CircularNorm.slope]
    apply div_nonneg _ (by positivity)
    nlinarith

theorem endpoint_norms (i : Bool) :
    N i (start i)< initialNorm i ∧ N i (Real.pi/2)< middleNorm i ∧
      N i (171/100)<finalNorm i := by
  have hfirst := N_square i (start i)
  have hmiddle := N_square i (Real.pi/2)
  have hlast := N_square i (171/100)
  have h0 : 0 ≤ start i := by linarith [(parameter_bounds i).2.2.2.1]
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
  all_goals refine ⟨?_,?_,?_⟩ <;> refine lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_ <;>
    linarith only [hfirst,hmiddle,hlast,hs0,hc0,hs1,hc1]

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
  refine ((((hasDerivAt_id x).add_const (K i)).sub
    ((Real.hasDerivAt_sin x).const_mul (9/100))).sub
      ((Real.hasDerivAt_cos x).const_mul (cosCoefficient i second))).sub
        ((N_deriv i x).const_mul R) |>.congr_deriv ?_
  rw [Fd]
  ring

theorem Fd_deriv (i second : Bool) (x : ℝ) : HasDerivAt (Fd i second) (Fdd i second x) x := by
  refine ((((Real.hasDerivAt_cos x).const_mul (9/100:ℝ)).const_sub 1).add
    ((Real.hasDerivAt_sin x).const_mul (cosCoefficient i second))).sub
      ((Nd_deriv i x).const_mul R) |>.congr_deriv ?_
  rw [Fdd]
  ring

theorem quadrant_domain (i second : Bool) {x : ℝ}
    (hx : x∈Icc (left i second) (right second)) : x∈Icc (start i) (171/100) := by
  have hp := Arithmetic.pi_hand_enclosure
  obtain ⟨-,-,-,hb1,hb2,-⟩ := parameter_bounds i
  obtain ⟨hx1,hx2⟩ := hx
  cases second <;> dsimp [left,right] at hx1 hx2 <;> constructor <;> linarith

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
    (fun x _ => Fd_deriv i second x) (fun _ hx => (Fdd_negative i second hx).le)

theorem final_cos : Real.cos (171/100:ℝ)< -(69/500:ℝ) := by
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

end SquaresInCircles.Eight.FrameLowMidPrimaryScalars
end
end
end

section
/-!
## The primary axis of the source in the low/middle pairs

A low source and a middle target, or a middle source and a low target, separated along the
primary axis of the source at a frame angle `x ≥ 0`, have the cost of the pair above `1801/2000`
for all signs (`low_mid_primary`, `mid_low_primary`). A positive target is bounded by the support
of its circle, in the first and in the second quadrant (`low_mid_circle_support`,
`mid_low_circle_support`); a negative low target by the smaller of its values at the two ends of
the low arc (`negative_endpoint_support`), concave in the angle and above `1` on `[11/10, 7/5]`
(`endpoint_concave`, `endpoint_lower`). The sign of the source enters through a monotone loss of
its marker, and the margins are weak.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidPrimary
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus
open FrameLowMidGeometry FrameLowMidCuts

theorem norm_identity (i : Bool) (x : ℝ) :
    Real.sqrt ((FrameLowMidPrimaryScalars.lam i*Real.cos x-FrameLowMidPrimaryScalars.p i)^2+
      (FrameLowMidPrimaryScalars.lam i*Real.sin x-FrameLowMidPrimaryScalars.q i)^2)=
        FrameLowMidPrimaryScalars.N i x := by
  dsimp [FrameLowMidPrimaryScalars.N,CircularNorm.norm,CircularNorm.energy]
  congr 1
  linear_combination (FrameLowMidPrimaryScalars.lam i)^2*(Real.sin_sq_add_cos_sq x)

theorem low_mid_circle_support (second : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (FrameLowMidPrimaryScalars.left true second)
      (FrameLowMidPrimaryScalars.right second))
    (hm : 0≤primary true b B x) :
    FrameLowMidPrimaryScalars.F true second x≤lowMidCost false true b B x := by
  have hs := low_primary_source hb (show (9/10:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hsource : FrameLowMidPrimaryScalars.sourceFloor true≤-L b-(9/10)*A b := by
    dsimp [FrameLowMidPrimaryScalars.sourceFloor]
    linarith [L1_precise.2,a1_precise.2]
  have hscaled := mul_nonneg (show (0:ℝ)≤9/10 by norm_num) hm
  have ht := circle_linear_lower
    (A_circle ⟨b1_mem.1.trans hB.1,hB.2.trans b2_mem.2⟩)
    ((9/10)*Real.cos x-FrameMidArc.p) ((9/10)*Real.sin x-FrameMidArc.q)
  have hn := norm_identity true x
  norm_num [FrameLowMidPrimaryScalars.lam,FrameLowMidPrimaryScalars.p,
    FrameLowMidPrimaryScalars.q] at hn
  rw [hn] at ht
  have hdom := FrameLowMidPrimaryScalars.quadrant_domain true second hx
  cases second with
  | false =>
      have hq : x∈Icc 0 (Real.pi/2) :=
        ⟨by norm_num [FrameLowMidPrimaryScalars.start] at hdom; linarith [hdom.1],
          by simpa [FrameLowMidPrimaryScalars.right] using hx.2⟩
      dsimp [primary] at hscaled
      rw [(first_width hq).1] at hscaled
      dsimp [lowMidCost,FrameLowMidPrimaryScalars.F,FrameLowMidPrimaryScalars.K,
        FrameLowMidPrimaryScalars.cosCoefficient,FrameLowMidPrimaryScalars.targetConstant,
        FrameLowMidPrimaryScalars.p,FrameLowMidPrimaryScalars.q,FrameLowMidPrimaryScalars.lam,M]
      rw [(first_width hq).2]
      norm_num [sign] at hscaled ⊢
      nlinarith
  | true =>
      have hq : x∈Icc (Real.pi/2) Real.pi :=
        ⟨by simpa [FrameLowMidPrimaryScalars.left] using hx.1,
          by linarith [hdom.2,FrameLowPair.pi_lower]⟩
      dsimp [primary] at hscaled
      rw [(second_width hq).1] at hscaled
      dsimp [lowMidCost,FrameLowMidPrimaryScalars.F,FrameLowMidPrimaryScalars.K,
        FrameLowMidPrimaryScalars.cosCoefficient,FrameLowMidPrimaryScalars.targetConstant,
        FrameLowMidPrimaryScalars.p,FrameLowMidPrimaryScalars.q,FrameLowMidPrimaryScalars.lam,M]
      rw [(second_width hq).2]
      norm_num [sign] at hscaled ⊢
      nlinarith

theorem mid_low_circle_support (second : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (FrameLowMidPrimaryScalars.left false second)
      (FrameLowMidPrimaryScalars.right second))
    (hm : 0≤primary true b B x) :
    FrameLowMidPrimaryScalars.F false second x≤ midLowCost false true b B x := by
  have hs := middle_primary_source hb (show (47/50:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hsource : FrameLowMidPrimaryScalars.sourceFloor false≤-M b-(47/50)*A b := by
    dsimp [FrameLowMidPrimaryScalars.sourceFloor]
    linarith [M_endpoints.2.2.2,a2_bounds.2]
  have hscaled := mul_nonneg (show (0:ℝ)≤47/50 by norm_num) hm
  have ht := circle_linear_lower (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    ((47/50)*Real.cos x-FrameLowArc.u) ((47/50)*Real.sin x-FrameLowArc.v)
  have hn := norm_identity false x
  norm_num [FrameLowMidPrimaryScalars.lam,FrameLowMidPrimaryScalars.p,
    FrameLowMidPrimaryScalars.q] at hn
  rw [hn] at ht
  have hbase := mul_le_mul_of_nonneg_left a0_precise.1.le
    (show 0≤FrameLowArc.u by norm_num [FrameLowArc.u])
  have hdom := FrameLowMidPrimaryScalars.quadrant_domain false second hx
  cases second with
  | false =>
      have hq : x∈Icc 0 (Real.pi/2) :=
        ⟨by norm_num [FrameLowMidPrimaryScalars.start] at hdom; linarith [hdom.1],
          by simpa [FrameLowMidPrimaryScalars.right] using hx.2⟩
      dsimp [primary] at hscaled
      rw [(first_width hq).1] at hscaled
      dsimp [midLowCost,FrameLowMidPrimaryScalars.F,FrameLowMidPrimaryScalars.K,
        FrameLowMidPrimaryScalars.cosCoefficient,FrameLowMidPrimaryScalars.targetConstant,
        FrameLowMidPrimaryScalars.p,FrameLowMidPrimaryScalars.q,FrameLowMidPrimaryScalars.lam,L]
      rw [(first_width hq).2]
      norm_num [sign] at hscaled ⊢
      nlinarith
  | true =>
      have hq : x∈Icc (Real.pi/2) Real.pi :=
        ⟨by simpa [FrameLowMidPrimaryScalars.left] using hx.1,
          by linarith [hdom.2,FrameLowPair.pi_lower]⟩
      dsimp [primary] at hscaled
      rw [(second_width hq).1] at hscaled
      dsimp [midLowCost,FrameLowMidPrimaryScalars.F,FrameLowMidPrimaryScalars.K,
        FrameLowMidPrimaryScalars.cosCoefficient,FrameLowMidPrimaryScalars.targetConstant,
        FrameLowMidPrimaryScalars.p,FrameLowMidPrimaryScalars.q,FrameLowMidPrimaryScalars.lam,L]
      rw [(second_width hq).2]
      norm_num [sign] at hscaled ⊢
      nlinarith

def endpointA (i : Bool) : ℝ := if i then a1 else a0
def endpointB (i : Bool) : ℝ := if i then b1 else 0
def endpointL (i : Bool) : ℝ := if i then L1 else 0
def endpointF (i : Bool) (x : ℝ) : ℝ :=
  x+59/100-M2-a2+endpointL i+(41/100-endpointB i)*Real.sin x+
    (41/100+endpointA i)*Real.cos x
def endpointD (i : Bool) (x : ℝ) : ℝ :=
  1+(41/100-endpointB i)*Real.cos x-(41/100+endpointA i)*Real.sin x
def endpointDD (i : Bool) (x : ℝ) : ℝ :=
  -(41/100-endpointB i)*Real.sin x-(41/100+endpointA i)*Real.cos x

theorem endpoint_deriv (i : Bool) (x : ℝ) : HasDerivAt (endpointF i) (endpointD i x) x := by
  refine ((((((((hasDerivAt_id x).add_const (59/100)).sub_const M2).sub_const a2).add_const
    (endpointL i)).add ((Real.hasDerivAt_sin x).const_mul (41/100-endpointB i))).add
      ((Real.hasDerivAt_cos x).const_mul (41/100+endpointA i)))).congr_deriv ?_
  rw [endpointD]
  ring

theorem endpointD_deriv (i : Bool) (x : ℝ) : HasDerivAt (endpointD i) (endpointDD i x) x := by
  convert ((((Real.hasDerivAt_cos x).const_mul (41/100-endpointB i)).const_add 1).sub
    ((Real.hasDerivAt_sin x).const_mul (41/100+endpointA i))) using 1
  · rfl
  · dsimp [endpointDD]; ring

theorem endpoint_coefficients (i : Bool) :
    0≤41/100-endpointB i ∧ 0≤41/100+endpointA i := by
  cases i <;> dsimp [endpointA,endpointB]
  all_goals constructor <;> linarith [FrameLowMidArc.b1_precise.2,a0_precise.1,a1_precise.1]

theorem endpoint_concave (i : Bool) :
    ConcaveOn ℝ (Icc (11/10:ℝ) (7/5)) (endpointF i) := by
  apply concave_of_deriv2 (fun x _ => endpoint_deriv i x) (fun x _ => endpointD_deriv i x)
  intro x hx
  have ht := FrameLowPair.quadrant (show x∈Icc 0 (Real.pi/2) from
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  have hp := endpoint_coefficients i
  have h1 := mul_nonneg hp.1 ht.1
  have h2 := mul_nonneg hp.2 ht.2.2.1
  dsimp [endpointDD]
  linarith

theorem endpoint_values (i : Bool) :
    (1:ℝ)<endpointF i (11/10:ℝ) ∧ 1<endpointF i (7/5:ℝ) := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤11/10 by norm_num)
  have hcL := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤11/10 by norm_num)
  have hsU := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤7/5 by norm_num)
  have hcU := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤7/5 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hsL hcL hsU hcU
  have hs0 : (89/100:ℝ)≤Real.sin (11/10:ℝ) := by linarith
  have hc0 : (9/20:ℝ)≤Real.cos (11/10:ℝ) := by linarith
  have hs1 : (49/50:ℝ)≤Real.sin (7/5:ℝ) := by linarith
  have hc1 : (169/1000:ℝ)≤Real.cos (7/5:ℝ) := by linarith
  have hp := endpoint_coefficients i
  have h1 := mul_le_mul_of_nonneg_left hs0 hp.1
  have h2 := mul_le_mul_of_nonneg_left hc0 hp.2
  have h3 := mul_le_mul_of_nonneg_left hs1 hp.1
  have h4 := mul_le_mul_of_nonneg_left hc1 hp.2
  cases i <;> dsimp [endpointF,endpointA,endpointB,endpointL] at *
  all_goals constructor <;>
    linarith [M_endpoints.2.2.2,a2_bounds.2,a0_precise.1,a1_precise.1,
      FrameLowMidArc.b1_precise.2,L1_precise.1]

theorem endpoint_lower (i : Bool) {x : ℝ} (hx : x∈Icc (11/10:ℝ) (7/5)) :
    (1:ℝ)<endpointF i x :=
  concave_gt_of_endpoints (endpoint_concave i) hx (endpoint_values i).1 (endpoint_values i).2

theorem negative_endpoint_support {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (11/10:ℝ) (7/5)) (hm : 0≤primary false b B x) :
    min (endpointF false x) (endpointF true x)≤ midLowCost false false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hs := middle_primary_source hb (show (1:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
  have htarget := linear_endpoint_lower (p := FrameLowArc.u+Real.cos x)
    (q := FrameLowArc.v-Real.sin x)
    (by dsimp [FrameLowArc.u]; linarith [ht.2.2.1]) (by norm_num) b1_mem.2 hB
  simp only [linear,A_zero,A_b1,mul_zero,add_zero] at htarget
  dsimp [primary] at hm
  rw [(first_width hxq).1] at hm
  norm_num [sign] at hm
  rcases le_total ((FrameLowArc.u+Real.cos x)*a0)
    ((FrameLowArc.u+Real.cos x)*a1+(FrameLowArc.v-Real.sin x)*b1) with he | he
  · rw [min_eq_left he] at htarget
    apply (min_le_left _ _).trans
    dsimp [endpointF,endpointA,endpointB,endpointL,midLowCost,L]
    rw [(first_width hxq).2]
    norm_num [sign]
    nlinarith
  · rw [min_eq_right he] at htarget
    apply (min_le_right _ _).trans
    dsimp [endpointF,endpointA,endpointB,endpointL,midLowCost,L,L1]
    rw [(first_width hxq).2]
    norm_num [sign]
    nlinarith

theorem low_mid_primary (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2) (hx : 0≤x)
    (hm : 0≤primary k b B x) : (1801/2000:ℝ)<lowMidCost i k b B x := by
  apply lt_of_lt_of_le _ (low_mid_weaken_source i k hb)
  cases k with
  | false =>
      have hcut := low_mid_negative_cut hb hB hx hm
      exact low_mid_tail false false hb hB (by simpa [lowMidTail] using hcut.le)
  | true =>
      have hcut := low_mid_positive_cut hb hB hx hm
      by_cases htail : (171/100:ℝ)≤x
      · exact low_mid_tail false true hb hB (by simpa [lowMidTail] using htail)
      · by_cases hquad : x≤Real.pi/2
        · have hdom : x∈Icc (FrameLowMidPrimaryScalars.left true false)
              (FrameLowMidPrimaryScalars.right false) := by
            simpa [FrameLowMidPrimaryScalars.left,FrameLowMidPrimaryScalars.right,
              FrameLowMidPrimaryScalars.start] using And.intro hcut.le hquad
          exact (FrameLowMidPrimaryScalars.lower true false hdom).trans_le
            (low_mid_circle_support false hb hB hdom hm)
        · have hdom : x∈Icc (FrameLowMidPrimaryScalars.left true true)
              (FrameLowMidPrimaryScalars.right true) := by
            simp only [FrameLowMidPrimaryScalars.left,FrameLowMidPrimaryScalars.right,ite_true]
            exact ⟨(lt_of_not_ge hquad).le,(lt_of_not_ge htail).le⟩
          exact (FrameLowMidPrimaryScalars.lower true true hdom).trans_le
            (low_mid_circle_support true hb hB hdom hm)

theorem mid_low_primary (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (hx : 0≤x)
    (hm : 0≤primary k b B x) : (1801/2000:ℝ)< midLowCost i k b B x := by
  apply lt_of_lt_of_le _ (mid_low_weaken_source i k hb)
  cases k with
  | false =>
      have hcut := mid_low_negative_cut hb hB hx hm
      by_cases htail : (7/5:ℝ)≤x
      · exact mid_low_tail false false hb hB (by simpa [midLowTail] using htail)
      · have hdom : x∈Icc (11/10:ℝ) (7/5) := ⟨hcut.le,(lt_of_not_ge htail).le⟩
        have hh := (lt_min (endpoint_lower false hdom) (endpoint_lower true hdom)).trans_le
          (negative_endpoint_support hb hB hdom hm)
        linarith
  | true =>
      have hcut := mid_low_positive_cut hb hB hx hm
      by_cases htail : (171/100:ℝ)≤x
      · exact mid_low_tail false true hb hB (by simpa [midLowTail] using htail)
      · by_cases hquad : x≤Real.pi/2
        · have hdom : x∈Icc (FrameLowMidPrimaryScalars.left false false)
              (FrameLowMidPrimaryScalars.right false) := by
            simpa [FrameLowMidPrimaryScalars.left,FrameLowMidPrimaryScalars.right,
              FrameLowMidPrimaryScalars.start] using And.intro hcut.le hquad
          exact (FrameLowMidPrimaryScalars.lower false false hdom).trans_le
            (mid_low_circle_support false hb hB hdom hm)
        · have hdom : x∈Icc (FrameLowMidPrimaryScalars.left false true)
              (FrameLowMidPrimaryScalars.right true) := by
            simp only [FrameLowMidPrimaryScalars.left,FrameLowMidPrimaryScalars.right,ite_true]
            exact ⟨(lt_of_not_ge hquad).le,(lt_of_not_ge htail).le⟩
          exact (FrameLowMidPrimaryScalars.lower false true hdom).trans_le
            (mid_low_circle_support true hb hB hdom hm)

end SquaresInCircles.Eight.FrameLowMidPrimary
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidSecondaryEndpoints
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus
open FrameLowMidGeometry

theorem low_mid_negative_target (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (FrameLowMidEndpointScalars.start i) (Real.pi/2))
    (hm : 0≤ secondary i false b B x) : (1801/2000:ℝ)<lowMidCost i false b B x := by
  let lam := FrameLowMidEndpointScalars.lam i
  have hlam : 0≤lam := by cases i <;> norm_num [lam,FrameLowMidEndpointScalars.lam]
  have hx0 : 0≤x := by
    have hh : 0≤FrameLowMidEndpointScalars.start i := by
      cases i <;> norm_num [FrameLowMidEndpointScalars.start]
    exact hh.trans hx.1
  have hxq : x∈Icc 0 (Real.pi/2) := ⟨hx0,hx.2⟩
  have ht := FrameLowPair.quadrant hxq
  have hs : -FrameLowMidEndpointScalars.error i≤ sign i*(L b-lam*b) := by
    cases i with
    | false => simpa [lam,FrameLowMidEndpointScalars.lam,FrameLowMidEndpointScalars.error,sign]
        using low_unit_source hb
    | true => simpa [lam,FrameLowMidEndpointScalars.lam,FrameLowMidEndpointScalars.error,sign]
        using low_positive_source hb
  have hscaled := mul_nonneg hlam hm
  have hp : 0≤FrameMidArc.p-lam*Real.sin x := by
    cases i <;> dsimp [lam,FrameLowMidEndpointScalars.lam,FrameMidArc.p] <;> linarith [ht.2.1]
  have htarget := linear_endpoint_lower (p := FrameMidArc.p-lam*Real.sin x)
    (q := FrameMidArc.q-lam*Real.cos x) hp b1_mem.1 b2_mem.2 hB
  simp only [linear,A_b1,A_b2] at htarget
  dsimp [secondary] at hscaled
  rw [(first_width hxq).1] at hscaled
  have hmin : min (FrameLowMidEndpointScalars.F i false x)
      (FrameLowMidEndpointScalars.F i true x)≤lowMidCost i false b B x := by
    rcases le_total ((FrameMidArc.p-lam*Real.sin x)*a1+(FrameMidArc.q-lam*Real.cos x)*b1)
      ((FrameMidArc.p-lam*Real.sin x)*a2+(FrameMidArc.q-lam*Real.cos x)*b2) with he | he
    · rw [min_eq_left he] at htarget
      apply (min_le_left _ _).trans
      dsimp [FrameLowMidEndpointScalars.F,FrameLowMidEndpointScalars.P,
        FrameLowMidEndpointScalars.Q,FrameLowMidEndpointScalars.midA,
        FrameLowMidEndpointScalars.midB,FrameLowMidEndpointScalars.midLabel,
        lowMidCost,M,M1]
      rw [(first_width hxq).2]
      change -FrameLowMidEndpointScalars.error i≤ sign i*(L b-FrameLowMidEndpointScalars.lam i*b) at hs
      dsimp [lam,sign] at hs hscaled htarget ⊢
      nlinarith
    · rw [min_eq_right he] at htarget
      apply (min_le_right _ _).trans
      dsimp [FrameLowMidEndpointScalars.F,FrameLowMidEndpointScalars.P,
        FrameLowMidEndpointScalars.Q,FrameLowMidEndpointScalars.midA,
        FrameLowMidEndpointScalars.midB,FrameLowMidEndpointScalars.midLabel,
        lowMidCost,M,M2]
      rw [(first_width hxq).2]
      change -FrameLowMidEndpointScalars.error i≤ sign i*(L b-FrameLowMidEndpointScalars.lam i*b) at hs
      dsimp [lam,sign] at hs hscaled htarget ⊢
      nlinarith
  exact (lt_min (FrameLowMidEndpointScalars.F_lower i false hx)
    (FrameLowMidEndpointScalars.F_lower i true hx)).trans_le hmin

theorem low_target_endpoint {B x : ℝ} (hB : B∈Icc 0 b1)
    (_hx : x∈Icc 0 (Real.pi/2)) :
    min (linear (FrameLowArc.u-(189/200)*Real.sin x)
      (FrameLowArc.v-(189/200)*Real.cos x) 0)
      (linear (FrameLowArc.u-(189/200)*Real.sin x)
        (FrameLowArc.v-(189/200)*Real.cos x) b1)≤
      linear (FrameLowArc.u-(189/200)*Real.sin x)
        (FrameLowArc.v-(189/200)*Real.cos x) B := by
  by_cases hp : 0≤FrameLowArc.u-(189/200)*Real.sin x
  · exact linear_endpoint_lower hp (by norm_num) b1_mem.2 hB
  · have hq : 0≤FrameLowArc.v-(189/200)*Real.cos x := by
      dsimp [FrameLowArc.v]
      linarith [Real.cos_le_one x]
    exact (min_le_left _ _).trans
      (linear_monotone (le_of_not_ge hp) hq
        ⟨le_rfl,by linarith [c0_bounds.1]⟩ ⟨hB.1,hB.2.trans b1_mem.2⟩ hB.1)

theorem mid_low_positive_negative {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (11/100:ℝ) (16/25)) (hm : 0≤ secondary true false b B x) :
    (1801/2000:ℝ)< midLowCost true false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := middle_positive_source hb (show (4/5:ℝ)≤189/200 by norm_num)
  have hscaled := mul_nonneg (show (0:ℝ)≤189/200 by norm_num) hm
  have ht := low_target_endpoint hB hxq
  simp only [linear,A_zero,A_b1,mul_zero,add_zero] at ht
  dsimp [secondary] at hscaled
  rw [(first_width hxq).1] at hscaled
  norm_num [sign] at hscaled
  have hmin : min (FrameLowMidEndpointScalars.reverseF false x)
      (FrameLowMidEndpointScalars.reverseF true x)≤ midLowCost true false b B x := by
    rcases le_total ((FrameLowArc.u-(189/200)*Real.sin x)*a0)
      ((FrameLowArc.u-(189/200)*Real.sin x)*a1+
        (FrameLowArc.v-(189/200)*Real.cos x)*b1) with he | he
    · rw [min_eq_left he] at ht
      apply (min_le_left _ _).trans
      dsimp [FrameLowMidEndpointScalars.reverseF,FrameLowMidEndpointScalars.reverseP,
        FrameLowMidEndpointScalars.reverseQ,FrameLowMidEndpointScalars.lowA,
        FrameLowMidEndpointScalars.lowB,FrameLowMidEndpointScalars.lowLabel,midLowCost,L]
      rw [(first_width hxq).2]
      norm_num [sign]
      nlinarith
    · rw [min_eq_right he] at ht
      apply (min_le_right _ _).trans
      dsimp [FrameLowMidEndpointScalars.reverseF,FrameLowMidEndpointScalars.reverseP,
        FrameLowMidEndpointScalars.reverseQ,FrameLowMidEndpointScalars.lowA,
        FrameLowMidEndpointScalars.lowB,FrameLowMidEndpointScalars.lowLabel,midLowCost,L,L1]
      rw [(first_width hxq).2]
      norm_num [sign]
      nlinarith
  exact (lt_min (FrameLowMidEndpointScalars.reverse_lower false hx)
    (FrameLowMidEndpointScalars.reverse_lower true hx)).trans_le hmin

end SquaresInCircles.Eight.FrameLowMidSecondaryEndpoints
end
end
end
