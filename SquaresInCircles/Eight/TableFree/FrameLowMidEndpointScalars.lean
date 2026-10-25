module

public import SquaresInCircles.Eight.TableFree.FrameLowMidGeometry

/-!
# The remaining negative-target endpoint scalar supports

The full circle arcs reduce to their two intrinsic endpoints.  Each
resulting function is a linear term plus one sine and one cosine.
Its derivative is controlled by a single exact Euclidean coefficient
norm, on the whole physical interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowMidEndpointScalars
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

end SquaresInCircles.Eight.TableFree.FrameLowMidEndpointScalars
