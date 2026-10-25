module

public import SquaresInCircles.Eight.TableFree.FrameCoreLowEndpoint

/-!
# The whole core/low primary cancellation interval

The multiplier `g / sin x` cancels the signed core tangent.  Its actual
low endpoint is retained.  Before the quarter turn a single trigonometric
function has decreasing second derivative; one tangent parabola and an
endpoint principle prove positivity on the whole interval.  After the
quarter turn the same support has positive derivative.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreLowCancellation
open FramePair FrameCircleArc FrameLowArc FrameCoreArc FramePairCalculus
open FrameMidArc (g)
open FrameCoreMidScalars (ac)

def aa : ℝ := 13/12
def bb : ℝ := 1997/2500
def kk : ℝ := -(294157/500000)
def T (x : ℝ) : ℝ :=
  (x+kk)*Real.sin x-(9/100)*(Real.sin x)^2-
    (9/100)*Real.sin x*Real.cos x+g*aa*Real.cos x-g*bb
def T1 (x : ℝ) : ℝ :=
  (1-g*aa)*Real.sin x+(x+kk)*Real.cos x-
    (9/50)*Real.sin x*Real.cos x-(9/100)*Real.cos (2*x)
def T2 (x : ℝ) : ℝ :=
  (2-g*aa)*Real.cos x-(x+kk)*Real.sin x-
    (9/50)*Real.cos (2*x)+(9/50)*Real.sin (2*x)
def T3 (x : ℝ) : ℝ :=
  -(3-g*aa)*Real.sin x-(x+kk)*Real.cos x+
    (9/25)*(Real.sin (2*x)+Real.cos (2*x))

theorem T_deriv (x : ℝ) : HasDerivAt T (T1 x) x := by
  have h1 := ((hasDerivAt_id' x).add_const kk).fun_mul (Real.hasDerivAt_sin x)
  have h2 := ((Real.hasDerivAt_sin x).fun_pow 2).const_mul (9/100)
  have h3 := ((Real.hasDerivAt_sin x).fun_mul (Real.hasDerivAt_cos x)).const_mul (9/100)
  have h4 := (Real.hasDerivAt_cos x).const_mul (g*aa)
  have h := (((h1.fun_sub h2).fun_sub h3).fun_add h4).sub_const (g*bb)
  convert h using 1
  · funext y; simp only [T]; ring
  · simp only [T1,Real.cos_two_mul',Nat.cast_ofNat,Nat.add_one_sub_one,pow_one]
    ring

theorem T1_deriv (x : ℝ) : HasDerivAt T1 (T2 x) x := by
  have h1 := (Real.hasDerivAt_sin x).const_mul (1-g*aa)
  have h2 := ((hasDerivAt_id' x).add_const kk).fun_mul (Real.hasDerivAt_cos x)
  have h3 := ((Real.hasDerivAt_sin x).fun_mul (Real.hasDerivAt_cos x)).const_mul (9/50)
  have h4 := (((hasDerivAt_id' x).const_mul 2).cos).const_mul (9/100)
  have h := ((h1.fun_add h2).fun_sub h3).fun_sub h4
  convert h using 1
  · funext y; simp only [T1]; ring
  · simp only [T2,Real.cos_two_mul']
    ring

theorem T2_deriv (x : ℝ) : HasDerivAt T2 (T3 x) x := by
  have h1 := (Real.hasDerivAt_cos x).const_mul (2-g*aa)
  have h2 := ((hasDerivAt_id' x).add_const kk).fun_mul (Real.hasDerivAt_sin x)
  have h3 := (((hasDerivAt_id' x).const_mul 2).cos).const_mul (9/50)
  have h4 := (((hasDerivAt_id' x).const_mul 2).sin).const_mul (9/50)
  have h := ((h1.fun_sub h2).fun_sub h3).fun_add h4
  convert h using 1
  · rfl
  · simp only [T3]; ring

theorem endpoint_trig :
    (141/250:ℝ)<Real.sin (3/5:ℝ) ∧
      (887/1000:ℝ)<Real.sin (41/20:ℝ) ∧
        -(231/500:ℝ)<Real.cos (41/20:ℝ) := by
  have h0 := sin_lower_seven (show (0:ℝ)≤3/5 by norm_num)
  have h1 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤41/20 by norm_num)
  have h2 := Arithmetic.cos10_le_cos (show (0:ℝ)≤41/20 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,
    Arithmetic.cos8] at *
  refine ⟨?_,?_,?_⟩ <;> linarith

theorem interval_sine {x : ℝ} (hx : x∈Icc (3/5:ℝ) (41/20)) :
    (141/250:ℝ)<Real.sin x := by
  exact sin_endpoint_lower (by norm_num)
    (by linarith [FrameLowPair.pi_lower] : (41/20:ℝ)≤Real.pi) hx
    endpoint_trig.1 (by linarith [endpoint_trig.2.1])

theorem T3_negative {x : ℝ} (hx : x∈Icc (3/5:ℝ) (Real.pi/2)) :
    T3 x< -(1/2:ℝ) := by
  have hq := FrameLowPair.quadrant ⟨by linarith [hx.1],hx.2⟩
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(3/5:ℝ)) hx.2 hx.1
  have hsum : Real.sin (2*x)+Real.cos (2*x)≤(17/12:ℝ) := by
    nlinarith [Real.sin_sq_add_cos_sq (2*x),
      sq_nonneg (Real.sin (2*x)-Real.cos (2*x))]
  have hprod := mul_nonneg (show 0≤x+kk by dsimp [kk]; linarith [hx.1]) hq.2.2.1
  dsimp [T3,aa,g]
  linarith [endpoint_trig.1]

theorem T2_antitone : AntitoneOn T2 (Icc (3/5:ℝ) (Real.pi/2)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (T2_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => T2_deriv x
  · exact fun x hx => (T3_negative (Ioo_subset_Icc_self hx)).le.trans (by norm_num)

theorem T1_concave : ConcaveOn ℝ (Icc (3/5:ℝ) (Real.pi/2)) T1 :=
  concave_of_deriv2 (fun x _ => T1_deriv x) (fun x _ => T2_deriv x)
    (fun x hx => (T3_negative hx).le.trans (by norm_num))

theorem contact_trig :
    (391663/500000:ℝ)<Real.sin (9/10:ℝ) ∧
      Real.sin (9/10:ℝ)<97916/125000 ∧
        (621609/1000000:ℝ)<Real.cos (9/10:ℝ) ∧
          Real.cos (9/10:ℝ)<621611/1000000 := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤9/10 by norm_num)
  have hsU := Arithmetic.sin_le_sin9 (show (0:ℝ)≤9/10 by norm_num)
  have hcL := Arithmetic.cos10_le_cos (show (0:ℝ)≤9/10 by norm_num)
  have hcU := Arithmetic.cos_le_cos8 (show (0:ℝ)≤9/10 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem contact : (99/10000:ℝ)<T (9/10) ∧ |T1 (9/10)|<(1/200:ℝ) := by
  have ht := contact_trig
  have hs : 0≤Real.sin (9/10:ℝ) := by linarith [ht.1]
  have hc : 0≤Real.cos (9/10:ℝ) := by linarith [ht.2.2.1]
  have hs2L := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤391663/500000) ht.1.le 2
  have hs2U := pow_le_pow_left₀ hs ht.2.1.le 2
  have hc2L := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤621609/1000000) ht.2.2.1.le 2
  have hc2U := pow_le_pow_left₀ hc ht.2.2.2.le 2
  have hscL := mul_le_mul ht.1.le ht.2.2.1.le (by norm_num) hs
  have hscU := mul_le_mul ht.2.1.le ht.2.2.2.le hc (by norm_num)
  dsimp [T,T1,aa,bb,kk,g]
  rw [Real.cos_two_mul]
  refine ⟨by nlinarith,abs_lt.mpr ⟨by nlinarith,by nlinarith⟩⟩

theorem shoulder_trig :
    (557/625:ℝ)<Real.sin (11/10:ℝ) ∧ Real.sin (11/10:ℝ)<44561/50000 ∧
      (45359/100000:ℝ)<Real.cos (11/10:ℝ) ∧ Real.cos (11/10:ℝ)<45361/100000 := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤11/10 by norm_num)
  have hsU := Arithmetic.sin_le_sin9 (show (0:ℝ)≤11/10 by norm_num)
  have hcL := Arithmetic.cos10_le_cos (show (0:ℝ)≤11/10 by norm_num)
  have hcU := Arithmetic.cos_le_cos8 (show (0:ℝ)≤11/10 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem shoulder : (2/125:ℝ)<T (11/10) ∧ (3/50:ℝ)<T1 (11/10) ∧
    (1/6:ℝ)<T2 (11/10) := by
  have ht := shoulder_trig
  have hs : 0≤Real.sin (11/10:ℝ) := by linarith [ht.1]
  have hc : 0≤Real.cos (11/10:ℝ) := by linarith [ht.2.2.1]
  have hs2L := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤557/625) ht.1.le 2
  have hs2U := pow_le_pow_left₀ hs ht.2.1.le 2
  have hc2L := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤45359/100000) ht.2.2.1.le 2
  have hc2U := pow_le_pow_left₀ hc ht.2.2.2.le 2
  have hscL := mul_le_mul ht.1.le ht.2.2.1.le (by norm_num) hs
  have hscU := mul_le_mul ht.2.1.le ht.2.2.2.le hc (by norm_num)
  dsimp [T,T1,T2,aa,bb,kk,g]
  rw [Real.cos_two_mul,Real.sin_two_mul]
  refine ⟨?_,?_,?_⟩ <;> linarith [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]

theorem T_initial_positive {x : ℝ} (hx : x∈Icc (3/5:ℝ) (11/10)) : 0<T x := by
  have hcurv {z : ℝ} (hz : z∈Icc (3/5:ℝ) (11/10)) : (1/6:ℝ)≤T2 z := by
    have hh := T2_antitone ⟨hz.1,by linarith [hz.2,FrameLowPair.pi_lower]⟩
      ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩ hz.2
    exact shoulder.2.2.le.trans hh
  apply positive_of_curvature (κ := (1/6:ℝ)) (by norm_num) hx
    (show (9/10:ℝ)∈Icc (3/5:ℝ) (11/10) by constructor <;> norm_num)
    (fun z _ => T_deriv z) (fun z _ => T1_deriv z) (fun z hz => hcurv hz)
  obtain ⟨hl,hu⟩ := abs_lt.mp contact.2
  nlinarith [contact.1]

theorem T_positive {x : ℝ} (hx : x∈Icc (3/5:ℝ) (Real.pi/2)) : 0<T x := by
  by_cases hsmall : x≤11/10
  · exact T_initial_positive ⟨hx.1,hsmall⟩
  · have hc := T1_concave.subset
      (show Icc (11/10:ℝ) (Real.pi/2)⊆Icc (3/5:ℝ) (Real.pi/2) by
        exact Icc_subset_Icc (by norm_num) le_rfl) (convex_Icc _ _)
    have hh := endpoint_minimum_of_concave_derivative
      (show x∈Icc (11/10:ℝ) (Real.pi/2) from ⟨(lt_of_not_ge hsmall).le,hx.2⟩)
      (fun z _ => T_deriv z) hc (by linarith [shoulder.2.1] : 0≤T1 (11/10))
    have hquarter : 0<T (Real.pi/2) := by
      simp only [T,Real.sin_pi_div_two,Real.cos_pi_div_two,mul_zero,mul_one,
        one_pow,sub_zero,add_zero]
      norm_num [kk,aa,bb,g]
      linarith [FrameLowPair.pi_lower]
    exact (lt_min (by linarith [shoulder.1]) hquarter).trans_le hh

def dh : ℝ := a1-1/2
def G1 (x : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x+Real.cos x-1)-L1+g/2+
    g*((13/12)*Real.cos x-dh)/Real.sin x
def G2 (x : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x-Real.cos x-1)-L1+g/2+
    g*((1/12)*Real.cos x-dh)/Real.sin x
def G2d (x : ℝ) : ℝ :=
  1-(9/100)*(Real.sin x+Real.cos x)+
    g*(dh*Real.cos x-1/12)/(Real.sin x)^2
def G (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x-L1+
    (g/Real.sin x)*(pairWidth x-a1+ac*Real.cos x)

theorem G1_lower {x : ℝ} (hx : x∈Icc (3/5:ℝ) (Real.pi/2)) :
    (91/100:ℝ)<G1 x := by
  have hs : 0<Real.sin x := by
    have hh := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2)≤(3/5:ℝ)) hx.2 hx.1
    linarith [endpoint_trig.1]
  have he : (G1 x-91/100)*Real.sin x-T x=
      (307/1000-L1)*Real.sin x+g*(bb-dh) := by
    dsimp [G1,T,aa,bb,kk,g]
    field_simp [ne_of_gt hs]
    ring
  have hL : 0<(307/1000-L1)*Real.sin x := by
    exact mul_pos (by linarith [L1_bounds.2]) hs
  have ha : 0<g*(bb-dh) := by
    apply mul_pos (by norm_num [g])
    dsimp [bb,dh]
    linarith [a1_bounds.2]
  have ht := T_positive hx
  nlinarith

theorem G2_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt G2 (G2d x) x := by
  have hbase := ((((hasDerivAt_id' x).fun_sub
    ((((Real.hasDerivAt_sin x).fun_sub (Real.hasDerivAt_cos x)).sub_const 1).const_mul
      (9/100))).sub_const L1).add_const (g/2))
  have hquot := ((((Real.hasDerivAt_cos x).const_mul (1/12)).sub_const dh).const_mul g).fun_div
    (Real.hasDerivAt_sin x) hs
  convert hbase.fun_add hquot using 1
  · rfl
  · simp only [G2d]
    field_simp
    linear_combination (100*g)*Real.sin_sq_add_cos_sq x

theorem second_trig {x : ℝ} (hx : x∈Icc (Real.pi/2) (41/20:ℝ)) :
    (887/1000:ℝ)<Real.sin x ∧ -(231/500:ℝ)<Real.cos x ∧ Real.cos x≤0 := by
  have hs := sin_endpoint_lower (by positivity : 0≤Real.pi/2)
    (by linarith [FrameLowPair.pi_lower] : (41/20:ℝ)≤Real.pi) hx
    (by rw [Real.sin_pi_div_two]; norm_num : (887/1000:ℝ)<Real.sin (Real.pi/2))
    endpoint_trig.2.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1,Real.pi_pos] : 0≤x)
    (by linarith [FrameLowPair.pi_lower] : (41/20:ℝ)≤Real.pi) hx.2
  exact ⟨hs,by linarith [endpoint_trig.2.2],
    (second_signs ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩).2⟩

theorem G2d_positive {x : ℝ} (hx : x∈Icc (Real.pi/2) (41/20:ℝ)) : 0<G2d x := by
  have ht := second_trig hx
  have hd : 0≤dh ∧ dh≤4/5 := by
    dsimp [dh]
    constructor <;> linarith [a1_bounds.1,a1_bounds.2]
  have hdc := mul_le_mul_of_nonneg_left ht.2.1.le hd.1
  have hn : -(4/5)*(231/500)-1/12≤dh*Real.cos x-1/12 := by nlinarith
  have hs2 := pow_le_pow_left₀ (show (0:ℝ)≤887/1000 by norm_num) ht.1.le 2
  have hquot := negative_div_lower hn (by norm_num : -(4/5:ℝ)*(231/500)-1/12≤0)
    (by norm_num : (0:ℝ)<(887/1000)^2) hs2
  have hQ : -(1358800/2360307:ℝ)≤(dh*Real.cos x-1/12)/(Real.sin x)^2 :=
    le_trans (by norm_num) hquot
  have hscaled := mul_le_mul_of_nonneg_left hQ (show 0≤g by norm_num [g])
  have hgv : g=269343/250000 := rfl
  dsimp only [G2d]
  rw [mul_div_assoc]
  linarith [Real.sin_le_one x]

theorem G2_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (41/20:ℝ)) :
    (91/100:ℝ)<G2 x := by
  have hm : MonotoneOn G2 (Icc (Real.pi/2) (41/20:ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z hz => (G2_deriv (by linarith [(second_trig hz).1])).continuousAt.continuousWithinAt
    · exact fun z hz => G2_deriv (by linarith [(second_trig (Ioo_subset_Icc_self hz)).1])
    · exact fun z hz => (G2d_positive (Ioo_subset_Icc_self hz)).le
  have he : G2 (Real.pi/2)=G1 (Real.pi/2) := by simp [G2,G1]
  have hh := hm ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1
  rw [he] at hh
  exact (G1_lower ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩).trans_le hh

theorem G_lower {x : ℝ} (hx : x∈Icc (3/5:ℝ) (41/20)) : (91/100:ℝ)<G x := by
  have hs : Real.sin x≠0 := by linarith [interval_sine hx]
  by_cases hxQ : x≤Real.pi/2
  · have he : G x=G1 x := by
      dsimp [G,G1,dh,ac]
      rw [(first_width ⟨by linarith [hx.1],hxQ⟩).1,
        (first_width ⟨by linarith [hx.1],hxQ⟩).2]
      field_simp [hs]
      ring
    rw [he]
    exact G1_lower ⟨hx.1,hxQ⟩
  · have he : G x=G2 x := by
      dsimp [G,G2,dh,ac]
      have hx' : x∈Icc (Real.pi/2) Real.pi :=
        ⟨(lt_of_not_ge hxQ).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
      rw [(second_width hx').1,(second_width hx').2]
      field_simp [hs]
      ring
    rw [he]
    exact G2_lower ⟨(lt_of_not_ge hxQ).le,hx.2⟩

end SquaresInCircles.Eight.TableFree.FrameCoreLowCancellation
