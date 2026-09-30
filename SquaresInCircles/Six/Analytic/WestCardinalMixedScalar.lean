import SquaresInCircles.Six.Analytic.HarmonicRootConcavity
import SquaresInCircles.Seven.Analysis
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Five geometric endpoints for the cardinal/cardinal missing-west stress

The W angle is eliminated by an exact two-dimensional Cauchy inequality.
The remaining scalar is a sum J(d)+K(s)+L(pi/2+s-d). Each summand is concave
on its whole physical interval, separately across the actual wall s=0.
The domain is a rectangle and a triangle, whose five vertices are evaluated
by explicit Taylor and squared rational-root comparisons. There is no mesh,
interval-cover checker, or generated stress inventory in the proof.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.WestCardinalMixed

-- The multipliers on CW, CD, CS, WD, DS are 9/40,3/25,1/4,9/40,9/50.
def wP : ℝ := 50687289/800000000
def wQ : ℝ := 10187289/800000000
def wC : ℝ := -49653/800000
def dP : ℝ := 3897/40000
def dQ : ℝ := 27/625
def dC : ℝ := -81/1000
def sP : ℝ := 949/10000
def sQ : ℝ := -9/100

def wRoot (d : ℝ) : ℝ := harmonicRoot wP wQ wC d
def dRoot (r : ℝ) : ℝ := harmonicRoot dP dQ dC r
def sRoot (s : ℝ) : ℝ := harmonicRoot sP sQ 0 s

def westPart (d : ℝ) : ℝ :=
  (1161/25000)*Real.cos d+(1161/25000)*Real.sin d-wRoot d

def diagonalPart (r : ℝ) : ℝ := (9/50)*Real.sin r-(1689/1000)*dRoot r

def southPart (negative : Bool) (s : ℝ) : ℝ :=
  (1/4)*Real.cos s+(if negative then -1/4 else 0)*Real.sin s-(1689/1000)*sRoot s

def reduced (negative : Bool) (d s : ℝ) : ℝ :=
  28353/40000+westPart d+southPart negative s+diagonalPart (Real.pi/2+s-d)

lemma root_upper {p q r x u : ℝ} (hu : 0 ≤ u)
    (h : p+q*Real.sin x+r*Real.cos x ≤ u^2) : harmonicRoot p q r x ≤ u := by
  have hh := Real.sqrt_le_sqrt h
  simpa only [harmonicRoot,Real.sqrt_sq hu] using hh

lemma quarter_root_bounds : (7071:ℝ)/10000 ≤ Real.sqrt 2/2 ∧
    Real.sqrt 2/2 ≤ 7072/10000 := by
  constructor <;> nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]

lemma trig_three_fifths :
    (5646/10000 ≤ Real.sin ((3:ℝ)/5) ∧ Real.sin ((3:ℝ)/5) ≤ 5647/10000) ∧
    (8253/10000 ≤ Real.cos ((3:ℝ)/5) ∧ Real.cos ((3:ℝ)/5) ≤ 8254/10000) := by
  have hslo := Seven.sin_lower_seven (x := (3:ℝ)/5) (by norm_num)
  have hshi := Seven.sin_upper_five (x := (3:ℝ)/5) (by norm_num)
  have hclo := Seven.cos_lower_six (x := (3:ℝ)/5) (by norm_num)
  have hchi := Seven.cos_upper_four (x := (3:ℝ)/5) (by norm_num)
  constructor <;> constructor <;> nlinarith

lemma trig_two_fifths :
    (3894/10000 ≤ Real.sin ((2:ℝ)/5) ∧ Real.sin ((2:ℝ)/5) ≤ 3895/10000) ∧
    (921/1000 ≤ Real.cos ((2:ℝ)/5) ∧ Real.cos ((2:ℝ)/5) ≤ 9211/10000) := by
  have hslo := Seven.sin_lower_seven (x := (2:ℝ)/5) (by norm_num)
  have hshi := Seven.sin_upper_five (x := (2:ℝ)/5) (by norm_num)
  have hclo := Seven.cos_lower_six (x := (2:ℝ)/5) (by norm_num)
  have hchi := Seven.cos_upper_four (x := (2:ℝ)/5) (by norm_num)
  constructor <;> constructor <;> nlinarith

lemma trig_one_fifth :
    (1986/10000 ≤ Real.sin ((1:ℝ)/5) ∧ Real.sin ((1:ℝ)/5) ≤ 1987/10000) ∧
    (98/100 ≤ Real.cos ((1:ℝ)/5) ∧ Real.cos ((1:ℝ)/5) ≤ 9801/10000) := by
  have hslo := Seven.sin_lower_seven (x := (1:ℝ)/5) (by norm_num)
  have hshi := Seven.sin_upper_five (x := (1:ℝ)/5) (by norm_num)
  have hclo := Seven.cos_lower_six (x := (1:ℝ)/5) (by norm_num)
  have hchi := Seven.cos_upper_four (x := (1:ℝ)/5) (by norm_num)
  constructor <;> constructor <;> nlinarith

private lemma diagonal_trig {d : ℝ} (hd : 3/5 ≤ d ∧ d ≤ Real.pi/4) :
    (14/25 ≤ Real.sin d ∧ Real.sin d ≤ 71/100) ∧ 7/10 ≤ Real.cos d := by
  have hd0 : 0 ≤ d := by linarith [hd.1]
  have hslo := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (3:ℝ)/5 by linarith [Real.pi_pos])
    (show d ≤ Real.pi/2 by linarith [hd.2,Real.pi_pos]) hd.1
  have hshi := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ d by linarith [Real.pi_pos])
    (show Real.pi/4 ≤ Real.pi/2 by linarith [Real.pi_pos]) hd.2
  have hclo := Real.cos_le_cos_of_nonneg_of_le_pi hd0
    (show Real.pi/4 ≤ Real.pi by linarith [Real.pi_pos]) hd.2
  rw [Real.sin_pi_div_four] at hshi
  rw [Real.cos_pi_div_four] at hclo
  exact ⟨⟨by linarith [trig_three_fifths.1.1],by linarith [quarter_root_bounds.2]⟩,
    by linarith [quarter_root_bounds.1]⟩

private lemma west_root_positive {d : ℝ} (hd : 3/5 ≤ d ∧ d ≤ Real.pi/4) :
    0 < wP+wQ*Real.sin d+wC*Real.cos d := by
  have ht := diagonal_trig hd
  have hc := Real.cos_le_one d
  norm_num [wP,wQ,wC] at *
  nlinarith [ht.1.1]

private lemma west_root_small {d : ℝ} (hd : 3/5 ≤ d ∧ d ≤ Real.pi/4) :
    wRoot d ≤ 1/5 := by
  apply root_upper (by norm_num)
  have ht := diagonal_trig hd
  norm_num [wP,wQ,wC]
  nlinarith [ht.1.2,ht.2]

lemma westPart_concave : ConcaveOn ℝ (Set.Icc (3/5) (Real.pi/4)) westPart := by
  have h := harmonic_root_trig_concave
    (A := 1161/25000) (B := 1161/25000) (p := wP) (q := wQ) (r := wC) (R := 1)
    (by norm_num) (by norm_num [wP,wQ,wC])
    (fun d hd => west_root_positive hd)
    (fun d hd => by
      have hs := west_root_small hd
      have ht := diagonal_trig hd
      change 1*wRoot d ≤ _
      nlinarith [ht.1.1,ht.2])
  simpa only [westPart,wRoot,one_mul] using h

private lemma right_gap_trig {r : ℝ}
    (hr : Real.pi/4 ≤ r ∧ r ≤ Real.pi/2-1/5) :
    (7/10 ≤ Real.sin r ∧ Real.sin r ≤ 1) ∧ (0 ≤ Real.cos r ∧ Real.cos r ≤ 71/100) := by
  have hr0 : 0 ≤ r := by linarith [hr.1,Real.pi_pos]
  have hrpi : r ≤ Real.pi/2 := by linarith [hr.2]
  have hslo := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ Real.pi/4 by linarith [Real.pi_pos]) hrpi hr.1
  have hchi := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ Real.pi/4 by linarith [Real.pi_pos])
    (show r ≤ Real.pi by linarith [hrpi,Real.pi_pos]) hr.1
  rw [Real.sin_pi_div_four] at hslo
  rw [Real.cos_pi_div_four] at hchi
  exact ⟨⟨by linarith [quarter_root_bounds.1],Real.sin_le_one r⟩,
    ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hrpi⟩,
      by linarith [quarter_root_bounds.2]⟩⟩

private lemma right_root_positive {r : ℝ}
    (hr : Real.pi/4 ≤ r ∧ r ≤ Real.pi/2-1/5) :
    0 < dP+dQ*Real.sin r+dC*Real.cos r := by
  have ht := right_gap_trig hr
  norm_num [dP,dQ,dC]
  nlinarith [ht.1.1,ht.2.2]

private lemma right_root_curvature {r : ℝ}
    (hr : Real.pi/4 ≤ r ∧ r ≤ Real.pi/2-1/5) :
    (1689/1000)*dRoot r ≤ (18/25)*Real.sin r := by
  obtain ⟨⟨hslo,hshi⟩,⟨hclo,hchi⟩⟩ := right_gap_trig hr
  have hu := Real.sin_sq_add_cos_sq r
  have hline : (23/10)*(1-Real.sin r) ≤ Real.cos r := by
    have h1 : 0 ≤ 1-Real.sin r := by linarith
    have hp := mul_nonneg h1
      (show 0 ≤ 1+Real.sin r-(529/100)*(1-Real.sin r) by linarith)
    by_contra! hbad
    have hh := mul_pos (sub_pos.mpr hbad)
      (show 0 < (23/10)*(1-Real.sin r)+Real.cos r by linarith)
    nlinarith only [hu,hp,hh]
  have hradbound : dP+dQ*Real.sin r+dC*Real.cos r ≤
      dP+dQ*Real.sin r+dC*((23/10)*(1-Real.sin r)) := by
    dsimp [dC]
    linarith
  have hpoly := mul_nonneg (show 0 ≤ Real.sin r-7/10 by linarith)
    (show 0 ≤ (18/25)^2*(Real.sin r+7/10)-(1689/1000)^2*(dQ-(23/10)*dC) by
      norm_num [dQ,dC]
      linarith)
  have hreserve : (1689/1000)^2*(dP+dQ*Real.sin r+dC*Real.cos r) ≤
      (18/25)^2*(Real.sin r)^2 := by
    norm_num [dP,dQ,dC] at hradbound hpoly ⊢
    nlinarith only [hradbound,hpoly]
  have hs : (dRoot r)^2=dP+dQ*Real.sin r+dC*Real.cos r :=
    Real.sq_sqrt (right_root_positive hr).le
  have hn : 0 ≤ dRoot r := Real.sqrt_nonneg _
  by_contra! hbad
  have hp := mul_pos (sub_pos.mpr hbad)
    (show 0 < (1689/1000)*dRoot r+(18/25)*Real.sin r by linarith)
  nlinarith only [hs,hreserve,hp]

lemma diagonalPart_concave :
    ConcaveOn ℝ (Set.Icc (Real.pi/4) (Real.pi/2-1/5)) diagonalPart := by
  have h := harmonic_root_trig_concave
    (A := 0) (B := 9/50) (p := dP) (q := dQ) (r := dC) (R := 1689/1000)
    (by norm_num) (by norm_num [dP,dQ,dC])
    (fun r hr => right_root_positive hr)
    (fun r hr => by
      have hh := right_root_curvature hr
      change (1689/1000)*dRoot r ≤ _
      linarith)
  simpa only [diagonalPart,dRoot,zero_mul,zero_add] using h

private lemma south_root_positive (s : ℝ) : 0 < sP+sQ*Real.sin s+0*Real.cos s := by
  have h := Real.sin_le_one s
  norm_num [sP,sQ]
  linarith

private lemma south_root_small (s : ℝ) : sRoot s ≤ 1/2 := by
  apply root_upper (by norm_num)
  have h := Real.neg_one_le_sin s
  norm_num [sP,sQ]
  linarith

private lemma small_cos_lower {s : ℝ} (hs : |s| ≤ 2/5) : 23/25 ≤ Real.cos s := by
  have hp := mul_nonneg (sub_nonneg.mpr hs)
    (show 0 ≤ (2:ℝ)/5+|s| by positivity)
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := s),sq_abs s]

lemma southPart_positive_concave :
    ConcaveOn ℝ (Set.Icc 0 (2/5)) (southPart false) := by
  have h := harmonic_root_trig_concave
    (A := 1/4) (B := 0) (p := sP) (q := sQ) (r := 0) (R := 1689/1000)
    (by norm_num) (by norm_num [sP,sQ]) (fun s _ => south_root_positive s)
    (fun s hs => by
      have hc := small_cos_lower (by rw [abs_of_nonneg hs.1]; exact hs.2)
      have hn := south_root_small s
      change (1689/1000)*sRoot s ≤ _
      linarith)
  simpa only [southPart,sRoot,Bool.false_eq_true,if_false] using h

lemma southPart_negative_concave :
    ConcaveOn ℝ (Set.Icc (3/5-Real.pi/4) 0) (southPart true) := by
  have h := harmonic_root_trig_concave
    (A := 1/4) (B := -1/4) (p := sP) (q := sQ) (r := 0) (R := 1689/1000)
    (by norm_num) (by norm_num [sP,sQ]) (fun s _ => south_root_positive s)
    (fun s hs => by
      have habs : |s| ≤ 2/5 := by
        rw [abs_of_nonpos hs.2]
        linarith [hs.1,Real.pi_lt_d2]
      have hc := small_cos_lower habs
      have hsin : Real.sin s ≤ 0 := by
        have hn := Real.sin_nonneg_of_nonneg_of_le_pi (x := -s)
          (by linarith [hs.2]) (by linarith [hs.1,Real.pi_gt_d2])
        rw [Real.sin_neg] at hn
        linarith
      have hn := south_root_small s
      change (1689/1000)*sRoot s ≤ _
      linarith)
  simpa only [southPart,sRoot,if_true] using h

-- Bounds at the five vertices forced by the rectangle/triangle geometry.
private lemma left_w_root : wRoot (3/5) ≤ 1391/10000 := by
  apply root_upper (by norm_num)
  norm_num [wP,wQ,wC]
  nlinarith [trig_three_fifths.1.2,trig_three_fifths.2.1]

private lemma right_w_root : wRoot (Real.pi/4) ≤ 211/1250 := by
  apply root_upper (by norm_num)
  rw [Real.sin_pi_div_four,Real.cos_pi_div_four]
  norm_num [wP,wQ,wC]
  linarith [quarter_root_bounds.1]

private lemma quarter_d_root : dRoot (Real.pi/4) ≤ 2659/10000 := by
  apply root_upper (by norm_num)
  rw [Real.sin_pi_div_four,Real.cos_pi_div_four]
  norm_num [dP,dQ,dC]
  linarith [quarter_root_bounds.1]

private lemma complement_left_d_root : dRoot (Real.pi/2-3/5) ≤ 739/2500 := by
  apply root_upper (by norm_num)
  rw [Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub]
  norm_num [dP,dQ,dC]
  nlinarith [trig_three_fifths.2.2,trig_three_fifths.1.1]

private lemma complement_small_d_root : dRoot (Real.pi/2-1/5) ≤ 3517/10000 := by
  apply root_upper (by norm_num)
  rw [Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub]
  norm_num [dP,dQ,dC]
  nlinarith [trig_one_fifth.2.2,trig_one_fifth.1.1]

private lemma negative_corner_trig :
    (-1845/10000 ≤ Real.sin (3/5-Real.pi/4) ∧
      Real.sin (3/5-Real.pi/4) ≤ -1842/10000) ∧
    9827/10000 ≤ Real.cos (3/5-Real.pi/4) := by
  let t := Real.sqrt 2/2
  have htlo : (7071:ℝ)/10000 ≤ t := quarter_root_bounds.1
  have hthi : t ≤ 7072/10000 := quarter_root_bounds.2
  have ht0 : 0 ≤ t := by linarith
  have hlo := mul_nonneg
    (show 0 ≤ Real.sin (3/5)-Real.cos (3/5)+2608/10000 by
      linarith [trig_three_fifths.1.1,trig_three_fifths.2.2]) ht0
  have hhi := mul_nonpos_of_nonpos_of_nonneg
    (show Real.sin (3/5)-Real.cos (3/5)+2606/10000 ≤ 0 by
      linarith [trig_three_fifths.1.2,trig_three_fifths.2.1]) ht0
  have hc := mul_nonneg
    (show 0 ≤ Real.sin (3/5)+Real.cos (3/5)-13899/10000 by
      linarith [trig_three_fifths.1.1,trig_three_fifths.2.1]) ht0
  rw [Real.sin_sub,Real.cos_sub,Real.sin_pi_div_four,Real.cos_pi_div_four]
  change ((-1845/10000 ≤ Real.sin (3/5)*t-Real.cos (3/5)*t ∧
    Real.sin (3/5)*t-Real.cos (3/5)*t ≤ -1842/10000) ∧
    9827/10000 ≤ Real.cos (3/5)*t+Real.sin (3/5)*t)
  exact ⟨⟨by nlinarith only [hlo,hthi],by nlinarith only [hhi,htlo]⟩,
    by nlinarith only [hc,htlo]⟩

private lemma positive_corner_trig :
    (9265/10000 ≤ Real.sin (Real.pi/4+2/5) ∧
      Real.sin (Real.pi/4+2/5) ≤ 927/1000) ∧
    3758/10000 ≤ Real.cos (Real.pi/4+2/5) := by
  let t := Real.sqrt 2/2
  have htlo : (7071:ℝ)/10000 ≤ t := quarter_root_bounds.1
  have hthi : t ≤ 7072/10000 := quarter_root_bounds.2
  have ht0 : 0 ≤ t := by linarith
  have hlo := mul_nonneg
    (show 0 ≤ Real.cos (2/5)+Real.sin (2/5)-13104/10000 by
      linarith [trig_two_fifths.2.1,trig_two_fifths.1.1]) ht0
  have hhi := mul_nonpos_of_nonpos_of_nonneg
    (show Real.cos (2/5)+Real.sin (2/5)-13106/10000 ≤ 0 by
      linarith [trig_two_fifths.2.2,trig_two_fifths.1.2]) ht0
  have hc := mul_nonneg
    (show 0 ≤ Real.cos (2/5)-Real.sin (2/5)-5315/10000 by
      linarith [trig_two_fifths.2.1,trig_two_fifths.1.2]) ht0
  rw [Real.sin_add,Real.cos_add,Real.sin_pi_div_four,Real.cos_pi_div_four]
  change ((9265/10000 ≤ t*Real.cos (2/5)+t*Real.sin (2/5) ∧
    t*Real.cos (2/5)+t*Real.sin (2/5) ≤ 927/1000) ∧
    3758/10000 ≤ t*Real.cos (2/5)-t*Real.sin (2/5))
  exact ⟨⟨by nlinarith only [hlo,htlo],by nlinarith only [hhi,hthi]⟩,
    by nlinarith only [hc,htlo]⟩

private lemma positive_corner_d_root : dRoot (Real.pi/4+2/5) ≤ 409/1250 := by
  apply root_upper (by norm_num)
  norm_num [dP,dQ,dC]
  nlinarith [positive_corner_trig.1.2,positive_corner_trig.2]

private lemma negative_s_root : sRoot (3/5-Real.pi/4) ≤ 167/500 := by
  apply root_upper (by norm_num)
  norm_num [sP,sQ]
  nlinarith [negative_corner_trig.1.1]

private lemma zero_s_root : sRoot 0 ≤ 3081/10000 := by
  apply root_upper (by norm_num)
  norm_num [sP,sQ]

private lemma positive_s_root : sRoot (2/5) ≤ 2447/10000 := by
  apply root_upper (by norm_num)
  norm_num [sP,sQ]
  nlinarith [trig_two_fifths.1.1]

lemma left_negative_positive : 0 < reduced true (3/5) (3/5-Real.pi/4) := by
  have hW := left_w_root
  have hD := quarter_d_root
  have hS := negative_s_root
  dsimp [reduced,westPart,southPart,diagonalPart]
  rw [show Real.pi/2+(3/5-Real.pi/4)-3/5=Real.pi/4 by ring,Real.sin_pi_div_four]
  nlinarith [trig_three_fifths.2.1,trig_three_fifths.1.1,
    negative_corner_trig.2,negative_corner_trig.1.2,quarter_root_bounds.1]

lemma left_zero_positive : 0 < reduced false (3/5) 0 := by
  have hW := left_w_root
  have hD := complement_left_d_root
  have hS := zero_s_root
  dsimp [reduced,westPart,southPart,diagonalPart]
  simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,add_zero,
    Real.sin_pi_div_two_sub]
  nlinarith [trig_three_fifths.2.1,trig_three_fifths.1.1]

lemma right_zero_positive : 0 < reduced false (Real.pi/4) 0 := by
  have hW := right_w_root
  have hD := quarter_d_root
  have hS := zero_s_root
  dsimp [reduced,westPart,southPart,diagonalPart]
  simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,add_zero]
  rw [show Real.pi/2-Real.pi/4=Real.pi/4 by ring,
    Real.sin_pi_div_four,Real.cos_pi_div_four]
  nlinarith [quarter_root_bounds.1]

lemma left_positive_positive : 0 < reduced false (3/5) (2/5) := by
  have hW := left_w_root
  have hD := complement_small_d_root
  have hS := positive_s_root
  dsimp [reduced,westPart,southPart,diagonalPart]
  simp only [zero_mul,add_zero]
  rw [show Real.pi/2+2/5-3/5=Real.pi/2-1/5 by ring,Real.sin_pi_div_two_sub]
  nlinarith [trig_three_fifths.2.1,trig_three_fifths.1.1,
    trig_two_fifths.2.1,trig_one_fifth.2.1]

lemma right_positive_positive : 0 < reduced false (Real.pi/4) (2/5) := by
  have hW := right_w_root
  have hD := positive_corner_d_root
  have hS := positive_s_root
  dsimp [reduced,westPart,southPart,diagonalPart]
  simp only [zero_mul,add_zero]
  rw [show Real.pi/2+2/5-Real.pi/4=Real.pi/4+2/5 by ring,
    Real.sin_pi_div_four,Real.cos_pi_div_four]
  nlinarith [quarter_root_bounds.1,trig_two_fifths.2.1,positive_corner_trig.1.1]

private lemma positive_d_slice {s : ℝ} (hs : 0 ≤ s ∧ s ≤ 2/5) :
    ConcaveOn ℝ (Set.Icc (3/5) (Real.pi/4)) (fun d => reduced false d s) := by
  have hL := concave_affine_argument (a := -1) (b := Real.pi/2+s)
    (l := 3/5) (u := Real.pi/4) diagonalPart_concave
    (by intro d hd; constructor <;> linarith [hd.1,hd.2,hs.1,hs.2])
  have h := (((concave_constant (28353/40000) (3/5) (Real.pi/4)).add westPart_concave).add
    (concave_constant (southPart false s) (3/5) (Real.pi/4))).add hL
  convert h using 1
  funext d
  dsimp [reduced]
  congr 1
  congr 1
  ring

private lemma positive_s_slice {d : ℝ} (hd : 3/5 ≤ d ∧ d ≤ Real.pi/4) :
    ConcaveOn ℝ (Set.Icc 0 (2/5)) (fun s => reduced false d s) := by
  have hL := concave_affine_argument (a := 1) (b := Real.pi/2-d)
    (l := 0) (u := 2/5) diagonalPart_concave
    (by intro s hs; constructor <;> linarith [hd.1,hd.2,hs.1,hs.2])
  have h := ((concave_constant (28353/40000+westPart d) 0 (2/5)).add
    southPart_positive_concave).add hL
  convert h using 1
  funext s
  dsimp [reduced]
  congr 1
  congr 1
  ring

private lemma negative_diagonal_slice :
    ConcaveOn ℝ (Set.Icc (3/5) (Real.pi/4))
      (fun d => reduced true d (d-Real.pi/4)) := by
  have hK := concave_affine_argument (a := 1) (b := -Real.pi/4)
    (l := 3/5) (u := Real.pi/4) southPart_negative_concave
    (by intro d hd; constructor <;> linarith [hd.1,hd.2])
  have h := (((concave_constant (28353/40000) (3/5) (Real.pi/4)).add
    westPart_concave).add hK).add
    (concave_constant (diagonalPart (Real.pi/4)) (3/5) (Real.pi/4))
  convert h using 1
  funext d
  dsimp [reduced]
  rw [show Real.pi/2+(d-Real.pi/4)-d=Real.pi/4 by ring]
  simp only [one_mul,sub_eq_add_neg]

private lemma negative_s_slice {d : ℝ} (hd : 3/5 ≤ d ∧ d ≤ Real.pi/4) :
    ConcaveOn ℝ (Set.Icc (d-Real.pi/4) 0) (fun s => reduced true d s) := by
  have hK := concave_affine_argument (a := 1) (b := 0)
    (l := d-Real.pi/4) (u := 0) southPart_negative_concave
    (by intro s hs; constructor <;> linarith [hd.1,hs.1,hs.2])
  have hL := concave_affine_argument (a := 1) (b := Real.pi/2-d)
    (l := d-Real.pi/4) (u := 0) diagonalPart_concave
    (by intro s hs; constructor <;> linarith [hd.1,hd.2,hs.1,hs.2])
  have h := ((concave_constant (28353/40000+westPart d) (d-Real.pi/4) 0).add hK).add hL
  convert h using 1
  funext s
  dsimp [reduced]
  simp only [one_mul,add_zero]
  congr 1
  congr 1
  ring

lemma reduced_at_zero (d : ℝ) : reduced true d 0=reduced false d 0 := by
  simp [reduced,southPart]

/-- The complete cardinal/cardinal reduced domain is covered by a rectangle
and a triangle whose vertices are forced by s=0 and r=pi/4. -/
theorem reduced_positive {d s : ℝ}
    (hd : 3/5 ≤ d ∧ d ≤ Real.pi/4)
    (hs : d-Real.pi/4 ≤ s ∧ s ≤ 2/5) :
    0 < reduced (decide (s<0)) d s := by
  have hz : 0 < reduced false d 0 := positive_on_concave_interval
    (positive_d_slice (s := 0) (by constructor <;> norm_num)) hd
    left_zero_positive right_zero_positive
  by_cases hneg : s<0
  · have hdiag : 0 < reduced true d (d-Real.pi/4) := by
      apply positive_on_concave_interval negative_diagonal_slice hd left_negative_positive
      simpa only [sub_self,reduced_at_zero] using right_zero_positive
    have hzero : 0 < reduced true d 0 := by rwa [reduced_at_zero]
    have h := positive_on_concave_interval (negative_s_slice hd)
      ⟨hs.1,hneg.le⟩ hdiag hzero
    simpa [hneg] using h
  · have hpos : 0 < reduced false d (2/5) := positive_on_concave_interval
      (positive_d_slice (s := 2/5) (by constructor <;> norm_num)) hd
      left_positive_positive right_positive_positive
    have h := positive_on_concave_interval (positive_s_slice hd)
      ⟨le_of_not_gt hneg,hs.2⟩ hz hpos
    simpa [hneg] using h

end SquaresInCircles.Six.Analytic.WestCardinalMixed
