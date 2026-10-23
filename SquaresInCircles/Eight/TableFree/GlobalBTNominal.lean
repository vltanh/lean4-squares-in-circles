module

public import SquaresInCircles.Eight.TableFree.GlobalBTMarkers

/-!
# All-original-axis nominal bounds on the short return path

Each original projection rotates exactly one actual center.  Its
center norm bounds the full signed rotation increment, and the same
error's square width recovers the nominal inequality.  The three
actual return projections then constrain A without any H/G sign or
quarter-owner assumption.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign GlobalQuarterSign

def projection (quarter : Bool) (s t : State) (d : ℝ) : Fin 4→ℝ :=
  if quarter then
    ![transverse s+t.a*Real.cos d+transverse t*Real.sin d,
      t.a+s.a*Real.sin d+transverse s*Real.cos d,
      s.a*Real.cos d-transverse s*Real.sin d-transverse t,
      s.a+t.a*Real.sin d-transverse t*Real.cos d]
  else
    ![transverse s+t.a*Real.sin d-transverse t*Real.cos d,
      t.a-s.a*Real.cos d+transverse s*Real.sin d,
      s.a*Real.sin d+transverse s*Real.cos d-transverse t,
      s.a-t.a*Real.cos d-transverse t*Real.sin d]

def nominal (quarter : Bool) (s t : State) (j : Fin 4) : ℝ := projection quarter s t 0 j

theorem projection_feasible (quarter : Bool) (s t : State) (j : Fin 4) {d : ℝ}
    (hd : |d|≤frameCap) :
    s.Feasible t j ((if quarter then Real.pi/2 else 0)+d) ↔
      width d≤projection quarter s t d j := by
  cases quarter <;> fin_cases j <;>
    simp [State.Feasible,forwardMargin,projection,transverse,
      Real.sin_add,Real.cos_add,width,
      CommonQuarter.signed_width (by simpa only [frameCap] using hd),
      CommonQuarter.quarter_width (by simpa only [frameCap] using hd)] <;>
    constructor <;> intro hh <;> linarith

theorem transverse_sq (s : State) : (transverse s)^2=s.b^2 := by
  cases hp : s.positive <;> simp [transverse,FramePair.sign,hp]

theorem transverse_bounds (s : State) : -s.b≤transverse s ∧ transverse s≤s.b := by
  cases hp : s.positive <;> simp [transverse,FramePair.sign,hp] <;> linarith [s.b_nonneg]

theorem state_sum_sharp (s : State) : s.a+s.b≤2*c0 := by
  have hc := state_circle s
  have hh := c0_circle
  have ha := s.a_pos
  have hb := s.b_nonneg
  have hd := c0_bounds.1
  by_contra! hn
  have hm := mul_pos (show 0<s.a+s.b-2*c0 by linarith)
    (show 0<s.a+s.b+2*c0+2 by linarith)
  nlinarith [sq_nonneg (s.a-s.b)]

/-- The complete signed rotation increment, for arbitrary real force
components, uses the one original center norm. -/
theorem rotation_increment {a b d : ℝ} (hn : a^2+b^2≤(283/200:ℝ)^2) :
    a*(Real.cos d-1)+b*Real.sin d≤(283/200)*|d| := by
  have hc := Real.one_sub_sq_div_two_le_cos d
  have hunit := Real.sin_sq_add_cos_sq d
  have hdelta : (Real.cos d-1)^2+(Real.sin d)^2≤d^2 := by nlinarith
  have hforce : 0≤a^2+b^2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hdelta hforce
  have h2 := mul_le_mul_of_nonneg_right hn (sq_nonneg d)
  have hid : (a^2+b^2)*((Real.cos d-1)^2+(Real.sin d)^2)-
      (a*(Real.cos d-1)+b*Real.sin d)^2=
      (a*Real.sin d-b*(Real.cos d-1))^2 := by ring
  have hsq : (a*(Real.cos d-1)+b*Real.sin d)^2≤((283/200)*|d|)^2 := by
    rw [mul_pow,sq_abs]
    nlinarith only [h1,h2,hid,sq_nonneg (a*Real.sin d-b*(Real.cos d-1))]
  have hp : 0≤(283/200:ℝ)*|d| := mul_nonneg (by norm_num) (abs_nonneg d)
  nlinarith only [hsq,hp]

theorem projection_increment (quarter : Bool) (s t : State) (j : Fin 4) (d : ℝ) :
    projection quarter s t d j-nominal quarter s t j≤(283/200)*|d| := by
  have hs := (state_norm_sq s).le
  have ht := (state_norm_sq t).le
  have hss := transverse_sq s
  have hts := transverse_sq t
  cases quarter with
  | false =>
      fin_cases j
      · have hh := rotation_increment (a := -transverse t) (b := t.a) (d := d) (by nlinarith)
        dsimp [projection,nominal] at *
        norm_num at *
        linarith
      · have hh := rotation_increment (a := -s.a) (b := transverse s) (d := d) (by nlinarith)
        dsimp [projection,nominal] at *
        norm_num at *
        linarith
      · have hh := rotation_increment (a := transverse s) (b := s.a) (d := d) (by nlinarith)
        dsimp [projection,nominal] at *
        norm_num at *
        linarith
      · have hh := rotation_increment (a := -t.a) (b := -transverse t) (d := d) (by nlinarith)
        dsimp [projection,nominal] at *
        norm_num at *
        linarith
  | true =>
      fin_cases j
      · have hh := rotation_increment (a := t.a) (b := transverse t) (d := d) (by nlinarith)
        dsimp [projection,nominal] at *
        norm_num at *
        linarith
      · have hh := rotation_increment (a := transverse s) (b := s.a) (d := d) (by nlinarith)
        dsimp [projection,nominal] at *
        norm_num at *
        linarith
      · have hh := rotation_increment (a := s.a) (b := -transverse s) (d := d) (by nlinarith)
        dsimp [projection,nominal] at *
        norm_num at *
        linarith
      · have hh := rotation_increment (a := -transverse t) (b := t.a) (d := d) (by nlinarith)
        dsimp [projection,nominal] at *
        norm_num at *
        linarith

theorem width_abs (d : ℝ) : width d=width |d| := by
  by_cases hp : 0≤d
  · rw [abs_of_nonneg hp]
  · rw [abs_of_nonpos (by linarith : d≤0)]
    simp [width,Real.cos_neg,Real.sin_neg,abs_neg]

theorem short_width_reserve {d : ℝ} (hd : |d|≤(3/10:ℝ)) :
    1-|d|≤width d-(283/200)*|d| := by
  let z := |d|
  have hz : z∈Icc 0 (3/10:ℝ) := ⟨abs_nonneg d,hd⟩
  have hc := cos_lower_two hz.1
  have hs := sin_lower_three hz.1
  have hs0 := (transport_trig (show z∈Icc 0 frameCap by
    exact ⟨hz.1,by change z≤(7/10:ℝ); linarith [hz.2]⟩)).2.2.1
  have h2 : z^2≤(3/10)*z := by nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  have h3 := mul_le_mul_of_nonneg_right h2 hz.1
  have h4 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ)≤3/10)
  rw [width_abs,width,abs_of_nonneg hs0]
  change 1-z≤(1+Real.cos z+Real.sin z)/2-(283/200)*z
  nlinarith

/-- All four original axes, both signs and both zero/quarter words. -/
theorem original_nominal_lower (quarter : Bool) (s t : State) (j : Fin 4) {d : ℝ}
    (hd : |d|≤(3/10:ℝ))
    (hm : s.Feasible t j ((if quarter then Real.pi/2 else 0)+d)) :
    1-|d|≤nominal quarter s t j := by
  have hf := (projection_feasible quarter s t j
    (by change |d|≤(7/10:ℝ); linarith [hd])).1 hm
  linarith [projection_increment quarter s t j d,short_width_reserve hd]

theorem three_nominal_upper (e h g a : State) (jE jH jG : Fin 4)
    (he : transverse e≤0) (ha : 0≤transverse a) (hH : jH=0 ∨ jH=2) :
    nominal true e h jE+nominal false h g jH+nominal true g a jG≤4*c0-a.b := by
  have heq := transverse_nonpos_eq e he
  have haq := transverse_of_nonneg a ha
  have hHsum := state_sum_sharp h
  have hGsum := state_sum_sharp g
  have hAsum := state_sum_sharp a
  have hEsum := state_sum_sharp e
  have hHy := transverse_bounds h
  have hGy := transverse_bounds g
  change transverse e= -e.b at heq
  fin_cases jE <;> fin_cases jG <;> rcases hH with rfl | rfl <;>
    simp only [nominal,projection,Bool.true_eq_true,Bool.false_eq_true,if_true,if_false,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero,sub_zero,heq,haq] <;>
    linarith [e.b_nonneg,a.b_nonneg]

theorem short_return_endpoint (e h g a : State) (jE jH jG : Fin 4) {r v t : ℝ}
    (he : transverse e≤0) (ha : 0≤transverse a) (hH : jH=0 ∨ jH=2)
    (hshort : |r|+|v|+|t|≤(3/10:ℝ))
    (hEH : e.Feasible h jE (Real.pi/2+r))
    (hHG : h.Feasible g jH v) (hGA : g.Feasible a jG (Real.pi/2+t)) :
    a.b≤4*c0-3+(|r|+|v|+|t|) := by
  have hr : |r|≤(3/10:ℝ) := by linarith [abs_nonneg v,abs_nonneg t]
  have hv : |v|≤(3/10:ℝ) := by linarith [abs_nonneg r,abs_nonneg t]
  have ht : |t|≤(3/10:ℝ) := by linarith [abs_nonneg r,abs_nonneg v]
  have hpE := original_nominal_lower true e h jE hr hEH
  have hpH := original_nominal_lower false h g jH hv (by simpa using hHG)
  have hpG := original_nominal_lower true g a jG ht hGA
  linarith [three_nominal_upper e h g a jE jH jG he ha hH]

end SquaresInCircles.Eight.TableFree.GlobalBT
