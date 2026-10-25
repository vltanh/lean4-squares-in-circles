module

public import SquaresInCircles.Eight.TableFree.FrameMidHighContactArc

/-!
# The actual high-source contact through the quarter turn

The middle target remains fixed.  The high point moves on its actual
circle along the explicit primary-minus-transverse level.  Both one-sided
charged derivatives have strict signs on the complete strip, and every
original weakly feasible high source lies below this contact parameter.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighSourceContact
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FrameMidHighContactArc

def L (before : Bool) (b e : ℝ) : ℝ := W before e-D e*A b+C e*b+1
def Ld (before : Bool) (b e : ℝ) : ℝ := Wd before e-C e*A b-D e*b
def Y (before : Bool) (b e : ℝ) : ℝ := FrameDiagonalContactRoot.Y 1 1 (L before b e)
def Yd (before : Bool) (b e : ℝ) : ℝ :=
  FrameDiagonalContactRoot.YD 1 1 (L before b e) 0 0 (Ld before b e)
def denominator (before : Bool) (b e : ℝ) : ℝ := 1+slope (Y before b e)
def F (before : Bool) (b e : ℝ) : ℝ := angular before e-M b-H (Y before b e)
def Fd (before : Bool) (b e : ℝ) : ℝ :=
  1-(9/100)*Wd before e-Hd (Y before b e)*Yd before b e

theorem L_bounds {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    L before b e∈Icc (19/10:ℝ) (243/100) := by
  have ha := A_mid_bounds hb
  have ht := CD_bounds (side_subset he)
  have hw := W_bounds he
  have hA0 : 0≤A b := by linarith [ha.1,a2_precise.1]
  have hb0 : 0≤b := (mid_subset hb).1
  have hDAU := mul_le_mul ht.2.2
    (show A b≤857/500 by linarith [ha.2,a1_precise.2]) hA0 (by norm_num)
  have hDAL := mul_le_mul ht.2.1
    (show (1623/1000:ℝ)≤A b by linarith [ha.1,a2_precise.1])
    (by norm_num) (by linarith [ht.2.1] : 0≤D e)
  have hCbU := mul_le_mul ht.1.2
    (show b≤39/40 by linarith [hb.2,b2_bounds.2]) hb0 (by norm_num)
  have hCbL := mul_le_mul ht.1.1
    (show (137/200:ℝ)≤b by linarith [hb.1,b1_bounds.1])
    (by norm_num) (by linarith [ht.1.1] : 0≤C e)
  dsimp [L]
  constructor <;> nlinarith

theorem root_data {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    0<4*Q0-(L before b e)^2 ∧ 0<Y before b e ∧ Y before b e<4/5 ∧
      0<FrameDiagonalContactRoot.X 1 1 (L before b e)+1 :=
  FrameDiagonalContactRoot.source_root_bounds (L_bounds hb he)

theorem Y_mem {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    Y before b e∈extended :=
  ⟨(root_data hb he).2.1.le,(root_data hb he).2.2.1.le⟩

theorem radial {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    FrameDiagonalContactRoot.X 1 1 (L before b e)=A (Y before b e) :=
  FrameDiagonalContactRoot.X_eq_chart (by norm_num) (root_data hb he).1.le
    (root_data hb he).2.2.2.le

theorem contact {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    A (Y before b e)-Y before b e+D e*A b-C e*b=W before e := by
  have hh := FrameDiagonalContactRoot.contact (c := (1:ℝ)) (d := (1:ℝ))
    (l := L before b e) (by norm_num)
  rw [radial hb he] at hh
  change 1*(A (Y before b e)+1)-1*Y before b e=L before b e at hh
  dsimp [L] at hh
  linarith

theorem L_deriv (before : Bool) (b e : ℝ) : HasDerivAt (L before b) (Ld before b e) e := by
  have hh := (((W_deriv before e).fun_sub ((D_deriv e).mul_const (A b))).fun_add
    ((C_deriv e).mul_const b)).add_const 1
  rw [show L before b=fun x => W before x-D x*A b+C x*b+1 from rfl]
  exact hh.congr_deriv (by simp only [Ld]; ring)

theorem Y_deriv {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    HasDerivAt (Y before b) (Yd before b e) e :=
  FrameDiagonalContactRoot.Y_deriv (hasDerivAt_const e 1) (hasDerivAt_const e 1)
    (L_deriv before b e) (root_data hb he).1

theorem denominator_bounds {before : Bool} {b e : ℝ}
    (hb : b∈Icc b1 b2) (he : e∈side before) :
    1≤denominator before b e ∧ denominator before b e<13/10 := by
  have hr := extended_slope (Y_mem hb he)
  dsimp [denominator]
  constructor <;> linarith

theorem speed_identity {before : Bool} {b e : ℝ}
    (hb : b∈Icc b1 b2) (he : e∈side before) :
    Yd before b e*denominator before b e=C e*A b+D e*b-Wd before e := by
  have hh := FrameDiagonalContactRoot.YD_contact (c := (1:ℝ)) (d := (1:ℝ))
    (cp := (0:ℝ)) (dp := (0:ℝ)) (lp := Ld before b e)
    (by norm_num) (by norm_num) (root_data hb he).1 (root_data hb he).2.2.2.ne'
  rw [radial hb he] at hh
  change Yd before b e*(1+1*(Y before b e/(A (Y before b e)+1)))=
    0*(A (Y before b e)+1)-0*Y before b e-Ld before b e at hh
  dsimp [denominator,FrameDiagonalArc.slope]
  dsimp [Ld] at hh
  linarith

theorem before_speed {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side true) :
    (64/25:ℝ)<Yd true b e := by
  have hid := speed_identity hb he
  have ht := CD_bounds (side_subset he)
  have ha := A_mid_bounds hb
  have hsum := middle_sum_lower hb
  have hden := denominator_bounds hb he
  have hden0 : 0<denominator true b e := by linarith
  have hCA := mul_le_mul_of_nonneg_right ht.1.1
    (show 0≤A b by linarith [ha.1,a2_precise.1])
  have hDB := mul_le_mul_of_nonneg_right ht.2.1
    (show 0≤b+1 by linarith [(mid_subset hb).1])
  dsimp [Wd] at hid
  apply lt_of_mul_lt_mul_right _ hden0.le
  linarith

theorem after_speed {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side false) :
    0<Yd false b e ∧ Yd false b e<(3417/2000:ℝ) := by
  have hid := speed_identity hb he
  have ht := CD_bounds (side_subset he)
  have hs := side_signs he
  have ha := A_mid_bounds hb
  have hden := denominator_bounds hb he
  have hden0 : 0<denominator false b e := by linarith
  have hb0 := (mid_subset hb).1
  have hnum0 : 0<C e*(A b-1)+D e*b := by
    have hp := mul_pos (show 0<C e by linarith [ht.1.1])
      (show 0<A b-1 by linarith [ha.1,a2_precise.1])
    have hq := mul_nonneg (show 0≤D e by linarith [ht.2.1]) hb0
    linarith
  have hnumU : C e*(A b-1)+D e*b<(3417/2000:ℝ) := by
    have hp := mul_le_mul_of_nonneg_right hs.2.1
      (show 0≤A b-1 by linarith [ha.1,a2_precise.1])
    have hq := mul_le_mul ht.2.2
      (show b≤39/40 by linarith [hb.2,b2_bounds.2]) hb0 (by norm_num)
    nlinarith [ha.2,a1_precise.2]
  have hid' : Yd false b e*denominator false b e=C e*(A b-1)+D e*b := by
    dsimp [Wd] at hid
    linarith
  have hypos : 0<Yd false b e :=
    (mul_pos_iff_of_pos_right hden0).mp (by rw [hid']; exact hnum0)
  have hmul := mul_le_mul_of_nonneg_left hden.1 hypos.le
  exact ⟨hypos,by nlinarith⟩

theorem F_deriv {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    HasDerivAt (F before b) (Fd before b e) e := by
  have hh := ((angular_deriv before e).sub_const (M b)).fun_sub
    ((H_deriv_extended (Y_mem hb he)).comp e (Y_deriv hb he))
  rw [show F before b=fun x => angular before x-M b-(H ∘ Y before b) x from rfl]
  exact hh.congr_deriv (by simp only [Fd])

theorem before_Fd_negative {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side true) :
    Fd true b e<0 := by
  have hy := before_speed hb he
  have hH := (Hd_extended (Y_mem hb he)).1
  have hHp : 0<Hd (Y true b e) := by dsimp [u,v] at hH; linarith
  have hprod := mul_lt_mul_of_pos_left hy hHp
  have ha := angular_derivative_bounds he
  dsimp [Fd,u,v] at *
  nlinarith

theorem after_Fd_positive {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side false) :
    0<Fd false b e := by
  have hy := after_speed hb he
  have hH := (Hd_extended (Y_mem hb he)).2
  have hprod := mul_le_mul_of_nonneg_right hH hy.1.le
  have ha := angular_derivative_bounds he
  dsimp [Fd,v] at *
  nlinarith

theorem before_antitone {b : ℝ} (hb : b∈Icc b1 b2) : AntitoneOn (F true b) (side true) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun e he => (F_deriv hb he).continuousAt.continuousWithinAt
  · exact fun e he => F_deriv hb (Ioo_subset_Icc_self he)
  · exact fun e he => (before_Fd_negative hb (Ioo_subset_Icc_self he)).le

theorem after_monotone {b : ℝ} (hb : b∈Icc b1 b2) : MonotoneOn (F false b) (side false) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun e he => (F_deriv hb he).continuousAt.continuousWithinAt
  · exact fun e he => F_deriv hb (Ioo_subset_Icc_self he)
  · exact fun e he => (after_Fd_positive hb (Ioo_subset_Icc_self he)).le

theorem quarter_minimum {before : Bool} {b e : ℝ}
    (hb : b∈Icc b1 b2) (he : e∈side before) : F before b 0≤F before b e := by
  cases before
  · exact after_monotone hb (zero_side false) he he.1
  · exact before_antitone hb he (zero_side true) he.2

theorem F_zero_lower (before : Bool) {b : ℝ} (hb : b∈Icc b1 b2) :
    (4463/5000:ℝ)<F before b 0 := by
  have hc := contact hb (zero_side before)
  simp only [C_zero,D_zero,W_zero,one_mul] at hc
  have hh := FrameMidHighAlignedContact.actual_aligned_lower hb
    (extended_subset (Y_mem hb (zero_side before))) (by linarith :
      (A b-b)+(A (Y before b 0)-Y before b 0)=2)
  simpa only [F,angular_zero] using hh

theorem F_lower {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    (4463/5000:ℝ)<F before b e :=
  (F_zero_lower before hb).trans_le (quarter_minimum hb he)

theorem actual_source_le {before : Bool} {b B e : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (he : e∈side before)
    (hm : 0≤central false true (A B) B (A b) b (Real.pi/2+e)) : B≤Y before b e := by
  have hactual : W before e≤A B-B+D e*A b-C e*b := by
    dsimp [central,sign] at hm
    rw [(angle_trig e).1,(angle_trig e).2,← W_actual he] at hm
    dsimp [C,D]
    linarith
  have hc := contact hb he
  by_contra! hbad
  have hA := A_antitone (extended_subset (Y_mem hb he)) (high_subset hB) hbad.le
  linarith

theorem actual_lower {before : Bool} {b B e : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (he : e∈side before)
    (hm : 0≤central false true (A B) B (A b) b (Real.pi/2+e)) :
    (4463/5000:ℝ)<cost false true false true B b (Real.pi/2+e) := by
  have hy := actual_source_le hb hB he hm
  have hH := H_monotone_extended (high_extended hB) (Y_mem hb he) hy
  have hF := F_lower hb he
  rw [F,angular_actual he] at hF
  dsimp [cost,marker,sign]
  linarith

end SquaresInCircles.Eight.TableFree.FrameMidHighSourceContact
