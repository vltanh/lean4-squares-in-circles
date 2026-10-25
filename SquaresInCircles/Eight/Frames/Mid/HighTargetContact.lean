module

public import SquaresInCircles.Eight.Frames.Diagonal.ContactRoot
public import SquaresInCircles.Eight.Frames.Mid.HighAlignedContact
public import SquaresInCircles.Eight.Frames.Mid.HighContactArc

/-!
# Eight squares: the actual high-target contact through the quarter turn

For each fixed original middle point, the explicit circle root retains
the central contact.  Its charged cost decreases up to the quarter turn
and increases afterwards.  Every originally feasible high target is
compared with that root on the same circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighTargetContact
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FrameMidHighContactArc

def L (before : Bool) (b e : ℝ) : ℝ := W before e-(A b-b)+D e
def Ld (before : Bool) (e : ℝ) : ℝ := Wd before e+C e
def Y (before : Bool) (b e : ℝ) : ℝ :=
  FrameDiagonalContactRoot.Y (C e) (D e) (L before b e)
def Yd (before : Bool) (b e : ℝ) : ℝ :=
  FrameDiagonalContactRoot.YD (C e) (D e) (L before b e) (-D e) (C e) (Ld before e)
def denominator (before : Bool) (b e : ℝ) : ℝ := C e+D e*slope (Y before b e)
def F (before : Bool) (b e : ℝ) : ℝ := angular before e-M b-H (Y before b e)
def Fd (before : Bool) (b e : ℝ) : ℝ :=
  1-(9/100)*Wd before e-Hd (Y before b e)*Yd before b e

theorem L_bounds {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    L before b e∈Icc (197/100:ℝ) (12/5) := by
  have hd := FrameMidHighAlignedContact.domain_bounds
    (FrameMidHighAlignedContact.middle_difference hb)
  have ht := strip_trig (side_subset he)
  have hCD := CD_bounds (side_subset he)
  have hsg := side_signs he
  cases before
  · have h1 : 1≤D e := hsg.2.2
    dsimp [L,W]
    constructor <;> linarith [hCD.2.2]
  · dsimp [L,W,C,D]
    constructor <;> linarith

theorem root_data {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    0<4*Q0-(L before b e)^2 ∧ 0<Y before b e ∧ Y before b e<4/5 ∧
      0<FrameDiagonalContactRoot.X (C e) (D e) (L before b e)+1 := by
  exact FrameDiagonalContactRoot.target_root_bounds
    (CD_bounds (side_subset he)).1 (CD_bounds (side_subset he)).2 (L_bounds hb he)

theorem Y_mem {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    Y before b e∈extended :=
  ⟨(root_data hb he).2.1.le,(root_data hb he).2.2.1.le⟩

theorem radial {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    FrameDiagonalContactRoot.X (C e) (D e) (L before b e)=A (Y before b e) :=
  FrameDiagonalContactRoot.X_eq_chart (unit e) (root_data hb he).1.le
    (root_data hb he).2.2.2.le

theorem contact {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    (A b-b)+D e*A (Y before b e)-C e*Y before b e=W before e := by
  have hh := FrameDiagonalContactRoot.contact (l := L before b e) (unit e)
  rw [radial hb he] at hh
  change D e*(A (Y before b e)+1)-C e*Y before b e=L before b e at hh
  dsimp [L] at hh
  linarith

theorem L_deriv (before : Bool) (b e : ℝ) : HasDerivAt (L before b) (Ld before e) e := by
  exact ((W_deriv before e).sub_const (A b-b)).fun_add (D_deriv e)

theorem Y_deriv {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    HasDerivAt (Y before b) (Yd before b e) e :=
  FrameDiagonalContactRoot.Y_deriv (C_deriv e) (D_deriv e) (L_deriv before b e)
    (root_data hb he).1

theorem denominator_lower {before : Bool} {b e : ℝ}
    (hb : b∈Icc b1 b2) (he : e∈side before) :
    (4899/5000:ℝ)≤denominator before b e := by
  have ht := CD_bounds (side_subset he)
  have hr := extended_slope (Y_mem hb he)
  have hp := mul_nonneg (by linarith [ht.2.1] : 0≤D e) hr.1
  dsimp [denominator]
  linarith [ht.1.1]

theorem speed_identity {before : Bool} {b e : ℝ}
    (hb : b∈Icc b1 b2) (he : e∈side before) :
    Yd before b e*denominator before b e=
      C e*A (Y before b e)+D e*Y before b e-Wd before e := by
  have hh := FrameDiagonalContactRoot.YD_contact (cp := -D e) (dp := C e)
    (lp := Ld before e) (unit e) (by ring) (root_data hb he).1
    (root_data hb he).2.2.2.ne'
  rw [radial hb he] at hh
  change Yd before b e*(C e+D e*(Y before b e/(A (Y before b e)+1)))=
    C e*(A (Y before b e)+1)- -D e*Y before b e-Ld before e at hh
  dsimp only [Ld] at hh
  dsimp [denominator,FrameDiagonalArc.slope]
  linarith

theorem before_speed {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side true) :
    (66/25:ℝ)<Yd true b e := by
  have hid := speed_identity hb he
  have ht := strip_trig (side_subset he)
  have hs := side_signs he
  have hr := extended_slope (Y_mem hb he)
  have hrad := (extended_radial (Y_mem hb he)).1
  have hC := (CD_bounds (side_subset he)).1.1
  have hD := (CD_bounds (side_subset he)).2.1
  have hden : 1≤denominator true b e := by
    have hp := mul_nonneg (show 0≤D e by linarith) hr.1
    dsimp [denominator]
    linarith [hs.2.1]
  have hden0 : 0<denominator true b e := by linarith
  have hcancel : Yd true b e*denominator true b e=
      (A (Y true b e)+1)*denominator true b e+2*Real.sin e := by
    have hp := (A_shift_pos (extended_subset (Y_mem hb he))).ne'
    have hr : slope (Y true b e)*(A (Y true b e)+1)=Y true b e := by
      dsimp [FrameDiagonalArc.slope]
      field_simp [hp]
    have hcd : D e-C e=2*Real.sin e := by dsimp [C,D]; ring
    rw [hid]
    dsimp [Wd,denominator]
    linear_combination -(D e)*hr+hcd
  have hmul := mul_lt_mul_of_pos_right hrad hden0
  apply lt_of_mul_lt_mul_right _ hden0.le
  linarith [ht.1]

theorem after_speed {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side false) :
    0<Yd false b e ∧ Yd false b e<(8080/4899:ℝ) := by
  have hid := speed_identity hb he
  have hs := side_signs he
  have ht := CD_bounds (side_subset he)
  have hy := root_data hb he
  have ha := extended_radial (Y_mem hb he)
  have hden := denominator_lower hb he
  have hden0 : 0<denominator false b e := by linarith
  have hnum0 : 0<C e*(A (Y false b e)-1)+D e*Y false b e := by
    have hp := mul_pos (show 0<C e by linarith [ht.1.1])
      (show 0<A (Y false b e)-1 by linarith [ha.1])
    have hq := mul_nonneg (show 0≤D e by linarith [ht.2.1]) hy.2.1.le
    linarith
  have hnumU : C e*(A (Y false b e)-1)+D e*Y false b e<(202/125:ℝ) := by
    have hp := mul_le_mul_of_nonneg_right hs.2.1
      (show 0≤A (Y false b e)-1 by linarith [ha.1])
    have hq := mul_le_mul ht.2.2 hy.2.2.1.le hy.2.1.le (by norm_num : (0:ℝ)≤51/50)
    nlinarith [ha.2,a0_precise.2]
  have hid' : Yd false b e*denominator false b e=
      C e*(A (Y false b e)-1)+D e*Y false b e := by
    dsimp [Wd] at hid
    linarith
  have hypos : 0<Yd false b e :=
    (mul_pos_iff_of_pos_right hden0).mp (by rw [hid']; exact hnum0)
  have hmul := mul_le_mul_of_nonneg_left hden hypos.le
  exact ⟨hypos,by nlinarith⟩

theorem F_deriv {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    HasDerivAt (F before b) (Fd before b e) e := by
  have hh := ((angular_deriv before e).sub_const (M b)).sub
    ((H_deriv_extended (Y_mem hb he)).comp e (Y_deriv hb he))
  convert hh using 1
  · funext y
    simp only [F,Pi.sub_apply,Function.comp_apply]
  · simp only [Fd]

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

theorem actual_target_le {before : Bool} {b B e : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (he : e∈side before)
    (hm : 0≤central false true (A b) b (A B) B (Real.pi/2+e)) : B≤Y before b e := by
  have hactual : W before e≤(A b-b)+D e*A B-C e*B := by
    dsimp [central,sign] at hm
    rw [(angle_trig e).1,(angle_trig e).2,← W_actual he] at hm
    dsimp [C,D]
    linarith
  have hc := contact hb he
  have ht := CD_bounds (side_subset he)
  by_contra! hbad
  have hA := A_antitone (extended_subset (Y_mem hb he)) (high_subset hB) hbad.le
  have hp := mul_le_mul_of_nonneg_left hA (show 0≤D e by linarith [ht.2.1])
  have hq := mul_lt_mul_of_pos_left hbad (show 0<C e by linarith [ht.1.1])
  nlinarith

theorem actual_lower {before : Bool} {b B e : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (he : e∈side before)
    (hm : 0≤central false true (A b) b (A B) B (Real.pi/2+e)) :
    (4463/5000:ℝ)<cost true false false true b B (Real.pi/2+e) := by
  have hy := actual_target_le hb hB he hm
  have hH := H_monotone_extended (high_extended hB) (Y_mem hb he) hy
  have hF := F_lower hb he
  rw [F,angular_actual he] at hF
  dsimp [cost,marker,sign]
  linarith

end SquaresInCircles.Eight.FrameMidHighTargetContact
