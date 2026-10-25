module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Words.Common.QuarterState
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.PositivePrimary

/-!
# Eight squares: whole-angle scalar bounds for the eight unit-support owners

The four tuples are literal role-label differences. The only endpoint
evaluations occur at alignment and the common final angle 7/10.
-/

section
/-!
## The outer-circle chart shared by the word proofs

This module contains only the analytic circle chart `arc`, the ratio `ratio`, and their exact
derivatives. The chart covers both the transverse and the primary coordinate intervals. States
are recovered from their original circle equation, with the diagonal and axial endpoints
(`arc_diagonal`, `arc_zero`, `arc_axial`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortOuterOne.SameContact

open CommonQuarter CorePairGeometry Arithmetic

def arc (b : ℝ) : ℝ := Real.sqrt (Q0-(b+1/2)^2)-1/2
def ratio (b : ℝ) : ℝ := (b+1/2)/(arc b+1/2)
def ratioD (b : ℝ) : ℝ := Q0/(arc b+1/2)^3
def ratioDD (b : ℝ) : ℝ := 3*Q0*(b+1/2)/(arc b+1/2)^5

lemma diagonal_le_axial : outerDiagonal≤outerAxial := by
  linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]

lemma outer_domain {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    b∈Icc 0 outerAxial := ⟨hb.1,hb.2.trans diagonal_le_axial⟩

lemma radicand_pos {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    0<Q0-(b+1/2)^2 := by
  have hp := pow_le_pow_left₀ (show 0≤b+1/2 by linarith [hb.1])
    (show b+1/2≤outerAxial+1/2 by linarith [hb.2]) 2
  nlinarith [axial_circle]

lemma shifted_positive {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    0<arc b+1/2 := by
  simpa [arc] using Real.sqrt_pos.mpr (radicand_pos hb)

lemma arc_circle {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    (arc b+1/2)^2+(b+1/2)^2=Q0 := by
  have hh := Real.sq_sqrt (radicand_pos hb).le
  dsimp [arc]
  nlinarith

lemma arc_nonneg {b : ℝ} (hb : b∈Icc 0 outerAxial) : 0≤arc b := by
  have hp := pow_le_pow_left₀ (show 0≤b+1/2 by linarith [hb.1])
    (show b+1/2≤outerAxial+1/2 by linarith [hb.2]) 2
  have hc := arc_circle hb
  have hs := shifted_positive hb
  nlinarith [axial_circle]

lemma arc_zero : arc 0=outerAxial := by
  norm_num [arc,outerAxial]

lemma arc_diagonal : arc outerDiagonal=outerDiagonal := by
  have hp : 0≤outerDiagonal+1/2 := by linarith [outer_endpoint_bounds.2.2.1]
  have he : Q0-(outerDiagonal+1/2)^2=(outerDiagonal+1/2)^2 := by
    nlinarith [diagonal_circle]
  rw [arc,he,Real.sqrt_sq hp]
  ring

lemma arc_axial : arc outerAxial=0 := by
  have he : Q0-(outerAxial+1/2)^2=(1/2:ℝ)^2 := by
    nlinarith [axial_circle]
  rw [arc,he,Real.sqrt_sq (by norm_num : (0:ℝ)≤1/2)]
  ring

lemma arc_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    HasDerivAt arc (-ratio b) b := by
  have hr := radicand_pos hb
  have hin : HasDerivAt (fun x : ℝ => Q0-(x+1/2)^2) (-(2*(b+1/2))) b := by
    convert (((hasDerivAt_id' b).add_const (1/2)).fun_pow 2).const_sub Q0 using 1
    norm_num
  have hd : HasDerivAt arc (-(2*(b+1/2))/(2*Real.sqrt (Q0-(b+1/2)^2))) b :=
    (hin.sqrt hr.ne').sub_const (1/2)
  have ha : arc b+1/2=Real.sqrt (Q0-(b+1/2)^2) := by
    rw [arc]
    ring
  convert hd using 1
  rw [ratio,ha]
  ring

lemma ratio_pos {b : ℝ} (hb : b∈Icc 0 outerAxial) : 0<ratio b := by
  exact div_pos (by linarith [hb.1]) (shifted_positive hb)

lemma ratioD_pos {b : ℝ} (hb : b∈Icc 0 outerAxial) : 0<ratioD b := by
  exact div_pos (by norm_num [Q0]) (pow_pos (shifted_positive hb) 3)

lemma ratio_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    HasDerivAt ratio (ratioD b) b := by
  have hp := shifted_positive hb
  have hne := hp.ne'
  have hd := ((hasDerivAt_id' b).add_const (1/2)).div
    ((arc_hasDerivAt hb).add_const (1/2)) hne
  convert hd using 1
  · rfl
  · rw [ratioD,← arc_circle hb,ratio]
    field_simp
    ring

lemma ratioD_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    HasDerivAt ratioD (ratioDD b) b := by
  have hp := shifted_positive hb
  have hd := (hasDerivAt_const b Q0).div
    (((arc_hasDerivAt hb).add_const (1/2)).pow 3) (pow_ne_zero _ hp.ne')
  convert hd using 1
  · rfl
  · dsimp [ratioD,ratioDD,ratio]
    field_simp [hp.ne']
    ring

lemma arc_antitone : AntitoneOn arc (Icc 0 outerAxial) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hb => (arc_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun _ hb => arc_hasDerivAt (Ioo_subset_Icc_self hb))
    (fun _ hb => neg_nonpos.mpr (ratio_pos (Ioo_subset_Icc_self hb)).le)

lemma ratio_monotone : MonotoneOn ratio (Icc 0 outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hb => (ratio_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun _ hb => ratio_hasDerivAt (Ioo_subset_Icc_self hb))
    (fun _ hb => (ratioD_pos (Ioo_subset_Icc_self hb)).le)

lemma actual_arc {a b : ℝ} (hs : OuterState a b) :
    arc b=a ∧ arc a=b := by
  have ha : 0≤a+1/2 := by linarith [hs.1,hs.2.1]
  have hb : 0≤b+1/2 := by linarith [hs.1]
  have he : Q0-(b+1/2)^2=(a+1/2)^2 := by linarith [hs.2.2]
  have he' : Q0-(a+1/2)^2=(b+1/2)^2 := by linarith [hs.2.2]
  constructor
  · rw [arc,he,Real.sqrt_sq ha]
    ring
  · rw [arc,he',Real.sqrt_sq hb]
    ring

lemma arc_state {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : OuterState (arc b) b := by
  have hd : outerDiagonal∈Icc 0 outerAxial :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],diagonal_le_axial⟩
  have hm := arc_antitone (outer_domain hb) hd hb.2
  rw [arc_diagonal] at hm
  exact ⟨hb.1,hb.2.trans hm,arc_circle (outer_domain hb)⟩

lemma primary_state {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    OuterState a (arc a) := by
  have had : a∈Icc 0 outerAxial :=
    ⟨by linarith [ha.1,outer_endpoint_bounds.2.2.1],ha.2⟩
  have hd : outerDiagonal∈Icc 0 outerAxial :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],diagonal_le_axial⟩
  have hm := arc_antitone hd had ha.1
  rw [arc_diagonal] at hm
  refine ⟨arc_nonneg had,hm.trans ha.1,?_⟩
  nlinarith [arc_circle had]

lemma primary_secondary_mem {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    arc a∈Icc 0 outerDiagonal :=
  ⟨(primary_state ha).1,(CommonQuarter.outer_bounds (primary_state ha)).2.2.2.1⟩

end SquaresInCircles.Eight.ShortOuterOne.SameContact
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Unit
open CommonQuarter CorePairGeometry Arithmetic

abbrev Row := Fin 4
def c : Row→ℝ := ![-53489/100000,-53062/100000,3846/100000,-20704/100000]
def vp : Row→ℝ := ![9133/100000,19335/100000,0,0]
def vq : Row→ℝ := ![88074/100000,76744/100000,86884/100000,94766/100000]
def vP : Row→ℝ := ![-33147/100000,-20967/100000,0,-21826/100000]
def vt : Row→ℝ := ![11336/10000,83048/100000,71553/100000,83472/100000]
def up (r : Row) : ℝ := -vP r
def uq (r : Row) : ℝ := vt r
def uP (r : Row) : ℝ := -vp r
def ut (r : Row) : ℝ := vq r
def direction (high : Bool) : ℝ := if high then 1 else -1
def angle (high : Bool) (x : ℝ) : ℝ := Real.pi/2+direction high*x

def V (r : Row) (high : Bool) (x : ℝ) : ℝ :=
  angle high x+c r+(vp r-vP r)*outerAxial+1/2+
    (1/2-outerAxial)*Real.cos x+Real.sin x/2
def VD (high : Bool) (x : ℝ) : ℝ :=
  direction high+(outerAxial-1/2)*Real.sin x+Real.cos x/2
def VDD (x : ℝ) : ℝ := (outerAxial-1/2)*Real.cos x-Real.sin x/2

def axial (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2-x+c r+(up r-1-uP r)*outerAxial+1/2+
    Real.cos x/2+(1/2+outerAxial)*Real.sin x
def axialD (x : ℝ) : ℝ := -1-Real.sin x/2+(1/2+outerAxial)*Real.cos x
def diagonal (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2-x+c r+(up r-1)*outerAxial-(uP r+ut r)*outerDiagonal+1/2+
    (1/2+outerDiagonal)*(Real.sin x+Real.cos x)
def diagonalD (x : ℝ) : ℝ := -1+(1/2+outerDiagonal)*(Real.cos x-Real.sin x)
def diagonalDD (x : ℝ) : ℝ := -(1/2+outerDiagonal)*(Real.sin x+Real.cos x)
def positiveFloor (r : Row) : ℝ :=
  Real.pi/2+c r+(up r-1)*outerAxial+441/500-(uP r+ut r-191/250)*outerDiagonal

lemma coefficient_bounds (r : Row) :
    0≤vp r ∧ vp r≤1/5 ∧ vq r<1 ∧ -(1/3:ℝ)<vP r ∧ vP r≤0 ∧
      (7/10:ℝ)<vt r ∧ 0≤up r ∧ up r<1 ∧ 0<uq r ∧ uP r≤0 ∧
        (191/250:ℝ)<ut r := by
  fin_cases r <;> norm_num [vp,vq,vP,vt,up,uq,uP,ut]

lemma V_hasDerivAt (r : Row) (high : Bool) (x : ℝ) :
    HasDerivAt (V r high) (VD high x) x := by
  have h := ((((((hasDerivAt_id x).const_mul (direction high)).const_add (Real.pi/2)).add_const
    (c r+(vp r-vP r)*outerAxial+1/2)).add
      ((Real.hasDerivAt_cos x).const_mul (1/2-outerAxial))).add
        ((Real.hasDerivAt_sin x).div_const 2))
  convert h using 1
  · funext y; simp only [V,angle,Pi.add_apply,id_eq]; ring
  · simp only [VD]; ring

lemma VD_hasDerivAt (high : Bool) (x : ℝ) : HasDerivAt (VD high) (VDD x) x := by
  have h := ((((Real.hasDerivAt_sin x).const_mul (outerAxial-1/2)).const_add
    (direction high)).add ((Real.hasDerivAt_cos x).div_const 2))
  convert h using 1
  · funext y; simp only [VD,Pi.add_apply]
  · simp only [VDD]; ring

lemma VDD_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<VDD x := by
  have ht := positive_trig hx
  have hp := mul_le_mul (show (914575671/1000000000:ℝ)≤outerAxial-1/2 by
      linarith [ShortOuterZero.fine_axial_bounds.1])
    (show (191/250:ℝ)≤Real.cos x by linarith [ht.1]) (by norm_num)
    (by linarith [outer_endpoint_bounds.1] : 0≤outerAxial-1/2)
  dsimp [VDD]
  nlinarith [ht.2.2.2.1]

lemma VD_low_final : VD false (7/10)<0 := by
  have ht := cap_trig
  have hp := mul_le_mul
    (show outerAxial-1/2≤(914575672/1000000000:ℝ) by linarith [ShortOuterZero.fine_axial_bounds.2])
    ht.2.1.le (by linarith [ht.1] : 0≤Real.sin (7/10)) (by norm_num)
  dsimp [VD,direction]
  nlinarith [ht.2.2.2]

lemma V_high_initial (r : Row) : (597/500:ℝ)<V r true 0 := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hp := pi_hand_enclosure.1
  fin_cases r <;> norm_num [V,angle,direction,c,vp,vP] <;> linarith

lemma V_low_final (r : Row) : (1031/1000:ℝ)<V r false (7/10) := by
  have ha := ShortOuterZero.fine_axial_bounds
  have ht := cap_trig
  have hp := pi_hand_enclosure.1
  have hnegative := mul_le_mul
    (show outerAxial-1/2≤(914575672/1000000000:ℝ) by linarith [ha.2])
    ht.2.2.2.le (by linarith [ht.2.2.1] : 0≤Real.cos (7/10)) (by norm_num)
  have hpositive := mul_le_mul_of_nonneg_left ha.1.le
    (show 0≤vp r-vP r by fin_cases r <;> norm_num [vp,vP])
  fin_cases r <;> norm_num [V,angle,direction,c,vp,vP] at * <;> nlinarith

theorem V_lower (r : Row) (high : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (1031/1000:ℝ)<V r high x := by
  cases high with
  | true =>
      have hm : MonotoneOn (V r true) (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
        (fun y _ => (V_hasDerivAt r true y).continuousAt.continuousWithinAt)
        (fun y _ => V_hasDerivAt r true y)
        (fun y hy => by
          have ht := positive_trig (Ioo_subset_Icc_self hy)
          have hp := mul_nonneg (show 0≤outerAxial-1/2 by linarith [outer_endpoint_bounds.1]) ht.2.2.1
          dsimp [VD,direction]
          linarith [ht.1])
      have hh := hm (by norm_num) hx hx.1
      linarith [V_high_initial r]
  | false =>
      have hdm : MonotoneOn (VD false) (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
        (fun y _ => (VD_hasDerivAt false y).continuousAt.continuousWithinAt)
        (fun y _ => VD_hasDerivAt false y)
        (fun y hy => (VDD_positive (Ioo_subset_Icc_self hy)).le)
      have hm : AntitoneOn (V r false) (Icc 0 (7/10)) := antiOn_of_hasDeriv_nonpos
        (fun y _ => (V_hasDerivAt r false y).continuousAt.continuousWithinAt)
        (fun y _ => V_hasDerivAt r false y)
        (fun y hy => (hdm (Ioo_subset_Icc_self hy) (by norm_num) hy.2.le).trans VD_low_final.le)
      exact (V_low_final r).trans_le (hm hx (by norm_num) hx.2)

lemma axial_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (axial r) (axialD x) x := by
  have h := (((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+c r+(up r-1-uP r)*outerAxial+1/2)).add
      ((Real.hasDerivAt_cos x).div_const 2)).add
        ((Real.hasDerivAt_sin x).const_mul (1/2+outerAxial)))
  convert h using 1
  · funext y; simp only [axial,Pi.add_apply,Pi.neg_apply,id_eq]; ring
  · simp only [axialD]; ring

lemma diagonal_hasDerivAt (r : Row) (x : ℝ) :
    HasDerivAt (diagonal r) (diagonalD x) x := by
  have h := (((hasDerivAt_id x).neg).const_add
    (Real.pi/2+c r+(up r-1)*outerAxial-(uP r+ut r)*outerDiagonal+1/2)).add
      (((Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)).const_mul
        (1/2+outerDiagonal))
  convert h using 1
  · funext y; simp only [diagonal,Pi.add_apply,Pi.neg_apply,id_eq]; ring
  · simp only [diagonalD]; ring

lemma diagonalD_hasDerivAt (x : ℝ) : HasDerivAt diagonalD (diagonalDD x) x := by
  have h := (((Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x)).const_mul
    (1/2+outerDiagonal)).const_add (-1)
  convert h using 1
  · funext y; simp only [diagonalD,Pi.sub_apply]
  · simp only [diagonalDD]; ring

lemma axial_initial (r : Row) : (597/500:ℝ)<axial r 0 := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hp := pi_hand_enclosure.1
  fin_cases r <;> norm_num [axial,c,up,uP,vp,vP] <;> linarith

lemma diagonal_initial (r : Row) : (1279/1000:ℝ)<diagonal r 0 := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hp := pi_hand_enclosure.1
  fin_cases r <;> norm_num [diagonal,c,up,uP,ut,vp,vP,vq] <;> linarith

lemma diagonal_final (r : Row) : (1151/1000:ℝ)<diagonal r (7/10) := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hp := pi_hand_enclosure.1
  have ht := cap_trig
  have hprod := mul_le_mul
    (show (1399214/1000000:ℝ)≤1/2+outerDiagonal by linarith [hd.1])
    (show (3221/5000+19121/25000:ℝ)≤Real.sin (7/10)+Real.cos (7/10) by linarith [ht.1,ht.2.2.1])
    (by norm_num) (by linarith [outer_endpoint_bounds.2.2.1] : 0≤1/2+outerDiagonal)
  unfold diagonal
  generalize (1/2+outerDiagonal)*(Real.sin (7/10)+Real.cos (7/10)) = P at hprod ⊢
  fin_cases r <;> norm_num [c,up,uP,ut,vp,vP,vq] at * <;> linarith

lemma axial_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (597/500:ℝ)<axial r x := by
  have hderiv {y : ℝ} (hy : y∈Icc 0 (7/10)) : 0≤axialD y := by
    have ht := positive_trig hy
    have hp := mul_le_mul
      (show (1914575671/1000000000:ℝ)≤1/2+outerAxial by linarith [ShortOuterZero.fine_axial_bounds.1])
      (show (191/250:ℝ)≤Real.cos y by linarith [ht.1]) (by norm_num)
      (by linarith [outer_endpoint_bounds.1] : 0≤1/2+outerAxial)
    dsimp [axialD]
    nlinarith [ht.2.2.2.1]
  have hm : MonotoneOn (axial r) (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
    (fun y _ => (axial_hasDerivAt r y).continuousAt.continuousWithinAt)
    (fun y _ => axial_hasDerivAt r y) (fun y hy => hderiv (Ioo_subset_Icc_self hy))
  exact (axial_initial r).trans_le (hm (by norm_num) hx hx.1)

lemma diagonal_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (1151/1000:ℝ)<diagonal r x := by
  have hc : ConcaveOn ℝ (Icc 0 (7/10)) (diagonal r) := concave_of_deriv2
    (fun y _ => diagonal_hasDerivAt r y) (fun y _ => diagonalD_hasDerivAt y)
    (fun y hy => by
      have ht := positive_trig hy
      exact mul_nonpos_of_nonpos_of_nonneg
        (by linarith [outer_endpoint_bounds.2.2.1] : -(1/2+outerDiagonal)≤0)
        (by linarith [ht.2.2.2.2.2]))
  exact concave_gt_of_endpoints hc hx (by linarith [diagonal_initial r]) (diagonal_final r)

lemma positive_floor (r : Row) : (949/1000:ℝ)<positiveFloor r := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hp := pi_hand_enclosure.1
  fin_cases r <;> norm_num [positiveFloor,c,up,uP,ut,vp,vP,vq] <;> linarith

end SquaresInCircles.Eight.ShortOuterOne.Unit
end
end
end
