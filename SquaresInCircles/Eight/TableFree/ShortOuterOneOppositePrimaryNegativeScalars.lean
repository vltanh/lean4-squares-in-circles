module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryNegativeGeometry

/-!
# The six prescribed lower-half multipliers and scalar endpoints

Uncompiled transcription of sections 2--5 of the negative-primary note.
The six source radical upper bounds are the displayed fixed rationals.
They prove the displayed source supports directly by positive squaring.
Axial monotonicity and diagonal concavity hold on the whole feasible
interval, before any fixed endpoint value is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Negative
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def weight : Row→ℝ := ![93308/100000,11625/10000,100982/100000,108532/100000,110143/100000,112741/100000]
def normUpper : Row→ℝ := ![1880509701/1000000000,1386761738/1000000000,
  1332148407/1000000000,1176679496/1000000000,1452999491/1000000000,1241873719/1000000000]
def supportLower : Row→ℝ := ![-2397276/1000000,-1768154/1000000,-1696710/1000000,
  -1498695/1000000,-1850634/1000000,-1581731/1000000]
def S (r : Row) : ℝ := (weight r+q r-p r)/2-
  radius*Real.sqrt ((p r-weight r)^2+(q r)^2)
def X (r : Row) (x : ℝ) : ℝ := -P r+weight r*Real.sin x
def Y (r : Row) (x : ℝ) : ℝ := weight r*Real.cos x-t r
def axialValue (r : Row) (x : ℝ) : ℝ := Real.pi/2-x+c r+S r-P r*outerAxial+
  weight r/2+(weight r/2)*Real.cos x+weight r*(1/2+outerAxial)*Real.sin x
def axialD (r : Row) (x : ℝ) : ℝ :=
  -1-(weight r/2)*Real.sin x+weight r*(1/2+outerAxial)*Real.cos x
def diagonalValue (r : Row) (x : ℝ) : ℝ := Real.pi/2-x+c r+S r-(P r+t r)*outerDiagonal+
  weight r/2+weight r*(1/2+outerDiagonal)*(Real.sin x+Real.cos x)
def diagonalD (r : Row) (x : ℝ) : ℝ :=
  -1+weight r*(1/2+outerDiagonal)*(Real.cos x-Real.sin x)
def diagonalDD (r : Row) (x : ℝ) : ℝ :=
  -weight r*(1/2+outerDiagonal)*(Real.sin x+Real.cos x)

theorem weight_bounds (r : Row) : (23327/25000:ℝ)≤weight r ∧ weight r≤93/80 := by
  fin_cases r <;> norm_num [weight]
theorem weight_positive (r : Row) : 0<weight r := by linarith [(weight_bounds r).1]
theorem P_nonpositive (r : Row) (hr : r≠1) : P r≤0 := by
  fin_cases r <;> norm_num [P] at hr ⊢

theorem source_norm_upper (r : Row) : Real.sqrt ((p r-weight r)^2+(q r)^2)<normUpper r := by
  have hs := Real.sq_sqrt (show 0≤(p r-weight r)^2+(q r)^2 by positivity)
  have hp := Real.sqrt_nonneg ((p r-weight r)^2+(q r)^2)
  fin_cases r <;> norm_num [p,q,weight,normUpper] at hs ⊢ <;> nlinarith

theorem source_support_lower (r : Row) : supportLower r<S r := by
  have hr := ShortWord.MixedQuarter.Reference.radius_fine.2
  have hn := source_norm_upper r
  have hp := Real.sqrt_nonneg ((p r-weight r)^2+(q r)^2)
  have hprod := mul_lt_mul hr hn hp (by norm_num : (0:ℝ)<494697/250000)
  fin_cases r <;> norm_num [S,supportLower,weight,normUpper,p,q] at hprod ⊢ <;> linarith

theorem axial_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (axialValue r) (axialD r x) x := by
  have hh := (((((hasDerivAt_id x).const_sub (Real.pi/2)).add_const (c r)).add_const (S r)).
    sub_const (P r*outerAxial)).add_const (weight r/2)
  convert (hh.add ((Real.hasDerivAt_cos x).const_mul (weight r/2))).add
    ((Real.hasDerivAt_sin x).const_mul (weight r*(1/2+outerAxial))) using 1 <;>
      dsimp [axialValue,axialD] <;> ring

theorem axialD_positive (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) : (63/100:ℝ)<axialD r x := by
  have tr := small_trig hx
  have ha := ShortOuterZero.fine_axial_bounds.1
  have hp := mul_lt_mul (show (1914575671/1000000000:ℝ)<1/2+outerAxial by linarith)
    tr.1 (by norm_num : (0:ℝ)≤6091/6250) (by linarith [outer_endpoint_bounds.1])
  have hbracket : (1/2+outerAxial)*Real.cos x-Real.sin x/2>
      (1914575671/1000000000:ℝ)*(6091/6250)-(22409/100000)/2 := by linarith [tr.2.2]
  have hmul := mul_le_mul_of_nonneg_right (weight_bounds r).1
    (show 0≤(1/2+outerAxial)*Real.cos x-Real.sin x/2 by linarith)
  have hlower := mul_lt_mul_of_pos_left hbracket (by norm_num : (0:ℝ)<23327/25000)
  dsimp [axialD]
  nlinarith

theorem axial_monotone (r : Row) : MonotoneOn (axialValue r) (Icc 0 cap) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (axial_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => axial_hasDerivAt r x)
    (fun x hx => by linarith [axialD_positive r (Ioo_subset_Icc_self hx)])

theorem diagonal_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (diagonalValue r) (diagonalD r x) x := by
  have hh := (((((hasDerivAt_id x).const_sub (Real.pi/2)).add_const (c r)).add_const (S r)).
    sub_const ((P r+t r)*outerDiagonal)).add_const (weight r/2)
  convert hh.add (((Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)).
    const_mul (weight r*(1/2+outerDiagonal))) using 1 <;> dsimp [diagonalValue,diagonalD] <;> ring
theorem diagonalD_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (diagonalD r) (diagonalDD r x) x := by
  convert ((((Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x)).
    const_mul (weight r*(1/2+outerDiagonal))).const_add (-1)) using 1 <;>
      dsimp [diagonalD,diagonalDD] <;> ring
theorem diagonal_concave (r : Row) : ConcaveOn ℝ (Icc 0 cap) (diagonalValue r) := by
  apply concave_of_deriv2 (fun x _ => diagonal_hasDerivAt r x)
    (fun x _ => diagonalD_hasDerivAt r x)
  intro x hx
  have tr := small_trig hx
  dsimp [diagonalDD]
  have hh := mul_nonneg (mul_nonneg (weight_positive r).le
    (show 0≤1/2+outerDiagonal by linarith [outer_endpoint_bounds.2.2.1]))
    (show 0≤Real.sin x+Real.cos x by linarith [tr.1,tr.2.1])
  nlinarith

theorem axial_initial (r : Row) : threshold r<axialValue r 0 := by
  have hS := source_support_lower r
  have ha := ShortOuterZero.fine_axial_bounds
  have hpi : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  fin_cases r <;> norm_num [threshold,axialValue,c,p,q,P,t,weight,supportLower] at hS ⊢ <;> linarith

theorem diagonal_initial (r : Row) (hr : r≠1) : threshold r<diagonalValue r 0 := by
  have hS := source_support_lower r
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hpi : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  fin_cases r <;> norm_num [threshold,diagonalValue,c,p,q,P,t,weight,supportLower] at hr hS ⊢ <;> linarith

def diagonalCapBox (r : Row) : Interval (diagonalValue r cap-S r) := by
  convert (((((halfPi.sub (Interval.point cap)).add (Interval.point (c r))).sub
    ((Interval.point (P r+t r)).mul diagonal)).add (Interval.point (weight r/2))).
      add (((Interval.point (weight r)).mul ((Interval.point (1/2)).add diagonal)).
        mul ((sine (by norm_num [cap] : 0≤cap)).add (cosine (by norm_num [cap] : 0≤cap))))) using 1
  dsimp [diagonalValue]
  ring

theorem diagonal_final (r : Row) (hr : r≠1) : (9309/10000:ℝ)<diagonalValue r cap := by
  have hh : (9309/10000:ℝ)<supportLower r+(diagonalCapBox r).lo := by
    fin_cases r <;> norm_num at hr <;> dsimp [diagonalCapBox,cap,c,P,t,weight,supportLower] <;> mixed_fixed
  have hb := (diagonalCapBox r).mem.1
  linarith [source_support_lower r]

theorem axial_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) : threshold r<axialValue r x :=
  (axial_initial r).trans_le ((axial_monotone r) (by norm_num [cap]) hx hx.1)
theorem diagonal_lower (r : Row) (hr : r≠1) {x : ℝ} (hx : x∈Icc 0 cap) : threshold r<diagonalValue r x := by
  apply concave_gt_of_endpoints (diagonal_concave r) hx (diagonal_initial r hr)
  have hh := diagonal_final r hr
  dsimp [threshold]
  split_ifs <;> linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Negative
