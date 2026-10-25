module

public import SquaresInCircles.Eight.TableFree.ShortWordZero

/-!
# Whole-angle scalar bounds for the eight unit-support owners

Uncompiled transcription of equations (7)--(8), (12)--(16) and
(21)--(29) of `HAND_SHORT_WORD_SAME_SIGN_UNIT_SUPPORTS_WITHOUT_TABLES.md`.
The four tuples are literal role-label differences. The only endpoint
evaluations occur at alignment and the common final angle 7/10.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Unit
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

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Unit
