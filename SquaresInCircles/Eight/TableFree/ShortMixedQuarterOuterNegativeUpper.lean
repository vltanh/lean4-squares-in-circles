module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterNegativeData
public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterReferences

/-!
# All six negative-core primary upper halves

Uncompiled transcription of section 6 of the negative-core note.
The constant multiplier g leaves the core coefficients with their
original signs: the primary term is nonpositive and the transverse
term nonnegative. The axial core bound therefore applies to either
piece, including its join. The resulting support increases on the
whole closed upper angle half from a fixed value greater than .905.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.Upper
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open MixedQuarter.Reference

def S (r : Row) : ℝ := (ocG r-ocP r+ocQ r)/2-
  CommonQuarter.radius*Real.sqrt ((ocG r-ocP r)^2+(ocQ r)^2)
def F (r : Row) (x : ℝ) : ℝ := Real.pi/2+x+ocC r+S r+
  ocG r/2+(ocG r/2)*Real.cos x-(ocG r/12)*Real.sin x
def Fd (r : Row) (x : ℝ) : ℝ := 1-(ocG r/2)*Real.sin x-(ocG r/12)*Real.cos x

def radiusBox : Interval CommonQuarter.radius :=
  rootSix (Interval.point Q0) 2 (by norm_num) (by norm_num [Interval.point,Q0])
def normBox (r : Row) : Interval (Real.sqrt ((ocG r-ocP r)^2+(ocQ r)^2)) :=
  rootSix (Interval.point ((ocG r-ocP r)^2+(ocQ r)^2)) 2 (by norm_num)
    (by dsimp [Interval.point]; positivity)
def sourceBox (r : Row) : Interval (S r) :=
  (Interval.point ((ocG r-ocP r+ocQ r)/2)).sub (radiusBox.mul (normBox r))
def initialBox (r : Row) : Interval (F r 0) := by
  convert ((halfPi.add (Interval.point (ocC r))).add (sourceBox r)).add (Interval.point (ocG r)) using 1
  dsimp [F]
  simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,add_zero]
  ring

private lemma r83_mpr_lo {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).lo=S.lo := by subst e; rfl
private lemma r83_initial_eq (r : Row) : F r 0=Real.pi/2+ocC r+S r+ocG r := by
  dsimp [F]
  simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,add_zero]
  ring
private lemma r83_initialBox_lo (r : Row) :
    (initialBox r).lo=(((halfPi.add (Interval.point (ocC r))).add (sourceBox r)).add
      (Interval.point (ocG r))).lo :=
  r83_mpr_lo (r83_initial_eq r) _ _

theorem initial (r : Row) (hr : Remaining r) : (181/200:ℝ)<F r 0 := by
  have hh : (181/200:ℝ)<(initialBox r).lo := by
    rw [r83_initialBox_lo]
    rcases (remaining_iff r).1 hr with rfl|rfl|rfl|rfl|rfl|rfl <;>
      dsimp [sourceBox,normBox,radiusBox] <;> mixed_fixed
  exact hh.trans_le (initialBox r).mem.1

theorem F_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (F r) (Fd r x) x := by
  have hh := ((((((hasDerivAt_id' x).const_add (Real.pi/2)).add_const (ocC r)).add_const
    (S r)).add_const (ocG r/2)).fun_add ((Real.hasDerivAt_cos x).const_mul (ocG r/2))).fun_sub
      ((Real.hasDerivAt_sin x).const_mul (ocG r/12))
  exact hh.congr_deriv (by simp only [Fd]; ring)

theorem Fd_positive (r : Row) (hr : Remaining r) {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<Fd r x := by
  have hg := coefficients r hr
  have tr := positive_trig hx
  have hcos : 0≤Real.cos x := by linarith [tr.1]
  have hs := mul_le_mul hg.2.2.1.le tr.2.2.2.1.le tr.2.2.1
    (by norm_num : (0:ℝ)≤1139/1000)
  have hc := mul_le_mul hg.2.2.1.le (Real.cos_le_one x) hcos
    (by norm_num : (0:ℝ)≤1139/1000)
  dsimp [Fd]
  nlinarith

theorem F_monotone (r : Row) (hr : Remaining r) : MonotoneOn (F r) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (F_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => F_hasDerivAt r x)
    (fun x hx => (Fd_positive r hr (Ioo_subset_Icc_self hx)).le)

theorem original_ge_F (r : Row) (hr : Remaining r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle true x)) :
    F r x≤outerCoreCost r a b A B (angle true x) := by
  have hg := (coefficients r hr).2.1
  have tr := positive_trig hx
  obtain ⟨hA0,hA,hB0,hBA,hB⟩ := CoreAngleEndpoint.state_bounds ht
  have hsep := (primary_separator r hr a b A B (angle true x)).1 hm
  rw [angle_width true hx,angle_cos,angle_sin] at hsep
  dsimp [direction] at hsep
  have hp := mul_le_mul_of_nonneg_left hsep hg.le
  have hcircle := outer_circle_lower (X:=ocP r-ocG r) (Y:=-(ocQ r)) hs
  have hnorm : (ocP r-ocG r)^2+(-(ocQ r))^2=(ocG r-ocP r)^2+(ocQ r)^2 := by ring
  rw [hnorm] at hcircle
  have hAcost := mul_le_mul_of_nonneg_right hA (mul_nonneg hg.le tr.2.2.1)
  have hBcost := mul_nonneg (mul_nonneg hg.le (sub_nonneg.mpr (Real.cos_le_one x))) hB0
  rw [primary_cost r hr]
  dsimp [F,S,angle,direction]
  nlinarith only [hp,hcircle,hAcost,hBcost]

theorem original (r : Row) (hr : Remaining r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle true x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle true x) := by
  have hmF := (F_monotone r hr) (by norm_num : (0:ℝ)∈Icc 0 (7/10)) hx hx.1
  have hv : (449/500:ℝ)<F r x := by linarith [initial r hr,hmF]
  exact hv.trans_le (original_ge_F r hr hs ht hx hm)

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.Upper
