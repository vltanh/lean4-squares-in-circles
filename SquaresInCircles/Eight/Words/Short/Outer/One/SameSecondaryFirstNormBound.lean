module

public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryFirstNorm

/-!
# Eight squares: the two fixed support comparisons for the first secondary row

The exact norm is substituted only at 0.7 and 0.03. The whole-interval
curvature proof then propagates positivity of the derivative and the
lower bound from 0.03 to every later angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstNorm
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.SameZero.PJ.Reference (sinBox cosBox)
open SecondWord.OppositeThree.ReferenceAlgebra (rootThree rootStep)

def energyBox (x : ℝ) (hx : 0≤x) : Interval (CircularNorm.energy normA normB normC x) :=
  (((Interval.point normA).add ((Interval.point normB).mul (cosBox x hx))).add
    ((Interval.point normC).mul (sinBox x hx)))
def normBox (x : ℝ) (hx : 0≤x) (hr : 0≤(energyBox x hx).lo) : Interval (N x) :=
  rootThree (energyBox x hx) (6/5) (by norm_num) hr
def radiusBox : Interval radius := rootThree (Interval.point Q0) 2 (by norm_num)
  (by norm_num [Interval.point,Q0])
def slopeBox (x : ℝ) (hx : 0≤x) : Interval (CircularNorm.slope normB normC x) :=
  (((Interval.point (-normB)).mul (sinBox x hx))).add
    ((Interval.point normC).mul (cosBox x hx))
def firstBox (x : ℝ) (hx : 0≤x) (hr : 0≤(energyBox x hx).lo)
    (hn : 0<(normBox x hx hr).lo) : Interval (first x) := by
  let denominator := (Interval.point 2).mul (normBox x hx hr)
  have hden : 0<denominator.lo := Interval.mul_lo_pos (by norm_num [Interval.point]) hn
  exact (((Interval.point (-1)).sub ((Interval.point weight).mul (sinBox x hx))).sub
    (radiusBox.mul ((slopeBox x hx).div denominator hden)))
def valueBox (x : ℝ) (hx : 0≤x) (hr : 0≤(energyBox x hx).lo) : Interval (value x) := by
  let V₀ := ((RoleFour.piBox.mul (Interval.point (1/2))).sub (Interval.point x)).add
    (Interval.point (c 0))
  let V₁ := (V₀.sub ((Interval.point (P 0)).mul RoleFour.aBox)).add
    (Interval.point ((weight-p 0+q 0)/2))
  let V₂ := V₁.add ((Interval.point weight).mul (cosBox x hx))
  convert V₂.sub (radiusBox.mul (normBox x hx hr)) using 1 <;> dsimp [value] <;> ring

local macro "first_secondary_norm_reference" : tactic => `(tactic|
  norm_num [energyBox,normBox,radiusBox,slopeBox,firstBox,valueBox,normA,normB,normC,
    weight,RoleFour.piBox,RoleFour.aBox,SecondWord.SameZero.PJ.Reference.sinBox,
    SecondWord.SameZero.PJ.Reference.cosBox,rootThree,rootStep,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,Interval.mul,
    Interval.square,Interval.div,Interval.inv,HighOrderTaylor.S17,HighOrderTaylor.S15,
    HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,HighOrderTaylor.C16,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,Q0,c,p,q,P,t])

lemma final_first : (3/50:ℝ)<first (7/10) := by
  have hr : 0≤(energyBox (7/10) (by norm_num)).lo := by first_secondary_norm_reference
  have hn : 0<(normBox (7/10) (by norm_num) hr).lo := by first_secondary_norm_reference
  have hlo : (3/50:ℝ)<(firstBox (7/10) (by norm_num) hr hn).lo := by
    first_secondary_norm_reference
  exact hlo.trans_le (firstBox (7/10) (by norm_num) hr hn).mem.1

private lemma r87_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl

private lemma r87_value_eq (x : ℝ) : value x=Real.pi*(1/2)-x+c 0-P 0*outerAxial+
    (weight-p 0+q 0)/2+weight*Real.cos x-radius*N x := by
  simp only [value]; ring
private lemma r87_valueBox_lo (x : ℝ) (hx : 0≤x) (hr : 0≤(energyBox x hx).lo) :
    (valueBox x hx hr).lo=(((((((RoleFour.piBox.mul (Interval.point (1/2))).sub
      (Interval.point x)).add (Interval.point (c 0))).sub
        ((Interval.point (P 0)).mul RoleFour.aBox)).add
          (Interval.point ((weight-p 0+q 0)/2))).add
            ((Interval.point weight).mul (cosBox x hx))).sub
              (radiusBox.mul (normBox x hx hr))).lo := by
  dsimp only [valueBox]
  exact r87_mpr_lo (r87_value_eq x) _ _

lemma initial_reference : (89929/100000:ℝ)<value (3/100) := by
  have hr : 0≤(energyBox (3/100) (by norm_num)).lo := by first_secondary_norm_reference
  have hlo : (89929/100000:ℝ)<(valueBox (3/100) (by norm_num) hr).lo := by
    rw [r87_valueBox_lo]
    first_secondary_norm_reference
  exact hlo.trans_le (valueBox (3/100) (by norm_num) hr).mem.1

lemma first_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : (3/50:ℝ)<first x :=
  final_first.trans_le (first_antitone hx (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx.2)

lemma value_monotone : MonotoneOn value (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
  (fun x hx => (value_hasDerivAt hx).continuousAt.continuousWithinAt)
  (fun x hx => value_hasDerivAt (Ioo_subset_Icc_self hx))
  (fun x hx => by linarith [first_positive (Ioo_subset_Icc_self hx)])

theorem original_later {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc (3/100:ℝ) (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x) :
    (89929/100000:ℝ)<Real.pi/2-x+c 0-P 0*a+t 0*b+p 0*A-q 0*B := by
  have hv := value_monotone (show (3/100:ℝ)∈Icc 0 (7/10) by norm_num)
    (show x∈Icc 0 (7/10) from ⟨by linarith [hx.1],hx.2⟩) hx.1
  exact initial_reference.trans_le (hv.trans (original_support hs ht hm))

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstNorm
