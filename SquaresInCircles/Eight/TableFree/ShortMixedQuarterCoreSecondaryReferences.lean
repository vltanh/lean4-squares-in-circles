module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterCoreSecondaryNorm

/-!
# Named endpoints of the positive-target secondary supports

Uncompiled source. Concavity has already been proved on both whole
halves. The only substitutions are alignment, the physical cap, and
the original negative-source feasibility cap phi=1.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.CoreSecondaryPositive
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives Reference

def energyBox (r : Row) (upper : Bool) {x : ℝ}
    (S : Interval (Real.sin x)) (C : Interval (Real.cos x)) :
    Interval (CircularNorm.energy (mass r) (cosineWeight r) (sineWeight r upper) x) :=
  ((Interval.point (mass r)).add ((Interval.point (cosineWeight r)).mul C)).add
    ((Interval.point (sineWeight r upper)).mul S)
def normBox (r : Row) (upper : Bool) {x : ℝ}
    (S : Interval (Real.sin x)) (C : Interval (Real.cos x))
    (hn : 0≤(energyBox r upper S C).lo) : Interval (N r upper x) :=
  rootSix (energyBox r upper S C) 2 (by norm_num) hn
def valueBox (r : Row) (upper : Bool) {x : ℝ} (X : Interval x)
    (S : Interval (Real.sin x)) (C : Interval (Real.cos x))
    (hn : 0≤(energyBox r upper S C).lo) : Interval (F r upper x) := by
  let T : Interval (if upper then Real.sin x else 0) := by
    cases upper
    · exact Interval.point 0
    · exact S
  convert (((((halfPi.add ((Interval.point (direction upper)).mul X)).add
    (Interval.point (coC r))).add (Interval.point ((lambda r+coP r+coQ r)/2))).add
      ((Interval.point (lambda r)).mul (C.add T))).sub (circleRadius.mul (normBox r upper S C hn)))
    using 1 <;> cases upper <;> dsimp [F,angle,T,direction] <;> ring

def zeroS : Interval (Real.sin (0:ℝ)) := by simpa using Interval.point (0:ℝ)
def zeroC : Interval (Real.cos (0:ℝ)) := by simpa using Interval.point (1:ℝ)
private lemma r83_mpr_lo {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).lo=S.lo := by subst e; rfl
private lemma r83_mpr_hi {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).hi=S.hi := by subst e; rfl
private lemma r83_zeroS_lo : zeroS.lo=0 := r83_mpr_lo Real.sin_zero _ _
private lemma r83_zeroS_hi : zeroS.hi=0 := r83_mpr_hi Real.sin_zero _ _
private lemma r83_zeroC_lo : zeroC.lo=1 := r83_mpr_lo Real.cos_zero _ _
private lemma r83_zeroC_hi : zeroC.hi=1 := r83_mpr_hi Real.cos_zero _ _
private lemma r83_valueBox_false_lo (r : Row) {x : ℝ} (X : Interval x)
    (S : Interval (Real.sin x)) (C : Interval (Real.cos x)) (hn : 0≤(energyBox r false S C).lo) :
    (valueBox r false X S C hn).lo=(((((halfPi.add ((Interval.point (direction false)).mul X)).add
      (Interval.point (coC r))).add (Interval.point ((lambda r+coP r+coQ r)/2))).add
        ((Interval.point (lambda r)).mul (C.add (Interval.point 0)))).sub
          (circleRadius.mul (normBox r false S C hn))).lo := by
  unfold valueBox
  exact r83_mpr_lo (by simp only [F,angle]) _ _
private lemma r83_valueBox_true_lo (r : Row) {x : ℝ} (X : Interval x)
    (S : Interval (Real.sin x)) (C : Interval (Real.cos x)) (hn : 0≤(energyBox r true S C).lo) :
    (valueBox r true X S C hn).lo=(((((halfPi.add ((Interval.point (direction true)).mul X)).add
      (Interval.point (coC r))).add (Interval.point ((lambda r+coP r+coQ r)/2))).add
        ((Interval.point (lambda r)).mul (C.add S))).sub
          (circleRadius.mul (normBox r true S C hn))).lo := by
  unfold valueBox
  exact r83_mpr_lo (by simp only [F,angle]) _ _
private lemma r83_rows (r : Row) (hr : targetPositive r=true) :
    r=1 ∨ r=2 ∨ r=3 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=10 ∨ r=13 ∨ r=14 ∨ r=15 ∨ r=18 ∨ r=20 ∨ r=21 ∨ r=22 := by
  fin_cases r <;> simp_all [targetPositive]

local macro "r83_fixed" : tactic => `(tactic|
  norm_num [r83_zeroS_lo,r83_zeroS_hi,r83_zeroC_lo,r83_zeroC_hi,
    energyBox,normBox,mass,cosineWeight,sineWeight,direction,lambda,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    piBox,halfPi,axial,circleRadius,Reference.sine,Reference.cosine,
    rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
    SecondWord.OppositeThree.ReferenceAlgebra.rootStep,HighOrderTaylor.S15,HighOrderTaylor.S13,
    HighOrderTaylor.S11,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8,
    coC,coP,coQ,coG,Q0])
theorem zero_energy (r : Row) (hr : targetPositive r=true) :
    0≤(energyBox r false zeroS zeroC).lo := by
  rcases r83_rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> r83_fixed
theorem aligned (r : Row) (hr : targetPositive r=true) : (89809/100000:ℝ)<F r false 0 := by
  have hlo : (89809/100000:ℝ)<
      (valueBox r false (Interval.point 0) zeroS zeroC (zero_energy r hr)).lo := by
    rw [r83_valueBox_false_lo]
    rcases r83_rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> r83_fixed
  exact hlo.trans_le (valueBox r false _ zeroS zeroC (zero_energy r hr)).mem.1

theorem cap_energy (r : Row) (hr : targetPositive r=true) (upper : Bool) :
    0≤(energyBox r upper (sine (by norm_num : (0:ℝ)≤7/10))
      (cosine (by norm_num : (0:ℝ)≤7/10))).lo := by
  fin_cases r <;> cases upper <;> norm_num [targetPositive] at hr <;>
    dsimp [energyBox,mass,cosineWeight,sineWeight,direction,lambda] <;> mixed_fixed
theorem lower_cap (r : Row) (hr : targetPositive r=true) (hs : sourcePositive r=true) :
    (1813/2000:ℝ)<F r false (7/10) := by
  have hlo : (1813/2000:ℝ)<(valueBox r false (Interval.point (7/10))
      (sine (by norm_num : (0:ℝ)≤7/10)) (cosine (by norm_num : (0:ℝ)≤7/10))
        (cap_energy r hr false)).lo := by
    rw [r83_valueBox_false_lo]
    have hrows : r=1 ∨ r=5 ∨ r=10 ∨ r=13 ∨ r=18 ∨ r=22 := by
      rcases r83_rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp_all [sourcePositive]
    rcases hrows with rfl|rfl|rfl|rfl|rfl|rfl <;> r83_fixed
  exact hlo.trans_le (valueBox r false _ _ _ (cap_energy r hr false)).mem.1
private lemma r83_upper_cap_first (r : Row) (hr : targetPositive r=true)
    (hrows : r=1 ∨ r=2 ∨ r=3 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=10) :
    (119/100:ℝ)<(valueBox r true (Interval.point (7/10))
      (sine (by norm_num : (0:ℝ)≤7/10)) (cosine (by norm_num : (0:ℝ)≤7/10))
        (cap_energy r hr true)).lo := by
  rw [r83_valueBox_true_lo]
  rcases hrows with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> r83_fixed
private lemma r83_upper_cap_second (r : Row) (hr : targetPositive r=true)
    (hrows : r=13 ∨ r=14 ∨ r=15 ∨ r=18 ∨ r=20 ∨ r=21 ∨ r=22) :
    (119/100:ℝ)<(valueBox r true (Interval.point (7/10))
      (sine (by norm_num : (0:ℝ)≤7/10)) (cosine (by norm_num : (0:ℝ)≤7/10))
        (cap_energy r hr true)).lo := by
  rw [r83_valueBox_true_lo]
  rcases hrows with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> r83_fixed
theorem upper_cap (r : Row) (hr : targetPositive r=true) : (119/100:ℝ)<F r true (7/10) := by
  have hlo : (119/100:ℝ)<(valueBox r true (Interval.point (7/10))
      (sine (by norm_num : (0:ℝ)≤7/10)) (cosine (by norm_num : (0:ℝ)≤7/10))
        (cap_energy r hr true)).lo := by
    have hsplit : (r=1 ∨ r=2 ∨ r=3 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=10) ∨
        (r=13 ∨ r=14 ∨ r=15 ∨ r=18 ∨ r=20 ∨ r=21 ∨ r=22) := by
      rcases r83_rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    rcases hsplit with h|h
    · exact r83_upper_cap_first r hr h
    · exact r83_upper_cap_second r hr h
  exact hlo.trans_le (valueBox r true _ _ _ (cap_energy r hr true)).mem.1

def cut : ℝ := Real.pi/2-1
theorem cut_mem : cut∈Icc 0 (7/10) := by
  dsimp [cut]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]
def cutS : Interval (Real.sin cut) := by
  simpa [cut,Real.sin_sub] using cosine (by norm_num : (0:ℝ)≤1)
def cutC : Interval (Real.cos cut) := by
  simpa [cut,Real.cos_sub] using sine (by norm_num : (0:ℝ)≤1)
def cutX : Interval cut := halfPi.sub (Interval.point 1)
private lemma r83_cutS_lo : cutS.lo=(cosine (by norm_num : (0:ℝ)≤1)).lo := by
  unfold cutS
  exact r83_mpr_lo (by rw [cut,Real.sin_pi_div_two_sub]) _ _
private lemma r83_cutS_hi : cutS.hi=(cosine (by norm_num : (0:ℝ)≤1)).hi := by
  unfold cutS
  exact r83_mpr_hi (by rw [cut,Real.sin_pi_div_two_sub]) _ _
private lemma r83_cutC_lo : cutC.lo=(sine (by norm_num : (0:ℝ)≤1)).lo := by
  unfold cutC
  exact r83_mpr_lo (by rw [cut,Real.cos_pi_div_two_sub]) _ _
private lemma r83_cutC_hi : cutC.hi=(sine (by norm_num : (0:ℝ)≤1)).hi := by
  unfold cutC
  exact r83_mpr_hi (by rw [cut,Real.cos_pi_div_two_sub]) _ _

theorem cut_energy (r : Row) (hr : targetPositive r=true) :
    0≤(energyBox r false cutS cutC).lo := by
  rcases r83_rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [r83_cutS_lo,r83_cutS_hi,r83_cutC_lo,r83_cutC_hi,cutX,
      energyBox,normBox,mass,cosineWeight,sineWeight,direction,lambda,
      Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
      piBox,halfPi,axial,circleRadius,Reference.sine,Reference.cosine,
      rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
      SecondWord.OppositeThree.ReferenceAlgebra.rootStep,HighOrderTaylor.S15,HighOrderTaylor.S13,
      HighOrderTaylor.S11,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8,
      coC,coP,coQ,coG,Q0]
theorem lower_cut (r : Row) (hr : targetPositive r=true) (hs : sourcePositive r=false) :
    (1813/2000:ℝ)<F r false cut := by
  have hlo : (1813/2000:ℝ)<(valueBox r false cutX cutS cutC (cut_energy r hr)).lo := by
    rw [r83_valueBox_false_lo]
    have hrows : r=2 ∨ r=3 ∨ r=6 ∨ r=7 ∨ r=14 ∨ r=15 ∨ r=20 ∨ r=21 := by
      rcases r83_rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp_all [sourcePositive]
    rcases hrows with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [r83_cutS_lo,r83_cutS_hi,r83_cutC_lo,r83_cutC_hi,cutX,
        energyBox,normBox,mass,cosineWeight,sineWeight,direction,lambda,
        Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
        Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
        piBox,halfPi,axial,circleRadius,Reference.sine,Reference.cosine,
        rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
        SecondWord.OppositeThree.ReferenceAlgebra.rootStep,HighOrderTaylor.S15,HighOrderTaylor.S13,
        HighOrderTaylor.S11,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
        Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8,
        coC,coP,coQ,coG,Q0]
  exact hlo.trans_le (valueBox r false cutX cutS cutC (cut_energy r hr)).mem.1

def cap (x : ℝ) : ℝ := (outerAxial-1/2)*Real.cos x-Real.sin x/2-1/2
theorem cap_antitone : AntitoneOn cap (Icc 0 (7/10)) := by
  have hd : ∀ x, HasDerivAt cap (-(outerAxial-1/2)*Real.sin x-Real.cos x/2) x := by
    intro x
    have h := (((Real.hasDerivAt_cos x).const_mul (outerAxial-1/2)).fun_sub
      ((Real.hasDerivAt_sin x).div_const 2)).sub_const (1/2)
    exact h.congr_deriv (by ring)
  apply antiOn_of_hasDeriv_nonpos (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => hd x)
  intro x hx
  have ht := positive_trig (Ioo_subset_Icc_self hx)
  have hh := mul_nonneg (show 0≤outerAxial-1/2 by linarith [outer_endpoint_bounds.1]) ht.2.2.1
  linarith [ht.1]
theorem cap_cut_negative : cap cut<0 := by
  let B := (((axial.sub (Interval.point (1/2))).mul cutC).sub
    (cutS.div (Interval.point 2) (by norm_num [Interval.point]))).sub (Interval.point (1/2))
  have hhi : B.hi<0 := by
    simp only [B]
    norm_num [r83_cutS_lo,r83_cutS_hi,r83_cutC_lo,r83_cutC_hi,cutX,
      energyBox,normBox,mass,cosineWeight,sineWeight,direction,lambda,
      Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
      piBox,halfPi,axial,circleRadius,Reference.sine,Reference.cosine,
      rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
      SecondWord.OppositeThree.ReferenceAlgebra.rootStep,HighOrderTaylor.S15,HighOrderTaylor.S13,
      HighOrderTaylor.S11,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8,
      coC,coP,coQ,coG,Q0]
  exact B.mem.2.trans_lt hhi

theorem original_lower_cut (r : Row) (hr : targetPositive r=true) (hσ : sourcePositive r=false)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourceSecondary r a b A B (angle false x)) : x<cut := by
  have hcore := CoreAngleEndpoint.state_bounds hs
  have houter := outer_bounds ht
  have htr := positive_trig hx
  have hA := mul_le_mul_of_nonneg_right houter.2.1 (show 0≤Real.cos x by linarith [htr.1])
  have hB := mul_nonneg ht.1 htr.2.2.1
  dsimp [sourceSecondary] at hm
  rw [angle_width false hx,angle_sin,angle_cos] at hm
  simp [sourceSign,targetSign,WordProblems.sign,hσ,hr,direction] at hm
  have hcap : 0≤cap x := by dsimp [cap]; nlinarith
  by_contra! hbad
  have h := cap_antitone cut_mem hx hbad
  linarith [cap_cut_negative]

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.CoreSecondaryPositive
