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
      ((Interval.point (lambda r)).mul (C.add T))).sub (circleRadius.mul (normBox r upper S C hn))
    using 1 <;> cases upper <;> dsimp [F,angle,T,direction] <;> ring

def zeroS : Interval (Real.sin (0:ℝ)) := by simpa using Interval.point (0:ℝ)
def zeroC : Interval (Real.cos (0:ℝ)) := by simpa using Interval.point (1:ℝ)
theorem zero_energy (r : Row) (hr : targetPositive r=true) :
    0≤(energyBox r false zeroS zeroC).lo := by
  fin_cases r <;> norm_num [targetPositive] at hr <;>
    dsimp [energyBox,mass,cosineWeight,sineWeight,direction,zeroS,zeroC,lambda] <;> mixed_fixed
theorem aligned (r : Row) (hr : targetPositive r=true) : (89809/100000:ℝ)<F r false 0 := by
  let B := valueBox r false (Interval.point 0) zeroS zeroC (zero_energy r hr)
  have hlo : (89809/100000:ℝ)<B.lo := by
    fin_cases r <;> norm_num [targetPositive] at hr <;>
      dsimp [B,valueBox,normBox,energyBox,mass,cosineWeight,sineWeight,direction,zeroS,zeroC,lambda] <;>
        mixed_fixed
  exact hlo.trans_le B.mem.1

theorem cap_energy (r : Row) (hr : targetPositive r=true) (upper : Bool) :
    0≤(energyBox r upper (sine (by norm_num : (0:ℝ)≤7/10))
      (cosine (by norm_num : (0:ℝ)≤7/10))).lo := by
  fin_cases r <;> cases upper <;> norm_num [targetPositive] at hr <;>
    dsimp [energyBox,mass,cosineWeight,sineWeight,direction,lambda] <;> mixed_fixed
theorem lower_cap (r : Row) (hr : targetPositive r=true) (hs : sourcePositive r=true) :
    (1813/2000:ℝ)<F r false (7/10) := by
  let B := valueBox r false (Interval.point (7/10))
    (sine (by norm_num : (0:ℝ)≤7/10)) (cosine (by norm_num : (0:ℝ)≤7/10))
    (cap_energy r hr false)
  have hlo : (1813/2000:ℝ)<B.lo := by
    fin_cases r <;> norm_num [targetPositive,sourcePositive] at hr hs <;>
      dsimp [B,valueBox,normBox,energyBox,mass,cosineWeight,sineWeight,direction,lambda] <;> mixed_fixed
  exact hlo.trans_le B.mem.1
theorem upper_cap (r : Row) (hr : targetPositive r=true) : (119/100:ℝ)<F r true (7/10) := by
  let B := valueBox r true (Interval.point (7/10))
    (sine (by norm_num : (0:ℝ)≤7/10)) (cosine (by norm_num : (0:ℝ)≤7/10))
    (cap_energy r hr true)
  have hlo : (119/100:ℝ)<B.lo := by
    fin_cases r <;> norm_num [targetPositive] at hr <;>
      dsimp [B,valueBox,normBox,energyBox,mass,cosineWeight,sineWeight,direction,lambda] <;> mixed_fixed
  exact hlo.trans_le B.mem.1

def cut : ℝ := Real.pi/2-1
theorem cut_mem : cut∈Icc 0 (7/10) := by
  dsimp [cut]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]
def cutS : Interval (Real.sin cut) := by
  simpa [cut,Real.sin_sub] using cosine (by norm_num : (0:ℝ)≤1)
def cutC : Interval (Real.cos cut) := by
  simpa [cut,Real.cos_sub] using sine (by norm_num : (0:ℝ)≤1)
def cutX : Interval cut := halfPi.sub (Interval.point 1)
theorem cut_energy (r : Row) (hr : targetPositive r=true) :
    0≤(energyBox r false cutS cutC).lo := by
  fin_cases r <;> norm_num [targetPositive] at hr <;>
    dsimp [energyBox,mass,cosineWeight,sineWeight,direction,cutS,cutC,lambda] <;> mixed_fixed
theorem lower_cut (r : Row) (hr : targetPositive r=true) (hs : sourcePositive r=false) :
    (1813/2000:ℝ)<F r false cut := by
  let B := valueBox r false cutX cutS cutC (cut_energy r hr)
  have hlo : (1813/2000:ℝ)<B.lo := by
    fin_cases r <;> norm_num [targetPositive,sourcePositive] at hr hs <;>
      dsimp [B,valueBox,normBox,energyBox,mass,cosineWeight,sineWeight,direction,
        cutS,cutC,cutX,lambda] <;> mixed_fixed
  exact hlo.trans_le B.mem.1

def cap (x : ℝ) : ℝ := (outerAxial-1/2)*Real.cos x-Real.sin x/2-1/2
theorem cap_antitone : AntitoneOn cap (Icc 0 (7/10)) := by
  apply antiOn_of_hasDeriv_nonpos
    (f':=fun x => -(outerAxial-1/2)*Real.sin x-Real.cos x/2)
  · intro x _
    unfold cap
    fun_prop
  · intro x _
    convert ((((Real.hasDerivAt_cos x).const_mul (outerAxial-1/2)).sub
      ((Real.hasDerivAt_sin x).div_const 2)).sub_const (1/2)) using 1 <;> dsimp [cap] <;> ring
  · intro x hx
    have ht := positive_trig (Ioo_subset_Icc_self hx)
    have hh := mul_nonneg (show 0≤outerAxial-1/2 by linarith [outer_endpoint_bounds.1]) ht.2.2.1
    linarith [ht.1]
theorem cap_cut_negative : cap cut<0 := by
  let B := (((axial.sub (Interval.point (1/2))).mul cutC).sub
    (cutS.div (Interval.point 2) (by norm_num [Interval.point]))).sub (Interval.point (1/2))
  have hhi : B.hi<0 := by dsimp [B,cutS,cutC]; mixed_fixed
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
