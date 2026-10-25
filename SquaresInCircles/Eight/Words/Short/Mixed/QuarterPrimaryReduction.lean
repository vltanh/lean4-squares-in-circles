module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterData
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.PositivePrimary

/-!
# Eight squares: pointwise source-sign dominance for the original primary owners

The primary separating inequality is unchanged when the normalized source sign is negative
(`primary_constraint`). The original signed labels dominate that comparison pointwise on the same
state (`core_cost_reduction`, `outer_cost_reduction`). This is only a pair inequality; the vertex
labels of the cyclic sum stay the same.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter
open CommonQuarter CorePairGeometry Arithmetic

def primaryRow : Row→Row :=
  ![0,3,2,3,4,7,6,7,4,11,6,11,12,15,14,15,12,19,14,19,20,21,20,23]

theorem primaryRow_signs (r : Row) :
    sourcePositive (primaryRow r)=false ∧ targetPositive (primaryRow r)=targetPositive r := by
  fin_cases r <;> decide
theorem primaryRow_self (r : Row) (hr : sourcePositive r=false) : primaryRow r=r := by
  fin_cases r <;> simp [sourcePositive,primaryRow] at hr ⊢
theorem primary_constraint (r : Row) (a b A B φ : ℝ) :
    sourcePrimary (primaryRow r) a b A B φ↔sourcePrimary r a b A B φ := by
  simp only [sourcePrimary,targetSign,(primaryRow_signs r).2]

theorem core_cost_reduction (r : Row) {a b A B φ : ℝ} (hs : CoreState a b) :
    coreOuterCost (primaryRow r) a b A B φ≤coreOuterCost r a b A B φ := by
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.1
  fin_cases r <;>
    norm_num [coreOuterCost,primaryRow,sourceSign,targetSign,sourcePositive,targetPositive,
      WordProblems.sign,coC,coP,coQ,coG] <;> linarith

theorem outer_sum_lower {a b : ℝ} (hs : OuterState a b) : outerAxial≤a+b := by
  have ha : 0≤a := hs.1.trans hs.2.1
  have he := hs.2.2
  have hax := axial_circle
  have h0 : 0≤outerAxial := by linarith [outer_endpoint_bounds.1]
  have hQ : (1:ℝ)/2≤Q0 := by norm_num [Q0]
  have hprod : 0≤((b+1/2)^2-1/4)*(Q0-1/4-(b+1/2)^2) := by
    apply mul_nonneg
    · nlinarith [hs.1]
    · nlinarith [hs.1,hs.2.1]
  have hA : (a+1/2)^2=Q0-(b+1/2)^2 := by linarith
  have hsq : ((outerAxial+1/2)/2)^2≤((a+1/2)*(b+1/2))^2 := by
    rw [mul_pow,hA]
    nlinarith [hprod,hax]
  have hP : (outerAxial+1/2)/2≤(a+1/2)*(b+1/2) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by nlinarith [hs.1]) hsq
  have hsq2 : (outerAxial+1)^2≤(a+b+1)^2 := by nlinarith [hP,he,hax]
  have := le_of_pow_le_pow_left₀ (by norm_num) (by linarith [hs.1]) hsq2
  linarith

theorem outer_increasing_label_lower {a b X Y : ℝ} (hs : OuterState a b)
    (hY : |X|≤Y) : X*outerAxial≤X*a+Y*b := by
  have hb := outer_bounds hs
  have hy : 0≤Y := (abs_nonneg X).trans hY
  by_cases hx : 0≤X
  · have hsum := mul_le_mul_of_nonneg_left (outer_sum_lower hs) hx
    have hrem := mul_nonneg (show 0≤Y-X by rw [abs_of_nonneg hx] at hY; linarith) hs.1
    nlinarith
  · exact MixedQuarter.outer_axial_lower hs (le_of_not_ge hx) hy

theorem outer_cost_reduction (r : Row) {a b A B φ : ℝ} (hs : OuterState a b) :
    outerCoreCost (primaryRow r) a b A B φ≤outerCoreCost r a b A B φ := by
  by_cases hr : sourcePositive r=false
  · rw [primaryRow_self r hr]
  have hsigma : sourcePositive r=true := by cases h : sourcePositive r <;> simp_all
  let X := ocP r-ocP (primaryRow r)
  let Y := ocQ r+ocQ (primaryRow r)
  have hXY : |X|≤Y := by
    fin_cases r <;> norm_num [sourcePositive] at hsigma <;>
      norm_num [X,Y,primaryRow,ocP,ocQ]
  have hsource := outer_increasing_label_lower hs hXY
  have hzero : 0<ocC r-ocC (primaryRow r)+X*outerAxial := by
    have ha := ShortOuterZero.fine_axial_bounds
    fin_cases r <;> norm_num [sourcePositive] at hsigma <;>
      norm_num [X,primaryRow,ocC,ocP] <;> linarith [ha.1,ha.2]
  have htarget : ocG (primaryRow r)=ocG r := by
    fin_cases r <;> norm_num [primaryRow,ocG]
  have hsign : sourceSign (primaryRow r)= -1 := by
    simp [sourceSign,WordProblems.sign,(primaryRow_signs r).1]
  have hself : sourceSign r=1 := by simp [sourceSign,WordProblems.sign,hsigma]
  dsimp [outerCoreCost]
  rw [hsign,hself,htarget,show targetSign (primaryRow r)=targetSign r by
    simp [targetSign,(primaryRow_signs r).2]]
  dsimp [X,Y] at hsource hzero
  linarith

end SquaresInCircles.Eight.ShortWord.MixedQuarter
