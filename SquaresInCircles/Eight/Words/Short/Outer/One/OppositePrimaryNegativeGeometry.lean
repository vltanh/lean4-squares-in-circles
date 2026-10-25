module

public import SquaresInCircles.Eight.Stationary.Envelope
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAlignedL
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroPositiveJ
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroCycle
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterData
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterReferences
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryData
public import SquaresInCircles.Eight.Words.Short.Outer.One.RoleFour
public import SquaresInCircles.Eight.Owners.Stationary.PrimitiveForces
public import SquaresInCircles.Eight.Arithmetic.WholeIntervalPolynomial

/-!
# Eight squares: the original lower primary separator forces the whole angle cap

The separator makes the whole angle region beyond the cap impossible (`forced_cap`). The proof
takes the two outer-arc endpoints (`target_support`) and the strictly decreasing original
feasibility expression (`feasibility_decreases`, `cap_infeasible`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Negative
open CommonQuarter CorePairGeometry Arithmetic WrongWordCircleSupport StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def cap : ℝ := 113/500
def feasibility (x : ℝ) : ℝ := outerAxial*(1-Real.sin x)-width x
def feasibilityD (x : ℝ) : ℝ := -(outerAxial+1/2)*Real.cos x+Real.sin x/2

theorem target_support {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10)) :
    outerAxial*Real.sin x≤A*Real.sin x+B*Real.cos x := by
  have tr := positive_trig hx
  have ha := ShortOuterZero.fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hdk := mul_lt_mul'' hd.1 tr.1 (by norm_num) (by norm_num)
  have hds := mul_le_mul
    (show outerAxial-outerDiagonal≤176821959/125000000-449607/500000 by linarith)
    tr.2.2.2.1.le tr.2.2.1 (by norm_num)
  have hdiag : outerAxial*Real.sin x≤(Real.sin x+Real.cos x)*outerDiagonal := by
    linarith
  have hh := outer_concave_lower ht tr.2.2.1 (le_of_eq (mul_comm _ _)) hdiag
  linarith only [hh]

theorem feasibility_hasDerivAt (x : ℝ) : HasDerivAt feasibility (feasibilityD x) x := by
  have hw := ((((Real.hasDerivAt_cos x).const_add 1).fun_add (Real.hasDerivAt_sin x)).div_const 2)
  have hh := (((Real.hasDerivAt_sin x).const_sub 1).const_mul outerAxial).fun_sub hw
  exact hh.congr_deriv (by simp only [feasibilityD]; ring)

theorem feasibility_decreases : AntitoneOn feasibility (Icc 0 (7/10)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x _ => (feasibility_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => feasibility_hasDerivAt x)
  intro x hx
  have tr := positive_trig (Ioo_subset_Icc_self hx)
  have hp := mul_lt_mul''
    (show (191/100:ℝ)<outerAxial+1/2 by linarith [outer_endpoint_bounds.1]) tr.1
    (by norm_num) (by norm_num)
  dsimp [feasibilityD]
  linarith [tr.2.2.2.1]

theorem cap_infeasible : feasibility cap< -(17/10000:ℝ) := by
  let Z := (axial.mul ((Interval.point 1).sub (sine (by norm_num [cap] : 0≤cap)))).sub
    ((((Interval.point 1).add (cosine (by norm_num [cap] : 0≤cap))).add
      (sine (by norm_num [cap] : 0≤cap))).mul (Interval.point (1/2)))
  have hh : Z.hi< -(17/10000:ℝ) := by dsimp [Z,cap]; mixed_fixed
  have hz : feasibility cap≤Z.hi := by simpa [feasibility,width,div_eq_mul_inv] using Z.mem.2
  exact hz.trans_lt hh

theorem forced_cap {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : width x≤a-A*Real.sin x-B*Real.cos x) : x<cap := by
  have htarg := target_support ht hx
  have hsrc := (outer_bounds hs).2.1
  have hf : 0≤feasibility x := by dsimp [feasibility]; linarith
  by_contra! hcap
  have hh := feasibility_decreases (by norm_num [cap] : cap∈Icc 0 (7/10)) hx hcap
  linarith [cap_infeasible]

theorem cap_trig : (6091/6250:ℝ)<Real.cos cap ∧ Real.sin cap<22409/100000 := by
  have hc : (6091/6250:ℝ)<(ShortWord.MixedQuarter.Reference.cosine
      (by norm_num [cap] : (0:ℝ)≤cap)).lo := by
    dsimp [cap]; mixed_fixed
  have hs : (ShortWord.MixedQuarter.Reference.sine
      (by norm_num [cap] : (0:ℝ)≤cap)).hi<(22409/100000:ℝ) := by
    dsimp [cap]; mixed_fixed
  exact ⟨hc.trans_le (ShortWord.MixedQuarter.Reference.cosine (by norm_num [cap])).mem.1,
    (ShortWord.MixedQuarter.Reference.sine (by norm_num [cap])).mem.2.trans_lt hs⟩

theorem small_angle {x : ℝ} (hx : x∈Icc 0 cap) : x∈Icc 0 (7/10) :=
  ⟨hx.1,hx.2.trans (by norm_num [cap])⟩
theorem small_trig {x : ℝ} (hx : x∈Icc 0 cap) :
    (6091/6250:ℝ)<Real.cos x ∧ 0≤Real.sin x ∧ Real.sin x<22409/100000 := by
  have hc := cos_anti (small_angle hx) (by norm_num [cap] : cap∈Icc 0 (7/10)) hx.2
  have hs := sin_mono (small_angle hx) (by norm_num [cap] : cap∈Icc 0 (7/10)) hx.2
  exact ⟨cap_trig.1.trans_le hc,(positive_trig (small_angle hx)).2.2.1,hs.trans_lt cap_trig.2⟩

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Negative
