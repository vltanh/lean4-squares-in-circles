module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Common.Analysis
public import SquaresInCircles.Eight.Stationary.CriticalHessian
public import SquaresInCircles.Eight.Stationary.Generated.LocalStationaryBounds

/-!
# Eight squares: the stationary configuration

`sharpData` is the chain at the stationary zero `(qStar, sharpPose)` of `Analysis.lean`, with its
coordinates given by the successive square roots (`radicalCoordinates`). Its equations, its
branch signs and its uniqueness are theorems: it solves the stationary system
(`sharpData_stationary`), and every solution of that system equals it (`stationary_unique`), by
the geometric argument of `Envelope.lean` (`FiveCornerGeometry.stationary_chain_unique`). The
decimals below are rational brackets for `qStar` and the coordinates (`qStar_bracket`,
`qStar_limits`, `sharp_coordinates`, `sharp_y`), not definitions of them.
-/

section
/-!
## The stationary zero

For each squared radius `q` in `[qMinus, Q0]` the defect `F(q, ·, ·)` of the chain, as a function
of the position `y` and the half-angle tangent `z` of the tilt, is strongly convex on the fixed
compact rectangle `poseBox`: the interval bounds on its Hessian give it curvature `1/4` in both
coordinates (`hessian_data`, `family_strong_convex`). Its minimum over the rectangle is attained
at an interior point (`minimum_interior`), where both partial derivatives vanish
(`minimizingPose_stationary`). The minimum value decreases in `q` with slope between `3` and `4`
(`minimum_radius_difference`), so it is continuous, and it is positive at `qMinus` and negative at
`Q0` (`minimum_endpoint_signs`). By the intermediate value theorem it vanishes at exactly one
`qStar` (`unique_minimum_zero`), so `F`, `F_y` and `F_z` vanish at `(qStar, sharpPose)`
(`sharpPose_value`, `sharpPose_stationary`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set

namespace SquaresInCircles.Eight.Stationary
open Arithmetic Generated

abbrev Pose := ℝ × ℝ
def poseBox : Set Pose := Icc (-(937/1000)) (-(179/200)) ×ˢ Icc (1/20) (81/1000)
def radiusBox : Set ℝ := Icc (7831/2000) (9789/2500)
def trial : Pose := (trialY,trialZ)

def familyValue (q : ℝ) (p : Pose) : ℝ := FFormula.eval ![q,p.1,p.2]
def familyY (q : ℝ) (p : Pose) : ℝ := FyFormula.eval ![q,p.1,p.2]
def familyZ (q : ℝ) (p : Pose) : ℝ := FzFormula.eval ![q,p.1,p.2]
def familyQ (q : ℝ) (p : Pose) : ℝ := FqFormula.eval ![q,p.1,p.2]
def familyYY (q : ℝ) (p : Pose) : ℝ := FyyFormula.eval ![q,p.1,p.2]
def familyYZ (q : ℝ) (p : Pose) : ℝ := FyzFormula.eval ![q,p.1,p.2]
def familyZZ (q : ℝ) (p : Pose) : ℝ := FzzFormula.eval ![q,p.1,p.2]

theorem local_mem {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    localBox.Mem ![q,p.1,p.2] := by
  have hq' : (7831/2000:ℝ) ≤ q ∧ q ≤ 9789/2500 := hq
  have hy : -(937/1000:ℝ) ≤ p.1 ∧ p.1 ≤ -(179/200) := hp.1
  have hz : (1/20:ℝ) ≤ p.2 ∧ p.2 ≤ 81/1000 := hp.2
  intro i; fin_cases i
  · norm_num [localBox,QInterval.Mem]
    exact hq'
  · norm_num [localBox,QInterval.Mem]
    constructor <;> linarith [hy.1, hy.2]
  · norm_num [localBox,QInterval.Mem]
    exact hz

theorem trial_mem : trial ∈ poseBox := by
  norm_num [trial,poseBox,trialY,trialZ]

theorem family_continuous : Continuous (fun x : ℝ × Pose => familyValue x.1 x.2) := by
  simp only [familyValue,F_eval]
  unfold scalarF
  push_cast
  fun_prop (disch := intro x; positivity)

theorem family_continuous_pose (q : ℝ) : Continuous (familyValue q) := by
  have h := family_continuous.comp (continuous_const.prodMk continuous_id :
    Continuous fun p : Pose => (q,p))
  rw [Function.comp_def] at h
  simpa using h

theorem family_regular {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    FFormula.RegularAt ![q,p.1,p.2] ∧
    FyFormula.RegularAt ![q,p.1,p.2] ∧ FzFormula.RegularAt ![q,p.1,p.2] := by
  have he := local_mem hq hp
  exact ⟨fullF_regular _ he,fullFy_regular _ he,fullFz_regular _ he⟩

theorem family_q_bound {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    -4 ≤ familyQ q p ∧ familyQ q p ≤ -3 := fullFq_bound _ (local_mem hq hp)

theorem hessian_data {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    6 ≤ familyYY q p ∧
      0 < (familyYY q p-1/4)*(familyZZ q p-1/4)-(familyYZ q p)^2 := by
  have he := local_mem hq hp
  obtain ⟨i,j,hij⟩ := determinant_cover _ he
  have hd := (determinant_bound i j _ hij).1
  have hy := (fullFyy_bound _ he).1
  have heq := determinant_eval ![q,p.1,p.2]
  rw [show determinantFormula = formula258 from rfl] at heq
  exact ⟨hy,by dsimp [familyYY,familyYZ,familyZZ]; linarith⟩

theorem quadratic_form_bound {A B C : ℝ} (hA : 6 ≤ A)
    (hdet : 0 < (A-1/4)*(C-1/4)-B^2) (u v : ℝ) :
    (u^2+v^2)/4 ≤ A*u^2+2*B*u*v+C*v^2 := by
  have h := sq_nonneg ((A-1/4)*u+B*v)
  have h' := mul_nonneg hdet.le (sq_nonneg v)
  have heq : (A-1/4)*(A*u^2+2*B*u*v+C*v^2-(u^2+v^2)/4) =
      ((A-1/4)*u+B*v)^2+((A-1/4)*(C-1/4)-B^2)*v^2 := by ring
  have hp : 0 < A-1/4 := by linarith
  nlinarith

def segment (a b : Pose) (t : ℝ) : Pose :=
  ((1-t)*a.1+t*b.1,(1-t)*a.2+t*b.2)

theorem segment_mem {a b : Pose} (ha : a ∈ poseBox) (hb : b ∈ poseBox)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : segment a b t ∈ poseBox := by
  exact (convex_Icc _ _).prod (convex_Icc _ _) ha hb
    (by linarith [ht.2]) ht.1 (by ring)

theorem segment_deriv (q : ℝ) (a b : Pose) (t : ℝ) :
    ∀ i : Fin 3, HasDerivAt (fun s => ![q,(segment a b s).1,(segment a b s).2] i)
      (![0,b.1-a.1,b.2-a.2] i) t := by
  intro i; fin_cases i
  · simpa using hasDerivAt_const t q
  · convert (((hasDerivAt_id' t).const_sub 1).mul_const a.1).fun_add
      ((hasDerivAt_id' t).mul_const b.1) using 1 <;> simp [segment]
    ring
  · convert (((hasDerivAt_id' t).const_sub 1).mul_const a.2).fun_add
      ((hasDerivAt_id' t).mul_const b.2) using 1 <;> simp [segment]
    ring

theorem family_segment_first {q : ℝ} (hq : q ∈ radiusBox)
    {a b : Pose} (ha : a ∈ poseBox) (hb : b ∈ poseBox)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => familyValue q (segment a b s))
      (familyY q (segment a b t)*(b.1-a.1)+familyZ q (segment a b t)*(b.2-a.2)) t := by
  have h := Formula.hasDerivAt_curve FFormula (segment_deriv q a b t)
    (family_regular hq (segment_mem ha hb ht)).1
  rw [Formula.directional_eq_partials] at h
  simpa [Fin.sum_univ_succ,Fq_diff,Fy_diff,Fz_diff,familyValue,familyY,familyZ] using h

theorem family_segment_second {q : ℝ} (hq : q ∈ radiusBox)
    {a b : Pose} (ha : a ∈ poseBox) (hb : b ∈ poseBox)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt
      (fun s => familyY q (segment a b s)*(b.1-a.1)+
        familyZ q (segment a b s)*(b.2-a.2))
      (familyYY q (segment a b t)*(b.1-a.1)^2+
        2*familyYZ q (segment a b t)*(b.1-a.1)*(b.2-a.2)+
        familyZZ q (segment a b t)*(b.2-a.2)^2) t := by
  have hreg := family_regular hq (segment_mem ha hb ht)
  have hy := Formula.hasDerivAt_curve FyFormula (segment_deriv q a b t) hreg.2.1
  have hz := Formula.hasDerivAt_curve FzFormula (segment_deriv q a b t) hreg.2.2
  rw [Formula.directional_eq_partials] at hy hz
  have h := (hy.mul_const (b.1-a.1)).add (hz.mul_const (b.2-a.2))
  convert h using 1
  · rfl
  · simp [Fin.sum_univ_succ,Fyy_diff,Fyz_diff,Fzz_diff,mixed_partials,
      familyYY,familyYZ,familyZZ]
    ring

theorem family_strong_convex {q : ℝ} (hq : q ∈ radiusBox)
    {a b : Pose} (ha : a ∈ poseBox) (hb : b ∈ poseBox) :
    familyValue q a+familyY q a*(b.1-a.1)+familyZ q a*(b.2-a.2)+
      ((b.1-a.1)^2+(b.2-a.2)^2)/8 ≤ familyValue q b := by
  have hcurv := curvature_tangent (l:=0) (u:=1) (x:=1) (t:=0)
    (f:=fun s => familyValue q (segment a b s))
    (d:=fun s => familyY q (segment a b s)*(b.1-a.1)+
      familyZ q (segment a b s)*(b.2-a.2))
    (dd:=fun s => familyYY q (segment a b s)*(b.1-a.1)^2+
      2*familyYZ q (segment a b s)*(b.1-a.1)*(b.2-a.2)+
      familyZZ q (segment a b s)*(b.2-a.2)^2)
    (κ:=((b.1-a.1)^2+(b.2-a.2)^2)/4)
    (by norm_num) (by norm_num)
    (fun s hs => family_segment_first hq ha hb hs)
    (fun s hs => family_segment_second hq ha hb hs)
    (fun s hs => by
      obtain ⟨hA,hdet⟩ := hessian_data hq (segment_mem ha hb hs)
      exact quadratic_form_bound hA hdet _ _)
  have h0 : segment a b 0 = a := by simp [segment]
  have h1 : segment a b 1 = b := by simp [segment]
  simp only [h0,h1] at hcurv
  linarith

theorem compact_poseBox : IsCompact poseBox := isCompact_Icc.prod isCompact_Icc

theorem minimum_exists (q : ℝ) :
    ∃ p ∈ poseBox, ∀ r ∈ poseBox, familyValue q p ≤ familyValue q r := by
  obtain ⟨p,hp,hmin⟩ := compact_poseBox.exists_isMinOn ⟨trial,trial_mem⟩
    (family_continuous_pose q).continuousOn
  exact ⟨p,hp,hmin⟩

def minimizingPose (q : ℝ) : Pose := Classical.choose (minimum_exists q)
def minimumValue (q : ℝ) : ℝ := familyValue q (minimizingPose q)

theorem minimizingPose_mem (q : ℝ) : minimizingPose q ∈ poseBox :=
  (Classical.choose_spec (minimum_exists q)).1

theorem minimumValue_le (q : ℝ) {p : Pose} (hp : p ∈ poseBox) :
    minimumValue q ≤ familyValue q p :=
  (Classical.choose_spec (minimum_exists q)).2 p hp

theorem trial_gradients {q : ℝ} (hq : q ∈ radiusBox) :
    |familyY q trial| ≤ 1/5000 ∧ |familyZ q trial| ≤ 1/2500 := by
  have hq' : (7831/2000:ℝ) ≤ q ∧ q ≤ 9789/2500 := hq
  have hY := trialFy_bound ![q,trialY,trialZ] (by
    intro i; fin_cases i <;> norm_num [trialFyBox,QInterval.Mem,trialY,trialZ]
    exact hq')
  have hZ := trialFz_bound ![q,trialY,trialZ] (by
    intro i; fin_cases i <;> norm_num [trialFzBox,QInterval.Mem,trialY,trialZ]
    exact hq')
  change (-1/5000:ℝ) ≤ familyY q trial ∧ familyY q trial ≤ 1/5000 at hY
  change (-1/2500:ℝ) ≤ familyZ q trial ∧ familyZ q trial ≤ 1/2500 at hZ
  exact ⟨abs_le.mpr ⟨by linarith [hY.1],hY.2⟩,abs_le.mpr ⟨by linarith [hZ.1],hZ.2⟩⟩

theorem minimum_interior {q : ℝ} (hq : q ∈ radiusBox) :
    -(937/1000) < (minimizingPose q).1 ∧ (minimizingPose q).1 < -(179/200) ∧
    1/20 < (minimizingPose q).2 ∧ (minimizingPose q).2 < 81/1000 := by
  have hmin := minimumValue_le q trial_mem
  have hcurv := family_strong_convex hq trial_mem (minimizingPose_mem q)
  obtain ⟨hy,hz⟩ := trial_gradients hq
  have hy' := abs_le.mp hy
  have hz' := abs_le.mp hz
  have hdist : ((minimizingPose q).1-trial.1)^2+
      ((minimizingPose q).2-trial.2)^2 < 1/10000 := by
    dsimp [minimumValue] at hmin
    nlinarith [sq_nonneg ((minimizingPose q).1-trial.1+8*familyY q trial),
      sq_nonneg ((minimizingPose q).2-trial.2+8*familyZ q trial)]
  have hyclose : |(minimizingPose q).1-trial.1| < 1/100 := by
    rw [abs_lt]; constructor <;> nlinarith [sq_nonneg ((minimizingPose q).2-trial.2)]
  have hzclose : |(minimizingPose q).2-trial.2| < 1/100 := by
    rw [abs_lt]; constructor <;> nlinarith [sq_nonneg ((minimizingPose q).1-trial.1)]
  have hyc := abs_lt.mp hyclose
  have hzc := abs_lt.mp hzclose
  norm_num [trial,trialY,trialZ] at hyc hzc
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem family_partial_y {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun y => familyValue q (y,p.2)) (familyY q p) p.1 := by
  have h := Formula.hasDerivAt_partial FFormula 1 ![q,p.1,p.2] (family_regular hq hp).1
  rw [Fy_diff] at h
  have hfun : (fun t => FFormula.eval (Function.update ![q,p.1,p.2] 1 t)) =
      (fun y => familyValue q (y,p.2)) := by
    funext y
    simp only [familyValue]
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  rw [hfun] at h
  exact h

theorem family_partial_z {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun z => familyValue q (p.1,z)) (familyZ q p) p.2 := by
  have h := Formula.hasDerivAt_partial FFormula 2 ![q,p.1,p.2] (family_regular hq hp).1
  rw [Fz_diff] at h
  have hfun : (fun t => FFormula.eval (Function.update ![q,p.1,p.2] 2 t)) =
      (fun z => familyValue q (p.1,z)) := by
    funext z
    simp only [familyValue]
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  rw [hfun] at h
  exact h

theorem family_partial_q {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun r => familyValue r p) (familyQ q p) q := by
  have h := Formula.hasDerivAt_partial FFormula 0 ![q,p.1,p.2] (family_regular hq hp).1
  rw [Fq_diff] at h
  have hfun : (fun t => FFormula.eval (Function.update ![q,p.1,p.2] 0 t)) =
      (fun r => familyValue r p) := by
    funext r
    simp only [familyValue]
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  rw [hfun] at h
  exact h

theorem minimizingPose_stationary {q : ℝ} (hq : q ∈ radiusBox) :
    familyY q (minimizingPose q)=0 ∧ familyZ q (minimizingPose q)=0 := by
  have hp := minimizingPose_mem q
  obtain ⟨hyL,hyU,hzL,hzU⟩ := minimum_interior hq
  have hymin : IsMinOn (fun y => familyValue q (y,(minimizingPose q).2))
      (Icc (-(937/1000)) (-(179/200))) (minimizingPose q).1 := by
    intro y hy
    exact minimumValue_le q ⟨hy,hp.2⟩
  have hzmin : IsMinOn (fun z => familyValue q ((minimizingPose q).1,z))
      (Icc (1/20) (81/1000)) (minimizingPose q).2 := by
    intro z hz
    exact minimumValue_le q ⟨hp.1,hz⟩
  exact ⟨(hymin.isLocalMin (Icc_mem_nhds hyL hyU)).hasDerivAt_eq_zero
      (family_partial_y hq hp),
    (hzmin.isLocalMin (Icc_mem_nhds hzL hzU)).hasDerivAt_eq_zero
      (family_partial_z hq hp)⟩

theorem family_radius_difference {q r : ℝ} (hq : q ∈ radiusBox) (hr : r ∈ radiusBox)
    (hqr : q ≤ r) {p : Pose} (hp : p ∈ poseBox) :
    -4*(r-q) ≤ familyValue r p-familyValue q p ∧
      familyValue r p-familyValue q p ≤ -3*(r-q) := by
  have hanti := antiOn_of_hasDeriv_nonpos (l:=7831/2000) (u:=9789/2500)
    (f:=fun x => familyValue x p+3*x) (d:=fun x => familyQ x p+3)
    (by exact ((family_continuous.comp (continuous_id.prodMk continuous_const)).add
      (continuous_const.mul continuous_id)).continuousOn)
    (fun x hx => by
      convert (family_partial_q ⟨hx.1.le,hx.2.le⟩ hp).fun_add
        ((hasDerivAt_id' x).const_mul 3) using 1; ring)
    (fun x hx => by linarith [(family_q_bound ⟨hx.1.le,hx.2.le⟩ hp).2])
  have hmono := monoOn_of_hasDeriv_nonneg (l:=7831/2000) (u:=9789/2500)
    (f:=fun x => familyValue x p+4*x) (d:=fun x => familyQ x p+4)
    (by exact ((family_continuous.comp (continuous_id.prodMk continuous_const)).add
      (continuous_const.mul continuous_id)).continuousOn)
    (fun x hx => by
      convert (family_partial_q ⟨hx.1.le,hx.2.le⟩ hp).fun_add
        ((hasDerivAt_id' x).const_mul 4) using 1; ring)
    (fun x hx => by linarith [(family_q_bound ⟨hx.1.le,hx.2.le⟩ hp).1])
  have h₁ := hanti hq hr hqr
  have h₂ := hmono hq hr hqr
  dsimp only at h₁ h₂
  constructor <;> linarith

theorem minimum_radius_difference {q r : ℝ} (hq : q ∈ radiusBox) (hr : r ∈ radiusBox)
    (hqr : q ≤ r) :
    -4*(r-q) ≤ minimumValue r-minimumValue q ∧
      minimumValue r-minimumValue q ≤ -3*(r-q) := by
  have h₁ := family_radius_difference hq hr hqr (minimizingPose_mem q)
  have h₂ := family_radius_difference hq hr hqr (minimizingPose_mem r)
  have h₃ := minimumValue_le r (minimizingPose_mem q)
  have h₄ := minimumValue_le q (minimizingPose_mem r)
  dsimp [minimumValue] at *
  constructor <;> linarith

theorem minimum_continuous : ContinuousOn minimumValue radiusBox := by
  have hlip : LipschitzWith (4:NNReal) (fun q : radiusBox => minimumValue q) := by
    apply LipschitzWith.of_dist_le_mul
    intro q r
    rcases le_total (q:ℝ) (r:ℝ) with h | h
    · have hh := minimum_radius_difference q.property r.property h
      simp only [Real.dist_eq,Subtype.dist_eq,NNReal.coe_ofNat]
      rw [abs_of_nonpos (by linarith : (q:ℝ)-(r:ℝ) ≤ 0)]
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    · have hh := minimum_radius_difference r.property q.property h
      simp only [Real.dist_eq,Subtype.dist_eq,NNReal.coe_ofNat]
      rw [abs_of_nonneg (by linarith : 0 ≤ (q:ℝ)-(r:ℝ))]
      exact abs_le.mpr ⟨by linarith,by linarith⟩
  exact continuousOn_iff_continuous_domRestrict.mpr hlip.continuous

theorem minimum_trial_lower {q : ℝ} (hq : q ∈ radiusBox) :
    familyValue q trial-2*(familyY q trial)^2-2*(familyZ q trial)^2 ≤ minimumValue q := by
  have h := family_strong_convex hq trial_mem (minimizingPose_mem q)
  dsimp [minimumValue]
  nlinarith [sq_nonneg ((minimizingPose q).1-trial.1+4*familyY q trial),
    sq_nonneg ((minimizingPose q).2-trial.2+4*familyZ q trial)]

theorem minimum_endpoint_signs :
    0 < minimumValue (7831/2000) ∧ minimumValue (9789/2500) < 0 := by
  have hL := lowerTest_bound ![7831/2000,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [lowerTestBox,QInterval.Mem,trialY,trialZ])
  have hU := upperTest_bound ![9789/2500,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [upperTestBox,QInterval.Mem,trialY,trialZ])
  have hcurv := minimum_trial_lower (q:=7831/2000) (by norm_num [radiusBox])
  obtain ⟨hy,hz⟩ := trial_gradients (q:=7831/2000) (by norm_num [radiusBox])
  have hy' := abs_le.mp hy
  have hz' := abs_le.mp hz
  have hupper := minimumValue_le (9789/2500) trial_mem
  change (1/8000:ℝ) ≤ familyValue (7831/2000) trial ∧ _ at hL
  change _ ∧ familyValue (9789/2500) trial ≤ (-1/5000) at hU
  constructor <;> nlinarith

theorem unique_minimum_zero : ∃! q : ℝ, q ∈ radiusBox ∧ minimumValue q=0 := by
  have hs := minimum_endpoint_signs
  have hcont : ContinuousOn (fun q => -minimumValue q) radiusBox := minimum_continuous.neg
  obtain ⟨q,hq,hzero⟩ := intermediate_value_Icc (by norm_num : (7831/2000:ℝ) ≤ 9789/2500)
    hcont ⟨show -minimumValue (7831/2000) ≤ 0 by linarith [hs.1],
      show 0 ≤ -minimumValue (9789/2500) by linarith [hs.2]⟩
  dsimp only at hzero
  refine ⟨q,⟨hq,by linarith⟩,?_⟩
  intro r hr
  rcases lt_trichotomy r q with h | h | h
  · have hb := (minimum_radius_difference hr.1 hq h.le).2
    linarith [hr.2]
  · exact h
  · have hb := (minimum_radius_difference hq hr.1 h.le).2
    linarith [hr.2]

def qStar : ℝ := Classical.choose unique_minimum_zero
def sharpPose : Pose := minimizingPose qStar

theorem qStar_mem : qStar ∈ radiusBox := (Classical.choose_spec unique_minimum_zero).1.1
theorem minimum_qStar : minimumValue qStar=0 := (Classical.choose_spec unique_minimum_zero).1.2
theorem sharpPose_stationary : familyY qStar sharpPose=0 ∧ familyZ qStar sharpPose=0 :=
  minimizingPose_stationary qStar_mem
theorem sharpPose_value : familyValue qStar sharpPose=0 := minimum_qStar

end SquaresInCircles.Eight.Stationary
end
end
end

section
/-!
## The envelope in the tilt and the uniqueness of the stationary chain

The general part (`EnvelopeGeometry`): two strict local minima of a continuous function enclose
an interior local maximum. So if every critical point of a function in an open interval is a
strict local minimum, there is at most one (`critical_unique_of_strict_minimum`), and it is the
minimum on the closed interval (`critical_is_global_minimum`); a positive second derivative makes
a critical point a strict minimum (`strictMinimum_of_positive_second_derivative`). If
`G(t, u) = 0` has a nonzero position derivative and a root `g t` that is unique in an open window
near `t`, then `g` is the implicit function, hence `C²` (`contDiffAt_of_unique_root`), with slope
`-G_t/G_u` (`implicit_root_derivative`).

On the window `[87/100, 11/10]` the four radicals stay positive for every `q` of the strip
(`window_bounds`). At every tilt with `0 ≤ s/c ≤ 1/5`, `positionHalf` is negative at `87/100`
(`comparison_position_negative`) and exceeds `c/4` at `11/10` (`upper_position_positive`), so it
vanishes inside, and by the strict convexity of `Convexity.lean` that root is the global position
minimum (`windowMinimizer_geometric`). `positionEnvelope q t` is the minimum over the window at
the tilt `t`; it is continuous and decreases with the radius faster than `q`
(`positionEnvelope_radius_decrease`). On `[1, 11/10]` the cross product of the position and tilt
derivatives of `(k₁, k₂)` is a negative quadratic form in `(c, s)`, so a critical point in the
window has `u < 1` and is a critical point of the strip of `CriticalHessian.lean`
(`windowMinimizer_isStripCritical`).

On the tilt interval `0 < t < arctan (1/5)` the position minimum is the implicit root of
`F_u = 0`, where `F` is the defect, so the envelope `M(t)` has `M' = F_t` and
`M'' = F_tt - F_tu²/F_uu`, which is positive at a critical point by the Hessian bound. Hence every
critical tilt is a strict minimum, there is at most one (`positionEnvelope_critical_unique`), and
it is the minimum on the closed interval (`positionEnvelope_critical_global_minimum`).

A stationary chain `d` gives the tilt `t = 2 arctan z` in `(0, arctan (1/5))`, where the envelope
`M(d.q, ·)` vanishes and is critical, so `M(d.q, ·) ≥ 0` on the closed tilt interval. If two
stationary chains had radii `q₀ < q₁`, the radius decrease would give
`0 ≤ M(q₁, t₀) < M(q₀, t₀) - (q₁ - q₀) < 0`; so the radii agree, then the critical tilts, then the
positions, and the chains are equal (`stationary_chain_unique`). `System.lean` uses this for
the uniqueness of the stationary configuration.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SquaresInCircles.Eight.Stationary.EnvelopeGeometry

/-! ### Functions whose critical points are strict minima -/

/-- `f x < f y` for every `y ≠ x` in an open interval about `x`. -/
def StrictMinimum (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε>0, ∀ y∈Ioo (x-ε) (x+ε), y≠x → f x<f y

/-- The strict second-derivative test. -/
theorem strictMinimum_of_positive_second_derivative {f : ℝ → ℝ} {a b x d : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : DifferentiableOn ℝ f (Ioo a b)) (hx : x∈Ioo a b)
    (hzero : deriv f x=0) (hsecond : HasDerivAt (deriv f) d x) (hdpos : 0<d) :
    StrictMinimum f x := by
  have hsign : ∀ᶠ y in 𝓝 x, SignType.sign (deriv f y)=SignType.sign (y-x) :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos (by rw [hsecond.deriv]; exact hdpos) hzero
  obtain ⟨ε,hε,hnear⟩ := Metric.eventually_nhds_iff.mp hsign
  let δ : ℝ := min ε (min (x-a) (b-x))
  have hδ : 0<δ := lt_min_iff.mpr ⟨hε,lt_min_iff.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩⟩
  have hδε : δ≤ε := min_le_left _ _
  have hδa : δ≤x-a := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ≤b-x := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,hδ,?_⟩
  intro y hy hyx
  have hya : a<y := by linarith [hy.1]
  have hyb : y<b := by linarith [hy.2]
  have hsign' (z : ℝ) (hz : z∈Ioo (x-δ) (x+δ)) :
      SignType.sign (deriv f z)=SignType.sign (z-x) := by
    apply hnear
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith [hz.1,hz.2]
  rcases lt_or_gt_of_ne hyx with hyx | hxy
  · have hsub : Icc y x ⊆ Icc a b := by
      intro z hz
      exact ⟨hya.le.trans hz.1,hz.2.trans hx.2.le⟩
    have hsub' : Ioo y x ⊆ Ioo a b := by
      intro z hz
      exact ⟨hya.trans hz.1,hz.2.trans hx.2⟩
    obtain ⟨z,hz,he⟩ := exists_deriv_eq_slope f hyx (hc.mono hsub) (hd.mono hsub')
    have hsg := hsign' z ⟨by linarith [hy.1,hz.1],by linarith [hz.2]⟩
    have hdz : deriv f z<0 := by
      rw [sign_neg (sub_neg.mpr hz.2)] at hsg
      exact sign_eq_neg_one_iff.mp hsg
    rw [he] at hdz
    have hnum : f x-f y<0 := by
      simpa using (div_lt_iff₀ (sub_pos.mpr hyx)).mp hdz
    linarith
  · have hsub : Icc x y ⊆ Icc a b := by
      intro z hz
      exact ⟨hx.1.le.trans hz.1,hz.2.trans hyb.le⟩
    have hsub' : Ioo x y ⊆ Ioo a b := by
      intro z hz
      exact ⟨hx.1.trans hz.1,hz.2.trans hyb⟩
    obtain ⟨z,hz,he⟩ := exists_deriv_eq_slope f hxy (hc.mono hsub) (hd.mono hsub')
    have hsg := hsign' z ⟨by linarith [hz.1],by linarith [hy.2,hz.2]⟩
    have hdz : 0<deriv f z := by
      rw [sign_pos (sub_pos.mpr hz.1)] at hsg
      exact sign_eq_one_iff.mp hsg
    rw [he] at hdz
    have hnum : 0<f y-f x := by
      simpa using (lt_div_iff₀ (sub_pos.mpr hxy)).mp hdz
    linarith

theorem StrictMinimum.right_witness {f : ℝ → ℝ} {x y : ℝ}
    (h : StrictMinimum f x) (hxy : x<y) :
    ∃ z∈Ioo x y, f x<f z := by
  obtain ⟨ε,hε,hf⟩ := h
  have hbound : x<min y (x+ε) := lt_min_iff.mpr ⟨hxy,by linarith⟩
  obtain ⟨z,hxz,hzu⟩ := exists_between hbound
  have hzy : z<y := lt_of_lt_of_le hzu (min_le_left _ _)
  have hze : z<x+ε := lt_of_lt_of_le hzu (min_le_right _ _)
  exact ⟨z,⟨hxz,hzy⟩,hf z ⟨by linarith,hze⟩ (ne_of_gt hxz)⟩

theorem StrictMinimum.left_witness {f : ℝ → ℝ} {x y : ℝ}
    (h : StrictMinimum f x) (hyx : y<x) :
    ∃ z∈Ioo y x, f x<f z := by
  obtain ⟨ε,hε,hf⟩ := h
  have hbound : max y (x-ε)<x := max_lt_iff.mpr ⟨hyx,by linarith⟩
  obtain ⟨z,hlz,hzx⟩ := exists_between hbound
  have hyz : y<z := lt_of_le_of_lt (le_max_left _ _) hlz
  have hez : x-ε<z := lt_of_le_of_lt (le_max_right _ _) hlz
  exact ⟨z,⟨hyz,hzx⟩,hf z ⟨hez,by linarith⟩ (ne_of_lt hzx)⟩

/-- A point above both ends of an interval forces an interior maximum. -/
theorem point_above_endpoints_forces_interior_maximum {f : ℝ → ℝ} {x y u : ℝ}
    (hxy : x<y) (hc : ContinuousOn f (Icc x y)) (hu : u∈Icc x y)
    (hux : f x<f u) (huy : f y<f u) :
    ∃ z∈Ioo x y, IsMaxOn f (Icc x y) z ∧ IsLocalMax f z := by
  obtain ⟨z,hz,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc x y).Nonempty from ⟨x,le_rfl,hxy.le⟩) hc
  have hzx : z≠x := by
    intro he
    have hh := hmax hu
    rw [he] at hh
    exact (not_lt_of_ge hh) hux
  have hzy : z≠y := by
    intro he
    have hh := hmax hu
    rw [he] at hh
    exact (not_lt_of_ge hh) huy
  have hxz : x<z := lt_of_le_of_ne hz.1 hzx.symm
  have hzy' : z<y := lt_of_le_of_ne hz.2 hzy
  exact ⟨z,⟨hxz,hzy'⟩,hmax,hmax.isLocalMax (Icc_mem_nhds hxz hzy')⟩

/-- Two strict minima enclose an interior maximum. -/
theorem strict_minima_force_interior_maximum {f : ℝ → ℝ} {x y : ℝ}
    (hxy : x<y) (hc : ContinuousOn f (Icc x y))
    (hx : StrictMinimum f x) (hy : StrictMinimum f y) :
    ∃ z∈Ioo x y, IsMaxOn f (Icc x y) z ∧ IsLocalMax f z := by
  obtain ⟨u,hu,hfu⟩ := hx.right_witness hxy
  obtain ⟨v,hv,hfv⟩ := hy.left_witness hxy
  obtain ⟨z,hz,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc x y).Nonempty from ⟨x,le_rfl,hxy.le⟩) hc
  have hzx : z≠x := by
    intro he
    have hh := hmax (show u∈Icc x y from ⟨hu.1.le,hu.2.le⟩)
    rw [he] at hh
    exact (not_lt_of_ge hh) hfu
  have hzy : z≠y := by
    intro he
    have hh := hmax (show v∈Icc x y from ⟨hv.1.le,hv.2.le⟩)
    rw [he] at hh
    exact (not_lt_of_ge hh) hfv
  have hxz : x<z := lt_of_le_of_ne hz.1 hzx.symm
  have hzy' : z<y := lt_of_le_of_ne hz.2 hzy
  exact ⟨z,⟨hxz,hzy'⟩,hmax,hmax.isLocalMax (Icc_mem_nhds hxz hzy')⟩

/-- If every critical point is a strict minimum, there is at most one. -/
theorem critical_unique_of_strict_minimum {f : ℝ → ℝ} {a b x y : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hmin : ∀ z∈Ioo a b, deriv f z=0 → StrictMinimum f z)
    (hx : x∈Ioo a b) (hy : y∈Ioo a b)
    (hxd : deriv f x=0) (hyd : deriv f y=0) : x=y := by
  have himpossible (u v : ℝ) (hu : u∈Ioo a b) (hv : v∈Ioo a b)
      (hud : deriv f u=0) (hvd : deriv f v=0) (huv : u<v) : False := by
    have hsub : Icc u v ⊆ Icc a b := by
      intro z hz
      exact ⟨hu.1.le.trans hz.1,hz.2.trans hv.2.le⟩
    obtain ⟨z,hz,hmax,hloc⟩ := strict_minima_force_interior_maximum huv
      (hc.mono hsub) (hmin u hu hud) (hmin v hv hvd)
    have hzab : z∈Ioo a b := ⟨hu.1.trans hz.1,hz.2.trans hv.2⟩
    have hzmin := hmin z hzab hloc.deriv_eq_zero
    obtain ⟨w,hw,hfw⟩ := hzmin.right_witness hz.2
    have hwuv : w∈Icc u v := ⟨(hz.1.trans hw.1).le,hw.2.le⟩
    exact (not_lt_of_ge (hmax hwuv)) hfw
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact False.elim (himpossible x y hx hy hxd hyd hxy)
  · exact hxy
  · exact False.elim (himpossible y x hy hx hyd hxd hyx)

/-- If every critical point is a strict minimum, each is the strict minimum on the closed
interval. -/
theorem critical_is_strict_global_minimum {f : ℝ → ℝ} {a b x : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hmin : ∀ z∈Ioo a b, deriv f z=0 → StrictMinimum f z)
    (hx : x∈Ioo a b) (hxd : deriv f x=0) :
    ∀ y∈Icc a b, y≠x → f x<f y := by
  intro y hy hyx
  by_contra! hle
  rcases lt_or_gt_of_ne hyx with hyx | hxy
  · obtain ⟨u,hu,hfu⟩ := (hmin x hx hxd).left_witness hyx
    have hsub : Icc y x ⊆ Icc a b := by
      intro z hz
      exact ⟨hy.1.trans hz.1,hz.2.trans hx.2.le⟩
    obtain ⟨z,hz,hmax,hloc⟩ := point_above_endpoints_forces_interior_maximum
      hyx (hc.mono hsub) ⟨hu.1.le,hu.2.le⟩ (hle.trans_lt hfu) hfu
    have hzab : z∈Ioo a b := ⟨hy.1.trans_lt hz.1,hz.2.trans hx.2⟩
    obtain ⟨w,hw,hfw⟩ := (hmin z hzab hloc.deriv_eq_zero).right_witness hz.2
    have hwsub : w∈Icc y x := ⟨(hz.1.trans hw.1).le,hw.2.le⟩
    exact (not_lt_of_ge (hmax hwsub)) hfw
  · obtain ⟨u,hu,hfu⟩ := (hmin x hx hxd).right_witness hxy
    have hsub : Icc x y ⊆ Icc a b := by
      intro z hz
      exact ⟨hx.1.le.trans hz.1,hz.2.trans hy.2⟩
    obtain ⟨z,hz,hmax,hloc⟩ := point_above_endpoints_forces_interior_maximum
      hxy (hc.mono hsub) ⟨hu.1.le,hu.2.le⟩ hfu (hle.trans_lt hfu)
    have hzab : z∈Ioo a b := ⟨hx.1.trans hz.1,hz.2.trans_le hy.2⟩
    obtain ⟨w,hw,hfw⟩ := (hmin z hzab hloc.deriv_eq_zero).right_witness hz.2
    have hwsub : w∈Icc x y := ⟨(hz.1.trans hw.1).le,hw.2.le⟩
    exact (not_lt_of_ge (hmax hwsub)) hfw

theorem critical_is_global_minimum {f : ℝ → ℝ} {a b x : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hmin : ∀ z∈Ioo a b, deriv f z=0 → StrictMinimum f z)
    (hx : x∈Ioo a b) (hxd : deriv f x=0) :
    ∀ y∈Icc a b, f x≤f y := by
  intro y hy
  by_cases he : y=x
  · rw [he]
  · exact (critical_is_strict_global_minimum hc hmin hx hxd y hy he).le

/-! ### Implicit roots -/

/-- The linear map `(v₁, v₂) ↦ dt v₁ + du v₂`. -/
def pairDerivative (dt du : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  dt • ContinuousLinearMap.fst ℝ ℝ ℝ+du • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem pairDerivative_apply (dt du : ℝ) (v : ℝ × ℝ) :
    pairDerivative dt du v=dt*v.1+du*v.2 := by
  simp [pairDerivative,smul_eq_mul]

/-- The differential of a jointly differentiable function of two variables is given by its two
partial derivatives. -/
theorem pair_hasFDerivAt {H : ℝ × ℝ → ℝ} {t u dt du : ℝ}
    (hH : DifferentiableAt ℝ H (t,u))
    (ht : HasDerivAt (fun x => H (x,u)) dt t)
    (hu : HasDerivAt (fun y => H (t,y)) du u) :
    HasFDerivAt H (pairDerivative dt du) (t,u) := by
  have hdt : fderiv ℝ H (t,u) (1,0)=dt :=
    (hH.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk (hasDerivAt_const t u))).unique ht
  have hdu : fderiv ℝ H (t,u) (0,1)=du :=
    (hH.hasFDerivAt.comp_hasDerivAt u ((hasDerivAt_const u t).prodMk (hasDerivAt_id' u))).unique hu
  have he : fderiv ℝ H (t,u)=pairDerivative dt du := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hv : v=v.1 • ((1,0):ℝ × ℝ)+v.2 • ((0,1):ℝ × ℝ) := by
      ext <;> simp
    nth_rewrite 1 [hv]
    rw [map_add,map_smul,map_smul,hdt,hdu,pairDerivative_apply,smul_eq_mul,smul_eq_mul]
    ring
  rw [← he]
  exact hH.hasFDerivAt

/-- The restriction of `pairDerivative dt du` to the second coordinate is invertible when
`du ≠ 0`. -/
theorem pairDerivative_position_invertible {dt du : ℝ} (hu : du≠0) :
    ((pairDerivative dt du).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (1/du) • ContinuousLinearMap.id ℝ ℝ)
  · ext
    simp [hu]
  · ext
    simp [hu]

/-- A root that is unique in an open window is the implicit function, hence `C²`. -/
theorem contDiffAt_of_unique_root {G : ℝ × ℝ → ℝ} {g : ℝ → ℝ}
    {t : ℝ} {W : Set ℝ} {dt du : ℝ}
    (hG : ContDiffAt ℝ 2 G (t,g t))
    (hd : HasFDerivAt G (pairDerivative dt du) (t,g t)) (hdu : du≠0)
    (hW : IsOpen W) (hmem : g t∈W) (hzero : G (t,g t)=0)
    (hunique : ∀ᶠ x in 𝓝 t, ∀ y∈W, G (x,y)=0 → y=g x) :
    ContDiffAt ℝ 2 g t := by
  have hn : (2:ℕ∞ω)≠0 := by norm_num
  have hinv : (fderiv ℝ G (t,g t) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hd.fderiv]
    exact pairDerivative_position_invertible hdu
  let ψ : ℝ → ℝ := hG.implicitFunction hn hinv
  have hψ : ContDiffAt ℝ 2 ψ t := hG.contDiffAt_implicitFunction hn hinv
  have hψself : ψ t=g t := hG.implicitFunction_apply_self hn hinv
  have hψroot : ∀ᶠ x in 𝓝 t, G (x,ψ x)=0 := by
    simpa only [hzero] using hG.eventually_apply_implicitFunction hn hinv
  have hψmem : ∀ᶠ x in 𝓝 t, ψ x∈W :=
    hψ.continuousAt.eventually (hW.mem_nhds (by rw [hψself]; exact hmem))
  have he : g =ᶠ[𝓝 t] ψ := by
    filter_upwards [hψroot,hψmem,hunique] with x hx hm hu
    exact (hu (ψ x) hm hx).symm
  exact hψ.congr_of_eventuallyEq he

/-- Differentiating a root equation gives the slope of the root. -/
theorem implicit_root_derivative {G : ℝ × ℝ → ℝ} {g : ℝ → ℝ}
    {t dt du : ℝ} (hg : DifferentiableAt ℝ g t)
    (hG : HasFDerivAt G (pairDerivative dt du) (t,g t)) (hdu : du≠0)
    (hzero : ∀ᶠ x in 𝓝 t, G (x,g x)=0) :
    HasDerivAt g (-dt/du) t := by
  have hcomp : HasDerivAt (fun x => G (x,g x)) (pairDerivative dt du (1,deriv g t)) t :=
    hG.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk hg.hasDerivAt)
  have he := hcomp.unique ((hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq hzero)
  rw [pairDerivative_apply] at he
  have hslope : deriv g t= -dt/du := by
    field_simp
    linarith
  exact hslope ▸ hg.hasDerivAt

/-- At a position minimum the position derivative vanishes, so the envelope has the tilt partial as
its derivative. -/
theorem envelope_first_derivative {F : ℝ × ℝ → ℝ} {g : ℝ → ℝ}
    {t dt dg : ℝ} (hg : HasDerivAt g dg t)
    (hF : HasFDerivAt F (pairDerivative dt 0) (t,g t)) :
    HasDerivAt (fun x => F (x,g x)) dt t :=
  (hF.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk hg)).congr_deriv (by simp)

/-- Along the root `u' = -F_tu/F_uu`, the tilt partial has derivative the Schur complement
`F_tt - F_tu²/F_uu`. -/
theorem envelope_tilt_derivative {T : ℝ × ℝ → ℝ} {g : ℝ → ℝ}
    {t tt tu uu : ℝ} (hg : HasDerivAt g (-tu/uu) t)
    (hT : HasFDerivAt T (pairDerivative tt tu) (t,g t)) :
    HasDerivAt (fun x => T (x,g x)) (tt-tu^2/uu) t :=
  (hT.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk hg)).congr_deriv (by
    rw [pairDerivative_apply]
    ring)

/-- With `uu > 0` and `uu tt - tu² > 0` the Schur complement `tt - tu²/uu` is positive. -/
theorem schur_positive {tt tu uu : ℝ} (huu : 0<uu) (hdet : 0<uu*tt-tu^2) :
    0<tt-tu^2/uu := by
  have hh := (div_lt_iff₀ huu).mpr (show tu^2<tt*uu by nlinarith)
  linarith

end SquaresInCircles.Eight.Stationary.EnvelopeGeometry

namespace SquaresInCircles.Eight.Stationary.FiveCornerGeometry

open EnvelopeGeometry

/-! ### The window of position minima -/

/-- The window `[87/100, 11/10]` of positions. -/
def positionWindow : Set ℝ := Icc (87/100) (11/10)

/-- Rational bounds on the radicals in the window. -/
structure WindowBounds (q u : ℝ) : Prop where
  domain : Domain q u
  r_lower : 41/25<lowerRight q u
  U_lower : 1619/1000<topRight q u
  V_lower : 1237/1000<topLeft q u
  Y_lower : 1411/1000<topHeight q u
  v_pos : 0<lowerHeight q u
  w_lower : 1885/1000<lowerLeft q u

theorem WindowBounds.smoothDomain {q u : ℝ} (h : WindowBounds q u) (hq : q<4) :
    SmoothDomain q u :=
  ⟨h.domain,hq,by linarith [h.r_lower],by linarith [h.U_lower],
    by linarith [h.Y_lower],by linarith [h.w_lower]⟩

/-- The four radicals are positive in the window, for every `q` of the strip. -/
theorem window_bounds {q u : ℝ} (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hu : u∈positionWindow) : WindowBounds q u := by
  have hul : 87/100 ≤ u := hu.1
  have huu : u ≤ 11/10 := hu.2
  have hup : 0 ≤ u := by linarith
  have hA : 9/10 ≤ 2-u ∧ 2-u ≤ 113/100 := by constructor <;> linarith
  have hr : 41/25<lowerRight q u ∧ lowerRight q u<2 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg hup huu
      nlinarith
    · nlinarith [sq_nonneg u]
  have hU : 1619/1000<topRight q u ∧ topRight q u<1763/1000 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ 2-u) hA.2
      nlinarith
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 9/10) hA.1
      nlinarith
  have hV : 1237/1000<topLeft q u ∧ topLeft q u<1381/1000 := by
    dsimp [topLeft]
    constructor <;> linarith [hU.1,hU.2]
  have hY : 1411/1000<topHeight q u ∧ topHeight q u<2 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ topLeft q u) hV.2.le
      nlinarith
    · nlinarith [sq_nonneg (topLeft q u)]
  have hv : 0<lowerHeight q u ∧ lowerHeight q u<589/1000 := by
    dsimp [lowerHeight]
    constructor <;> linarith [hY.1,hY.2]
  have hw : 1885/1000<lowerLeft q u ∧ lowerLeft q u<2 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg hv.1.le hv.2.le
      nlinarith
    · nlinarith [sq_nonneg (lowerHeight q u)]
  exact ⟨domain_of_pos hup (by linarith [hr.1]) (by linarith [hU.1]) (by linarith [hY.1])
    (by linarith [hw.1]),hr.1,hU.1,hV.1,hY.1,hv.1,hw.1⟩

/-- Rational bounds at `u = 11/10`. -/
theorem upper_comparison_bounds {q : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500) :
    lowerRight q (11/10)<33/20 ∧ lowerHeight q (11/10)<47/100 ∧
    191/100<lowerLeft q (11/10) ∧ 0<slopeRatio q (11/10) ∧
    slopeRatio q (11/10)<21/50 ∧ 2/3<(11/10)/lowerRight q (11/10) ∧
    0<lowerHeight q (11/10)/lowerLeft q (11/10) ∧
    lowerHeight q (11/10)/lowerLeft q (11/10)<1/4 := by
  have hb := window_bounds hql hqu (u:=11/10) (by norm_num [positionWindow])
  have hr : 0<lowerRight q (11/10) := by linarith [hb.r_lower]
  have hru : lowerRight q (11/10)<33/20 := by
    have hh : (41/25:ℝ)<Real.sqrt (q-(11/10)^2) ∧ Real.sqrt (q-(11/10)^2)<33/20 := by
      apply sqrt_between (by norm_num) <;> nlinarith
    exact hh.2
  have hU : 1758/1000<topRight q (11/10) := by
    have hh : (1758/1000:ℝ)<Real.sqrt (q-(2-11/10)^2) ∧ Real.sqrt (q-(2-11/10)^2)<2 := by
      apply sqrt_between (by norm_num) <;> nlinarith
    exact hh.1
  have hV : topLeft q (11/10)<1242/1000 := by dsimp [topLeft]; linarith
  have hY : 153/100<topHeight q (11/10) := by
    have hs := square_mono_nonneg (by linarith [hb.V_lower] : 0 ≤ topLeft q (11/10)) hV.le
    have hh : (153/100:ℝ)<Real.sqrt (q-topLeft q (11/10)^2) ∧
        Real.sqrt (q-topLeft q (11/10)^2)<2 := by
      apply sqrt_between (by norm_num)
      · nlinarith
      · nlinarith [sq_nonneg (topLeft q (11/10))]
    exact hh.1
  have hv : lowerHeight q (11/10)<47/100 := by dsimp [lowerHeight]; linarith
  have hw : 191/100<lowerLeft q (11/10) := by
    have hs := square_mono_nonneg hb.v_pos.le hv.le
    have hh : (191/100:ℝ)<Real.sqrt (q-lowerHeight q (11/10)^2) ∧
        Real.sqrt (q-lowerHeight q (11/10)^2)<2 := by
      apply sqrt_between (by norm_num)
      · nlinarith
      · nlinarith [sq_nonneg (lowerHeight q (11/10))]
    exact hh.1
  have hUp : 0<topRight q (11/10) := by linarith
  have hYp : 0<topHeight q (11/10) := by linarith
  have hwp : 0<lowerLeft q (11/10) := by linarith
  have hp : 0<slopeRatio q (11/10) := by
    dsimp [slopeRatio]
    exact div_pos (mul_pos (by norm_num) (by linarith [hb.V_lower])) (mul_pos hUp hYp)
  have hpu : slopeRatio q (11/10)<21/50 := by
    have hprod := mul_le_mul hU.le hY.le (by norm_num : (0:ℝ) ≤ 153/100) hUp.le
    dsimp [slopeRatio]
    rw [div_lt_iff₀ (mul_pos hUp hYp)]
    nlinarith
  have hx : 2/3<(11/10)/lowerRight q (11/10) := by
    rw [lt_div_iff₀ hr]
    nlinarith
  have hyl : 0<lowerHeight q (11/10)/lowerLeft q (11/10) := div_pos hb.v_pos hwp
  have hyu : lowerHeight q (11/10)/lowerLeft q (11/10)<1/4 := by
    rw [div_lt_iff₀ hwp]
    linarith
  exact ⟨hru,hv,hw,hp,hpu,hx,hyl,hyu⟩

/-- `positionHalf > c/4` at `u = 11/10`. -/
theorem upper_position_positive {q c s : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    (1/4)*c<positionHalf q c s (11/10) := by
  have hb := window_bounds hql hqu (u:=11/10) (by norm_num [positionWindow])
  obtain ⟨hr,hv,hw,hp,hpu,hx,hy,hyu⟩ := upper_comparison_bounds hql hqu
  obtain ⟨_,hcu,hsu,hsc⟩ := small_tilt_bounds hc hs hunit ht
  obtain ⟨hk₁,hk₂⟩ := components_pos (by linarith) hb.domain hc hcu hs hsu
  have hcr := mul_le_mul_of_nonneg_left (show lowerRight q (11/10)-1 ≤ 13/20 by linarith) hc.le
  have hk₁l : 27/20 ≤ firstComponent q c s (11/10) := by
    dsimp [firstComponent]
    nlinarith
  have hcx := mul_lt_mul_of_pos_left hx hc
  have ha : (2/3)*c<positionA q c s (11/10) := by
    dsimp [positionA]
    have he : c*((11/10)/lowerRight q (11/10))=c*(11/10)/lowerRight q (11/10) := by ring
    nlinarith
  have hcv := mul_le_mul_of_nonneg_left hv.le hc.le
  have hsw := mul_nonneg hs (by linarith : 0 ≤ lowerLeft q (11/10)-1)
  have hk₂u : secondComponent q c s (11/10) ≤ 147/100 := by dsimp [secondComponent]; nlinarith
  have hsy := mul_le_mul_of_nonneg_left hyu.le hs
  have hB : positionB q c s (11/10) ≤ (21/20)*c := by
    dsimp [positionB]
    have he : s*(lowerHeight q (11/10)/lowerLeft q (11/10))=
      s*lowerHeight q (11/10)/lowerLeft q (11/10) := by ring
    nlinarith
  have hBp : 0 ≤ positionB q c s (11/10) := by
    have hm := div_nonneg (mul_nonneg hs hb.v_pos.le) (by linarith : (0:ℝ) ≤ lowerLeft q (11/10))
    rw [positionB]
    linarith
  have hbu : positionb q c s (11/10) ≤ (441/1000)*c := by
    have hm := mul_le_mul hpu.le hB hBp (by norm_num : (0:ℝ) ≤ 21/50)
    dsimp [positionb]
    nlinarith
  have hbp : 0 ≤ positionb q c s (11/10) := mul_nonneg hp.le hBp
  have hfirst := mul_lt_mul_of_pos_left ha hk₁
  have hfirst' := mul_le_mul_of_nonneg_right hk₁l (by positivity : 0 ≤ (2/3)*c)
  have hsecond := mul_le_mul hk₂u hbu hbp (by norm_num : (0:ℝ) ≤ 147/100)
  have he : positionHalf q c s (11/10)=
      firstComponent q c s (11/10)*positionA q c s (11/10)-
      secondComponent q c s (11/10)*positionb q c s (11/10) := by
    dsimp [positionHalf,positionA,positionb,positionB]
    ring
  rw [he]
  nlinarith

/-- The position derivative vanishes inside the window, at the global position minimum. -/
theorem window_stationary_exists {q c s : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    ∃ u∈Ioo (87/100) (11/10), positionHalf q c s u=0 ∧
      HasDerivAt (defect q c s) 0 u ∧
      ∀ v, Domain q v → defect q c s u ≤ defect q c s v := by
  have hl := comparison_position_negative hql hqu hc hs ht hunit
  change positionHalf q c s (87/100)<0 at hl
  have hr : 0<positionHalf q c s (11/10) := by linarith [upper_position_positive hql hqu hc hs hunit ht]
  have hcont : ContinuousOn (positionHalf q c s) (Icc (87/100) (11/10)) := by
    intro u hu
    have hd := position_second_deriv (c:=c) (s:=s)
      ((window_bounds hql hqu hu).smoothDomain (by linarith))
    exact ((hd.continuousAt.const_mul (1/2)).congr (Eventually.of_forall fun v => by
      show (1/2:ℝ)*(2*positionHalf q c s v)=positionHalf q c s v
      ring)).continuousWithinAt
  obtain ⟨u,hu,hzero⟩ := intermediate_value_Icc (by norm_num : (87/100:ℝ) ≤ 11/10)
    hcont ⟨hl.le,hr.le⟩
  have hul : 87/100<u := by
    by_contra! hh
    have he : u=87/100 := le_antisymm hh hu.1
    rw [he] at hzero
    linarith
  have huu : u<11/10 := by
    by_contra! hh
    have he : u=11/10 := le_antisymm hu.2 hh
    rw [he] at hzero
    linarith
  have hb := window_bounds hql hqu hu
  have hd := position_deriv (q:=q) (c:=c) (s:=s) (u:=u)
    (by linarith [hb.r_lower]) (by linarith [hb.U_lower])
    (by linarith [hb.Y_lower]) (by linarith [hb.w_lower])
  rw [hzero,mul_zero] at hd
  obtain ⟨hcu,hsu⟩ := unit_le_one hunit
  exact ⟨u,⟨hul,huu⟩,hzero,hd,
    stationary_global_minimum (by linarith) hc hcu hs hsu hb.domain hd⟩

theorem window_minimum_exists (q c s : ℝ) :
    ∃ u∈positionWindow, ∀ v∈positionWindow, defect q c s u ≤ defect q c s v := by
  obtain ⟨u,hu,hm⟩ := (isCompact_Icc : IsCompact positionWindow).exists_isMinOn
    (show positionWindow.Nonempty from ⟨1,by norm_num [positionWindow]⟩)
    (defect_continuous q c s).continuousOn
  exact ⟨u,hu,fun v hv => hm hv⟩

/-- A minimum of the defect over the window. -/
def windowMinimizer (q c s : ℝ) : ℝ := Classical.choose (window_minimum_exists q c s)

theorem windowMinimizer_mem (q c s : ℝ) : windowMinimizer q c s∈positionWindow :=
  (Classical.choose_spec (window_minimum_exists q c s)).1

theorem windowMinimizer_le (q c s : ℝ) {u : ℝ} (hu : u∈positionWindow) :
    defect q c s (windowMinimizer q c s) ≤ defect q c s u :=
  (Classical.choose_spec (window_minimum_exists q c s)).2 u hu

/-- The minimum over the window is unique. -/
theorem window_minimizer_unique {q c s u v : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1)
    (hu : u∈positionWindow) (hv : v∈positionWindow)
    (hmu : ∀ w∈positionWindow, defect q c s u ≤ defect q c s w)
    (hmv : ∀ w∈positionWindow, defect q c s v ≤ defect q c s w) : u=v := by
  by_contra hne
  obtain ⟨hcu,hsu⟩ := unit_le_one hunit
  have hm : (1/2)*u+(1/2)*v∈positionWindow := by
    constructor <;> linarith [hu.1,hu.2,hv.1,hv.2]
  have hj := defect_mix_strict (by linarith : q<4) (window_bounds hql hqu hu).domain
    (window_bounds hql hqu hv).domain hne hc hcu hs hsu
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2) (by norm_num)
  have h₁ := hmu _ hm
  have h₂ := hmv _ hm
  linarith

/-- The minimum over the window is interior and critical, and it is the global minimum on the
radical domain. -/
theorem windowMinimizer_geometric {q c s : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    windowMinimizer q c s∈Ioo (87/100) (11/10) ∧
    positionHalf q c s (windowMinimizer q c s)=0 ∧
    HasDerivAt (defect q c s) 0 (windowMinimizer q c s) ∧
    ∀ v, Domain q v → defect q c s (windowMinimizer q c s) ≤ defect q c s v := by
  obtain ⟨u,hu,hzero,hd,hm⟩ := window_stationary_exists hql hqu hc hs hunit ht
  have hu' : u∈positionWindow := ⟨hu.1.le,hu.2.le⟩
  have he : windowMinimizer q c s=u := window_minimizer_unique hql hqu hc hs hunit
    (windowMinimizer_mem q c s) hu' (fun v hv => windowMinimizer_le q c s hv)
    (fun v hv => hm v (window_bounds hql hqu hv).domain)
  rw [he]
  exact ⟨hu,hzero,hd,hm⟩

/-- Every critical position is the minimum over the window. -/
theorem windowMinimizer_eq_of_stationary {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5)
    (hu : Domain q u) (hd : HasDerivAt (defect q c s) 0 u) : windowMinimizer q c s=u := by
  obtain ⟨_,_,_,hm⟩ := windowMinimizer_geometric hql hqu hc hs hunit ht
  obtain ⟨hcu,hsu⟩ := unit_le_one hunit
  exact minimizer_unique (by linarith) hc hcu hs hsu
    (window_bounds hql hqu (windowMinimizer_mem q c s)).domain hu hm
    (stationary_global_minimum (by linarith) hc hcu hs hsu hu hd)

/-- The envelope `M(q, t)`: the minimum of the defect over the window at the tilt `t`. -/
def positionEnvelope (q t : ℝ) : ℝ :=
  sInf ((fun u => defect q (Real.cos t) (Real.sin t) u) '' positionWindow)

/-- The envelope is attained at `windowMinimizer`. -/
theorem positionEnvelope_eq (q t : ℝ) :
    positionEnvelope q t=defect q (Real.cos t) (Real.sin t)
      (windowMinimizer q (Real.cos t) (Real.sin t)) := by
  obtain ⟨u,hu,he,hm⟩ := (isCompact_Icc : IsCompact positionWindow).exists_sInf_image_eq_and_le
    (show positionWindow.Nonempty from ⟨1,by norm_num [positionWindow]⟩)
    (defect_continuous q (Real.cos t) (Real.sin t)).continuousOn
  change sInf (defect q (Real.cos t) (Real.sin t) '' Icc (87/100) (11/10))=_
  rw [he]
  exact le_antisymm (hm _ (windowMinimizer_mem _ _ _)) (windowMinimizer_le _ _ _ hu)

theorem positionEnvelope_continuous (q : ℝ) : Continuous (positionEnvelope q) := by
  apply (isCompact_Icc : IsCompact positionWindow).continuous_sInf
  change Continuous fun p : ℝ × ℝ => defect q (Real.cos p.1) (Real.sin p.1) p.2
  unfold defect firstComponent secondComponent lowerRight lowerLeft lowerHeight topHeight
    topLeft topRight upper
  fun_prop

/-- The envelope decreases with the radius faster than `q`. -/
theorem positionEnvelope_radius_decrease {q₀ q₁ t : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q₀) (hqu : q₁ ≤ 9789/2500) (hq : q₀<q₁)
    (hc : 0<Real.cos t) (hs : 0 ≤ Real.sin t) :
    positionEnvelope q₁ t<positionEnvelope q₀ t-(q₁-q₀) := by
  have hu := windowMinimizer_mem q₀ (Real.cos t) (Real.sin t)
  have hdom := (window_bounds hql (by linarith : q₀ ≤ 9789/2500) hu).domain
  have hd := defect_radius_decrease hq (by linarith : q₁<4) hdom
    hc (Real.cos_le_one t) hs (Real.sin_le_one t)
  have hm := windowMinimizer_le q₁ (Real.cos t) (Real.sin t) hu
  rw [positionEnvelope_eq q₁ t,positionEnvelope_eq q₀ t]
  linarith

/-! ### Critical positions lie below one -/

/-- Rational bounds for `1 ≤ u ≤ 11/10`. -/
theorem right_window_bounds {q u : ℝ} (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hul : 1 ≤ u) (huu : u ≤ 11/10) :
    1<lowerRight q u ∧ lowerRight q u<171/100 ∧ 19/10<lowerLeft q u ∧
    0<lowerHeight q u ∧ 0<slopeRatio q u ∧ slopeRatio q u<21/40 ∧
    slopeRatio q u*lowerRight q u<lowerLeft q u-1 := by
  have hw : u∈positionWindow := ⟨by linarith,huu⟩
  have hb := window_bounds hql hqu hw
  have hur := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 1) hul
  have hru : lowerRight q u<171/100 := by
    have hh : (41/25:ℝ)<Real.sqrt (q-u^2) ∧ Real.sqrt (q-u^2)<171/100 := by
      apply sqrt_between (by norm_num)
      · have hs := square_mono_nonneg (by linarith : 0 ≤ u) huu
        nlinarith
      · nlinarith
    exact hh.2
  have hA : 9/10 ≤ 2-u ∧ 2-u ≤ 1 := by constructor <;> linarith
  have hU : 17/10<topRight q u := by
    have hs := square_mono_nonneg (by linarith : 0 ≤ 2-u) hA.2
    have hh : (17/10:ℝ)<Real.sqrt (q-(2-u)^2) ∧ Real.sqrt (q-(2-u)^2)<2 := by
      apply sqrt_between (by norm_num)
      · nlinarith
      · nlinarith [sq_nonneg (2-u)]
    exact hh.1
  have hV : topLeft q u<13/10 := by dsimp [topLeft]; linarith
  have hY : 147/100<topHeight q u := by
    have hs := square_mono_nonneg (by linarith [hb.V_lower] : 0 ≤ topLeft q u) hV.le
    have hh : (147/100:ℝ)<Real.sqrt (q-topLeft q u^2) ∧ Real.sqrt (q-topLeft q u^2)<2 := by
      apply sqrt_between (by norm_num)
      · nlinarith
      · nlinarith [sq_nonneg (topLeft q u)]
    exact hh.1
  have hv : lowerHeight q u<53/100 := by dsimp [lowerHeight]; linarith
  have hwl : 19/10<lowerLeft q u := by
    have hs := square_mono_nonneg hb.v_pos.le hv.le
    have hh : (19/10:ℝ)<Real.sqrt (q-lowerHeight q u^2) ∧ Real.sqrt (q-lowerHeight q u^2)<2 := by
      apply sqrt_between (by norm_num)
      · nlinarith
      · nlinarith [sq_nonneg (lowerHeight q u)]
    exact hh.1
  have hUp : 0<topRight q u := by linarith
  have hYp : 0<topHeight q u := by linarith
  have hp : 0<slopeRatio q u := by
    dsimp [slopeRatio]
    exact div_pos (mul_pos (by linarith) (by linarith [hb.V_lower])) (mul_pos hUp hYp)
  have hpu : slopeRatio q u<21/40 := by
    have hprod := mul_le_mul hU.le hY.le (by norm_num : (0:ℝ) ≤ 147/100) hUp.le
    have hnum := mul_le_mul hA.2 hV.le (by linarith [hb.V_lower]) (by norm_num : (0:ℝ) ≤ 1)
    dsimp [slopeRatio]
    rw [div_lt_iff₀ (mul_pos hUp hYp)]
    nlinarith
  have hpr : slopeRatio q u*lowerRight q u<lowerLeft q u-1 := by
    have hm := mul_le_mul hpu.le hru.le (by linarith [hb.r_lower]) (by norm_num : (0:ℝ) ≤ 21/40)
    nlinarith
  exact ⟨by linarith [hb.r_lower],hru,hwl,hb.v_pos,hp,hpu,hpr⟩

/-- The cross product of the position and tilt derivatives of `(k₁, k₂)` as a quadratic form in
`(c, s)`. -/
theorem tangent_cross_identity (r w u v p c s : ℝ) (hr : r≠0) (hw : w≠0) :
    (p*(c+s*v/w))*(s*(r-1)+c*u)-(s+c*u/r)*(c*(w-1)+s*v)=
      c^2*(u/r)*(p*r-w+1)+
      c*s*(p*(r-1)-(w-1)+u*v*(p/w-1/r))+
      s^2*(v/w)*(p*(r-1)-w) := by
  field_simp [hr,hw]
  ring

/-- On `[1, 11/10]` the cross product of the position and tilt derivatives of `(k₁, k₂)` is
negative. -/
theorem right_window_cross_negative {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hul : 1 ≤ u) (huu : u ≤ 11/10) (hc : 0<c) (hs : 0 ≤ s) :
    positionb q c s u*firstTilt q c s u+positionA q c s u*secondTilt q c s u<0 := by
  obtain ⟨hr,hru,hw,hv,hp,hpu,hpr⟩ := right_window_bounds hql hqu hul huu
  have hrp : 0<lowerRight q u := by linarith
  have hwp : 0<lowerLeft q u := by linarith
  have hu : 0<u := by linarith
  have hrw : lowerRight q u<lowerLeft q u := by linarith
  have hp₁ : slopeRatio q u<1 := by linarith
  have hP : slopeRatio q u*(lowerRight q u-1)<lowerLeft q u-1 := by
    have hm := mul_lt_mul_of_pos_right hp₁ (by linarith : 0<lowerRight q u-1)
    nlinarith
  have hratio : slopeRatio q u/lowerLeft q u<1/lowerRight q u := by
    apply (div_lt_div_iff₀ hwp hrp).2
    nlinarith
  have hC₀ : (u/lowerRight q u)*(slopeRatio q u*lowerRight q u-lowerLeft q u+1)<0 :=
    mul_neg_of_pos_of_neg (div_pos hu hrp) (by linarith)
  have hC₁ : slopeRatio q u*(lowerRight q u-1)-(lowerLeft q u-1)+
      u*lowerHeight q u*(slopeRatio q u/lowerLeft q u-1/lowerRight q u)<0 := by
    have hm := mul_neg_of_pos_of_neg (mul_pos hu hv) (sub_neg.mpr hratio)
    linarith
  have hC₂ : (lowerHeight q u/lowerLeft q u)*(slopeRatio q u*(lowerRight q u-1)-lowerLeft q u)<0 :=
    mul_neg_of_pos_of_neg (div_pos hv hwp) (by linarith)
  have h₀ := mul_neg_of_pos_of_neg (sq_pos_of_pos hc) hC₀
  have h₁ := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc.le hs) hC₁.le
  have h₂ := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s) hC₂.le
  have he := tangent_cross_identity (lowerRight q u) (lowerLeft q u) u (lowerHeight q u)
    (slopeRatio q u) c s (ne_of_gt hrp) (ne_of_gt hwp)
  dsimp [positionb,positionB,positionA,firstTilt,secondTilt]
  nlinarith

/-- A critical point in the window has `u < 1`. -/
theorem window_critical_below_one {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1)
    (hu : u∈positionWindow) (hp : positionHalf q c s u=0) (htilt : tiltFirst q c s u=0) :
    u<1 := by
  by_contra! hge
  have hcross := right_window_cross_negative hql hqu hge hu.2 hc hs
  have hb := window_bounds hql hqu hu
  obtain ⟨hcu,hsu⟩ := unit_le_one hunit
  have hk := (components_pos (by linarith : q<4) hb.domain hc hcu hs hsu).1
  have hzero : firstComponent q c s u*
      (positionb q c s u*firstTilt q c s u+positionA q c s u*secondTilt q c s u)=0 := by
    dsimp [positionHalf] at hp
    dsimp [tiltFirst] at htilt
    dsimp [positionA,positionb,positionB]
    linear_combination (slopeRatio q u*(c+s*lowerHeight q u/lowerLeft q u)/2)*htilt+
      secondTilt q c s u*hp
  have hn := mul_neg_of_pos_of_neg hk hcross
  linarith

/-- At a critical tilt the minimum over the window is a critical point of the strip. -/
theorem windowMinimizer_isStripCritical {q c s : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5)
    (hcritical : tiltFirst q c s (windowMinimizer q c s)=0) :
    StripCritical q c s (windowMinimizer q c s) := by
  obtain ⟨hu,hp,_,_⟩ := windowMinimizer_geometric hql hqu hc hs hunit ht
  have hupper := window_critical_below_one hql hqu hc hs hunit
    (windowMinimizer_mem q c s) hp hcritical
  exact ⟨⟨hql,hqu,hu.1.le,hupper.le⟩,hc,hs,hunit,ht,hp,hcritical⟩

/-! ### The envelope in the tilt -/

/-- The defect as a function of the tilt and the position. -/
def jointDefect (q : ℝ) (p : ℝ × ℝ) : ℝ :=
  defect q (Real.cos p.1) (Real.sin p.1) p.2
/-- The position derivative of the defect as a function of the tilt and the position. -/
def jointPosition (q : ℝ) (p : ℝ × ℝ) : ℝ :=
  2*positionHalf q (Real.cos p.1) (Real.sin p.1) p.2
/-- The tilt derivative of the defect as a function of the tilt and the position. -/
def jointTilt (q : ℝ) (p : ℝ × ℝ) : ℝ :=
  tiltFirst q (Real.cos p.1) (Real.sin p.1) p.2
/-- The position minimum at the tilt `t`. -/
def minimizingPosition (q t : ℝ) : ℝ :=
  windowMinimizer q (Real.cos t) (Real.sin t)
/-- The tilt interval `(0, arctan (1/5))`. -/
def tiltInterval : Set ℝ := Ioo 0 (Real.arctan (1/5))

theorem tiltInterval_bounds {t : ℝ} (ht : t∈tiltInterval) :
    0<Real.cos t ∧ 0<Real.sin t ∧ Real.sin t/Real.cos t<1/5 := by
  have hupper := Real.arctan_lt_pi_div_two (1/5:ℝ)
  have hmem : t∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [ht.1,ht.2,Real.pi_pos]
  have htan := Real.strictMonoOn_tan hmem (Real.arctan_mem_Ioo (1/5:ℝ)) ht.2
  rw [Real.tan_arctan,Real.tan_eq_sin_div_cos] at htan
  exact ⟨Real.cos_pos_of_mem_Ioo hmem,
    Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [hmem.2,Real.pi_pos]),htan⟩

private theorem upper_joint_contDiffAt {q : ℝ} {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f p) (hr : 0<upper q (f p)) :
    ContDiffAt ℝ 2 (fun x => upper q (f x)) p := by
  exact (contDiffAt_const.sub (hf.pow 2)).sqrt (ne_of_gt (Real.sqrt_pos.mp hr))

/-- The defect and its two partial derivatives are jointly `C²` where the radicals are
positive. -/
theorem SmoothDomain.joint_contDiffAt {q u : ℝ} (h : SmoothDomain q u) (t : ℝ) :
    ContDiffAt ℝ 2 (jointDefect q) (t,u) ∧
    ContDiffAt ℝ 2 (jointPosition q) (t,u) ∧
    ContDiffAt ℝ 2 (jointTilt q) (t,u) := by
  have dx : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.2) (t,u) := contDiffAt_snd
  have dc : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.cos p.1) (t,u) := contDiffAt_fst.cos
  have ds : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.sin p.1) (t,u) := contDiffAt_fst.sin
  have dr : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => lowerRight q p.2) (t,u) :=
    upper_joint_contDiffAt dx h.r_pos
  have dU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => topRight q p.2) (t,u) :=
    upper_joint_contDiffAt (contDiffAt_const.sub dx) h.U_pos
  have dV : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => topLeft q p.2) (t,u) :=
    contDiffAt_const.sub dU
  have dY : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => topHeight q p.2) (t,u) :=
    upper_joint_contDiffAt dV h.Y_pos
  have dv : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => lowerHeight q p.2) (t,u) :=
    contDiffAt_const.sub dY
  have dw : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => lowerLeft q p.2) (t,u) :=
    upper_joint_contDiffAt dv h.w_pos
  have dk₁ : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => firstComponent q (Real.cos p.1) (Real.sin p.1) p.2) (t,u) :=
    (contDiffAt_const.sub (dc.mul (dr.sub contDiffAt_const))).add (ds.mul dx)
  have dk₂ : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => secondComponent q (Real.cos p.1) (Real.sin p.1) p.2) (t,u) :=
    (contDiffAt_const.add (dc.mul dv)).sub (ds.mul (dw.sub contDiffAt_const))
  have dp : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => slopeRatio q p.2) (t,u) :=
    ((contDiffAt_const.sub dx).mul dV).div (dU.mul dY) (ne_of_gt (mul_pos h.U_pos h.Y_pos))
  have dA : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Real.sin p.1+Real.cos p.1*p.2/lowerRight q p.2) (t,u) :=
    ds.add ((dc.mul dx).div dr (ne_of_gt h.r_pos))
  have dB : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Real.cos p.1+Real.sin p.1*lowerHeight q p.2/lowerLeft q p.2) (t,u) :=
    dc.add ((ds.mul dv).div dw (ne_of_gt h.w_pos))
  have dkt₁ : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => firstTilt q (Real.cos p.1) (Real.sin p.1) p.2) (t,u) :=
    (ds.mul (dr.sub contDiffAt_const)).add (dc.mul dx)
  have dkt₂ : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => secondTilt q (Real.cos p.1) (Real.sin p.1) p.2) (t,u) :=
    (ds.neg.mul dv).sub (dc.mul (dw.sub contDiffAt_const))
  exact ⟨((dk₁.pow 2).add (dk₂.pow 2)).sub contDiffAt_const,
    contDiffAt_const.mul ((dk₁.mul dA).sub ((dk₂.mul dp).mul dB)),
    contDiffAt_const.mul ((dk₁.mul dkt₁).add (dk₂.mul dkt₂))⟩

theorem jointDefect_hasFDerivAt {q u : ℝ} (h : SmoothDomain q u) (t : ℝ) :
    HasFDerivAt (jointDefect q)
      (pairDerivative (tiltFirst q (Real.cos t) (Real.sin t) u)
        (2*positionHalf q (Real.cos t) (Real.sin t) u)) (t,u) :=
  pair_hasFDerivAt ((h.joint_contDiffAt t).1.differentiableAt (by norm_num))
    (defect_angle_deriv q u t)
    (position_deriv (c:=Real.cos t) (s:=Real.sin t) h.r_pos h.U_pos h.Y_pos h.w_pos)

theorem jointPosition_hasFDerivAt {q u : ℝ} (h : SmoothDomain q u) (t : ℝ) :
    HasFDerivAt (jointPosition q)
      (pairDerivative (mixedSecond q (Real.cos t) (Real.sin t) u)
        (positionSecond q (Real.cos t) (Real.sin t) u)) (t,u) :=
  pair_hasFDerivAt ((h.joint_contDiffAt t).2.1.differentiableAt (by norm_num))
    (mixed_angle_deriv q u t)
    (position_second_deriv (c:=Real.cos t) (s:=Real.sin t) h)

/-- The position derivative of the tilt partial is the mixed entry `mixedSecond`. -/
theorem tiltFirst_position_deriv {q c s u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (tiltFirst q c s) (mixedSecond q c s u) u := by
  obtain ⟨dr,_,_,_,dv,dw⟩ := radical_derivatives h.r_pos h.U_pos h.Y_pos h.w_pos
  obtain ⟨dk₁,dk₂⟩ := components_position_deriv (c:=c) (s:=s) h.r_pos h.U_pos h.Y_pos h.w_pos
  have dt₁ := ((dr.sub_const 1).const_mul s).fun_add ((hasDerivAt_id' u).const_mul c)
  have dt₂ := (dv.const_mul (-s)).fun_sub ((dw.sub_const 1).const_mul c)
  exact ((dk₁.fun_mul dt₁).fun_add (dk₂.fun_mul dt₂)).const_mul 2 |>.congr_deriv (by
    rw [mixedSecond,mixedNormal,positionA,positionb,positionB,firstTilt,secondTilt]
    ring)

theorem jointTilt_hasFDerivAt {q u : ℝ} (h : SmoothDomain q u) (t : ℝ) :
    HasFDerivAt (jointTilt q)
      (pairDerivative (tiltSecond q (Real.cos t) (Real.sin t) u)
        (mixedSecond q (Real.cos t) (Real.sin t) u)) (t,u) :=
  pair_hasFDerivAt ((h.joint_contDiffAt t).2.2.differentiableAt (by norm_num))
    (defect_angle_second_deriv q u t)
    (tiltFirst_position_deriv (c:=Real.cos t) (s:=Real.sin t) h)

theorem minimizingPosition_smoothDomain {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) :
    SmoothDomain q (minimizingPosition q t) :=
  (window_bounds hql hqu (windowMinimizer_mem q (Real.cos t) (Real.sin t))).smoothDomain
    (by linarith)

theorem minimizingPosition_root {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval) :
    jointPosition q (t,minimizingPosition q t)=0 := by
  obtain ⟨hc,hs,htan⟩ := tiltInterval_bounds ht
  have hp := (windowMinimizer_geometric hql hqu hc hs.le (Real.cos_sq_add_sin_sq t) htan.le).2.1
  dsimp [jointPosition,minimizingPosition]
  rw [hp,mul_zero]

/-- The position minimum is a `C²` function of the tilt. -/
theorem minimizingPosition_contDiffAt {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval) :
    ContDiffAt ℝ 2 (minimizingPosition q) t := by
  obtain ⟨hc,hs,htan⟩ := tiltInterval_bounds ht
  have hm := windowMinimizer_geometric hql hqu hc hs.le (Real.cos_sq_add_sin_sq t) htan.le
  have hdom := minimizingPosition_smoothDomain (t:=t) hql hqu
  apply contDiffAt_of_unique_root (hdom.joint_contDiffAt t).2.1
    (jointPosition_hasFDerivAt hdom t)
    (ne_of_gt (hdom.positionSecond_pos hc hs.le (Real.cos_sq_add_sin_sq t)))
    (W := Ioo (87/100) (11/10)) isOpen_Ioo hm.1 (minimizingPosition_root hql hqu ht)
  filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
  intro v hv hroot
  obtain ⟨hcx,hsx,htx⟩ := tiltInterval_bounds hx
  have hv' : v∈positionWindow := ⟨hv.1.le,hv.2.le⟩
  have hdomv := (window_bounds hql hqu hv').smoothDomain (by linarith)
  have hdv := position_deriv (c:=Real.cos x) (s:=Real.sin x)
    hdomv.r_pos hdomv.U_pos hdomv.Y_pos hdomv.w_pos
  have hz : 2*positionHalf q (Real.cos x) (Real.sin x) v=0 := hroot
  rw [hz] at hdv
  exact (windowMinimizer_eq_of_stationary hql hqu hcx hsx.le (Real.cos_sq_add_sin_sq x) htx.le
    hdomv.toDomain hdv).symm

/-- The slope of the position minimum is `-F_tu/F_uu`. -/
theorem minimizingPosition_hasDerivAt {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval) :
    HasDerivAt (minimizingPosition q)
      (-mixedSecond q (Real.cos t) (Real.sin t) (minimizingPosition q t)/
        positionSecond q (Real.cos t) (Real.sin t) (minimizingPosition q t)) t := by
  obtain ⟨hc,hs,htan⟩ := tiltInterval_bounds ht
  have hdom := minimizingPosition_smoothDomain (t:=t) hql hqu
  apply implicit_root_derivative
    ((minimizingPosition_contDiffAt hql hqu ht).differentiableAt (by norm_num))
    (jointPosition_hasFDerivAt hdom t)
    (ne_of_gt (hdom.positionSecond_pos hc hs.le (Real.cos_sq_add_sin_sq t)))
  filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
  exact minimizingPosition_root hql hqu hx

/-- `M' = F_t` at the position minimum. -/
theorem positionEnvelope_hasDerivAt {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval) :
    HasDerivAt (positionEnvelope q)
      (tiltFirst q (Real.cos t) (Real.sin t) (minimizingPosition q t)) t := by
  have hdom := minimizingPosition_smoothDomain (t:=t) hql hqu
  have hF := jointDefect_hasFDerivAt hdom t
  have hzero := minimizingPosition_root hql hqu ht
  change 2*positionHalf q (Real.cos t) (Real.sin t) (minimizingPosition q t)=0 at hzero
  rw [hzero] at hF
  have hh := envelope_first_derivative (minimizingPosition_hasDerivAt hql hqu ht) hF
  convert hh using 1
  funext x
  exact positionEnvelope_eq q x

/-- `M'' = F_tt - F_tu²/F_uu` at the position minimum. -/
theorem positionEnvelope_second_derivative {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval) :
    HasDerivAt (deriv (positionEnvelope q))
      (tiltSecond q (Real.cos t) (Real.sin t) (minimizingPosition q t)-
        mixedSecond q (Real.cos t) (Real.sin t) (minimizingPosition q t)^2/
          positionSecond q (Real.cos t) (Real.sin t) (minimizingPosition q t)) t := by
  have hdom := minimizingPosition_smoothDomain (t:=t) hql hqu
  have hh := envelope_tilt_derivative (minimizingPosition_hasDerivAt hql hqu ht)
    (jointTilt_hasFDerivAt hdom t)
  apply hh.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
  exact (positionEnvelope_hasDerivAt hql hqu hx).deriv

/-- Every critical tilt is a strict local minimum of the envelope. -/
theorem positionEnvelope_critical_strictMinimum {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval)
    (hzero : deriv (positionEnvelope q) t=0) :
    StrictMinimum (positionEnvelope q) t := by
  obtain ⟨hc,hs,htan⟩ := tiltInterval_bounds ht
  have hgrad := (positionEnvelope_hasDerivAt hql hqu ht).deriv
  have htilt : tiltFirst q (Real.cos t) (Real.sin t) (minimizingPosition q t)=0 := by
    linarith
  have hcritical := windowMinimizer_isStripCritical hql hqu hc hs.le (Real.cos_sq_add_sin_sq t) htan.le htilt
  have hdom := minimizingPosition_smoothDomain (t:=t) hql hqu
  have hdet := hcritical.hessian_pos
  dsimp only [hessianDeterminant] at hdet
  have hschur := schur_positive (hdom.positionSecond_pos hc hs.le (Real.cos_sq_add_sin_sq t)) hdet
  apply strictMinimum_of_positive_second_derivative
    (a:=0) (b:=Real.arctan (1/5)) (positionEnvelope_continuous q).continuousOn
    (fun x hx => (positionEnvelope_hasDerivAt hql hqu hx).differentiableAt.differentiableWithinAt)
    ht hzero (positionEnvelope_second_derivative hql hqu ht) hschur

/-- The envelope has at most one critical tilt. -/
theorem positionEnvelope_critical_unique {q t v : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval) (hv : v∈tiltInterval)
    (hdt : deriv (positionEnvelope q) t=0) (hdv : deriv (positionEnvelope q) v=0) : t=v :=
  critical_unique_of_strict_minimum (positionEnvelope_continuous q).continuousOn
    (fun _ hx hz => positionEnvelope_critical_strictMinimum hql hqu hx hz) ht hv hdt hdv

/-- A critical tilt is the minimum of the envelope on the closed tilt interval. -/
theorem positionEnvelope_critical_global_minimum {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval)
    (hdt : deriv (positionEnvelope q) t=0) :
    ∀ v∈Icc 0 (Real.arctan (1/5)), positionEnvelope q t≤positionEnvelope q v :=
  critical_is_global_minimum (positionEnvelope_continuous q).continuousOn
    (fun _ hx hz => positionEnvelope_critical_strictMinimum hql hqu hx hz) ht hdt

/-! ### The stationary chain is unique -/

/-- The tilt `2 arctan z` of a chain. -/
def coordinateAngle (d : Coordinates) : ℝ := 2*Real.arctan d.z

/-- `c` and `s` are the cosine and sine of `2 arctan z`. -/
theorem coordinateAngle_frame (d : Coordinates) :
    Real.cos (coordinateAngle d)=d.c ∧ Real.sin (coordinateAngle d)=d.s := by
  have hp : 0<1+d.z^2 := halfAngle_den_pos d.z
  have hs : (Real.sqrt (1+d.z^2))^2=1+d.z^2 := Real.sq_sqrt hp.le
  have hzs := congrArg (fun x : ℝ => d.z*x) hs
  have hn : Real.sqrt (1+d.z^2)≠0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  constructor
  · rw [coordinateAngle,Real.cos_two_mul,Real.cos_arctan]
    dsimp [Coordinates.c,halfAngleCos]
    field_simp [hn,ne_of_gt hp]
    nlinarith
  · rw [coordinateAngle,Real.sin_two_mul,Real.sin_arctan,Real.cos_arctan]
    dsimp [Coordinates.s,halfAngleSin]
    field_simp [hn,ne_of_gt hp]
    nlinarith

/-- The tilt of a stationary chain lies in the tilt interval. -/
theorem stationary_angle_mem {d : Coordinates} (hd : d.IsStationary) :
    coordinateAngle d∈tiltInterval := by
  have hpos : 0<Real.arctan d.z := Real.arctan_pos.mpr hd.z_pos
  have he := Real.two_mul_arctan (by linarith [hd.z_pos] : -1<d.z) hd.z_lt_one
  have hupper := Real.arctan_strictMono hd.tilt_range
  change 0<2*Real.arctan d.z ∧ 2*Real.arctan d.z<Real.arctan (1/5)
  constructor
  · linarith
  · rw [he]
    exact hupper

/-- The position minimum at the tilt of a stationary chain is its position. -/
theorem stationary_minimizingPosition {d : Coordinates} (hd : d.IsStationary) :
    minimizingPosition d.q (coordinateAngle d)= -d.y := by
  have hcritical := stationary_isStripCritical hd
  obtain ⟨hc,hs⟩ := coordinateAngle_frame d
  dsimp only [minimizingPosition]
  rw [hc,hs]
  exact windowMinimizer_eq_of_stationary hd.q_lower hd.q_upper
    hcritical.cosine_pos hcritical.sine_nonneg hcritical.unit hcritical.tilt_upper
    hcritical.strip.bounds.domain hcritical.position_derivative_zero

/-- The envelope vanishes at the radius and the tilt of a stationary chain. -/
theorem stationary_envelope_zero {d : Coordinates} (hd : d.IsStationary) :
    positionEnvelope d.q (coordinateAngle d)=0 := by
  rw [positionEnvelope_eq]
  change defect d.q (Real.cos (coordinateAngle d)) (Real.sin (coordinateAngle d))
    (minimizingPosition d.q (coordinateAngle d))=0
  obtain ⟨hc,hs⟩ := coordinateAngle_frame d
  rw [stationary_minimizingPosition hd,hc,hs,coordinate_defect hd.toIsChain]
  exact hd.zero_defect

/-- The tilt of a stationary chain is a critical tilt of the envelope at its radius. -/
theorem stationary_envelope_critical {d : Coordinates} (hd : d.IsStationary) :
    deriv (positionEnvelope d.q) (coordinateAngle d)=0 := by
  have hderiv := (positionEnvelope_hasDerivAt hd.q_lower hd.q_upper (stationary_angle_mem hd)).deriv
  obtain ⟨hc,hs⟩ := coordinateAngle_frame d
  rw [stationary_minimizingPosition hd,hc,hs,coordinate_tiltFirst hd.toIsChain] at hderiv
  exact hderiv.trans hd.tilt_stationary

/-- At the radius of a stationary chain the envelope is nonnegative on the closed tilt
interval. -/
theorem stationary_envelope_nonneg {d : Coordinates} (hd : d.IsStationary)
    {t : ℝ} (ht : t∈Icc 0 (Real.arctan (1/5))) :
    0 ≤ positionEnvelope d.q t := by
  have hm := positionEnvelope_critical_global_minimum hd.q_lower hd.q_upper
    (stationary_angle_mem hd) (stationary_envelope_critical hd) t ht
  rwa [stationary_envelope_zero hd] at hm

/-- Two stationary chains have the same radius. -/
theorem stationary_radius_eq {d e : Coordinates} (hd : d.IsStationary) (he : e.IsStationary) :
    d.q=e.q := by
  have htd := stationary_angle_mem hd
  have hte := stationary_angle_mem he
  obtain ⟨hcd,hsd,_⟩ := tiltInterval_bounds htd
  obtain ⟨hce,hse,_⟩ := tiltInterval_bounds hte
  rcases lt_trichotomy d.q e.q with hlt | hq | hlt
  · have hdecrease := positionEnvelope_radius_decrease hd.q_lower he.q_upper hlt hcd hsd.le
    have hnonneg := stationary_envelope_nonneg he ⟨htd.1.le,htd.2.le⟩
    rw [stationary_envelope_zero hd] at hdecrease
    linarith
  · exact hq
  · have hdecrease := positionEnvelope_radius_decrease he.q_lower hd.q_upper hlt hce hse.le
    have hnonneg := stationary_envelope_nonneg hd ⟨hte.1.le,hte.2.le⟩
    rw [stationary_envelope_zero he] at hdecrease
    linarith

/-- Two stationary chains have the same tilt. -/
theorem stationary_angle_eq {d e : Coordinates} (hd : d.IsStationary) (he : e.IsStationary) :
    coordinateAngle d=coordinateAngle e := by
  have hq := stationary_radius_eq hd he
  have hdcritical := stationary_envelope_critical hd
  have hecritical := stationary_envelope_critical he
  rw [← hq] at hecritical
  exact positionEnvelope_critical_unique hd.q_lower hd.q_upper
    (stationary_angle_mem hd) (stationary_angle_mem he) hdcritical hecritical

/-- The stationary system has at most one solution. -/
theorem stationary_chain_unique {d e : Coordinates} (hd : d.IsStationary) (he : e.IsStationary) :
    d=e := by
  have hq := stationary_radius_eq hd he
  have ht := stationary_angle_eq hd he
  have hdm := stationary_minimizingPosition hd
  have hem := stationary_minimizingPosition he
  rw [← hq,← ht] at hem
  have hy : d.y=e.y := by linarith
  have hz : d.z=e.z := by
    apply Real.arctan_injective
    dsimp only [coordinateAngle] at ht
    linarith
  exact Coordinates.chain_unique_radicals hd.toIsChain he.toIsChain hq hy hz

end SquaresInCircles.Eight.Stationary.FiveCornerGeometry
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.Stationary
open Arithmetic Generated Coordinates

def radicalCoordinates (q y z : ℝ) : Coordinates where
  q := q
  y := y
  z := z
  x₁ := Real.sqrt (q-y^2)
  x₂ := Real.sqrt (q-(y+2)^2)
  y₃ := Real.sqrt (q-(Real.sqrt (q-(y+2)^2)-3)^2)
  x₄ := -Real.sqrt (q-(Real.sqrt (q-(Real.sqrt (q-(y+2)^2)-3)^2)-2)^2)

theorem radical_formula_values (q y z : ℝ) :
    xOneFormula.eval ![q,y,z] = (radicalCoordinates q y z).x₁ ∧
    xTwoFormula.eval ![q,y,z] = (radicalCoordinates q y z).x₂ ∧
    yThreeFormula.eval ![q,y,z] = (radicalCoordinates q y z).y₃ ∧
    xFourFormula.eval ![q,y,z] = (radicalCoordinates q y z).x₄ ∧
    cosineFormula.eval ![q,y,z] = (radicalCoordinates q y z).c ∧
    sineFormula.eval ![q,y,z] = (radicalCoordinates q y z).s ∧
    hOneFormula.eval ![q,y,z] = (radicalCoordinates q y z).h₁ ∧
    hTwoFormula.eval ![q,y,z] = (radicalCoordinates q y z).h₂ := by
  simp [xOne_eval,xTwo_eval,yThree_eval,xFour_eval,cosine_eval,sine_eval,
    hOne_eval,hTwo_eval,scalarxOne,scalarxTwo,scalaryThree,scalarxFour,
    scalarcosine,scalarsine,scalarhOne,scalarhTwo,radicalCoordinates,
    c,s,h₁,h₂,y₄,halfAngleCos,halfAngleSin,div_eq_mul_inv,sub_eq_add_neg]

theorem radical_local_bounds {q y z : ℝ} (he : localBox.Mem ![q,y,z]) :
    17428/10000 ≤ (radicalCoordinates q y z).x₁ ∧
      (radicalCoordinates q y z).x₁ ≤ 17649/10000 ∧
    16414/10000 ≤ (radicalCoordinates q y z).x₂ ∧
      (radicalCoordinates q y z).x₂ ≤ 16691/10000 ∧
    14387/10000 ≤ (radicalCoordinates q y z).y₃ ∧
      (radicalCoordinates q y z).y₃ ≤ 14643/10000 ∧
    -19049/10000 ≤ (radicalCoordinates q y z).x₄ ∧
      (radicalCoordinates q y z).x₄ ≤ -18974/10000 ∧
    -14263/10000 ≤ (radicalCoordinates q y z).h₁ ∧
      (radicalCoordinates q y z).h₁ ≤ -13198/10000 ∧
    -15316/10000 ≤ (radicalCoordinates q y z).h₂ ∧
      (radicalCoordinates q y z).h₂ ≤ -13202/10000 := by
  obtain ⟨hx₁,hx₂,hy₃,hx₄,hc,hs,hh₁,hh₂⟩ := radical_formula_values q y z
  have h₁ := localXOne_bound _ he
  have h₂ := localXTwo_bound _ he
  have h₃ := localYThree_bound _ he
  have h₄ := localXFour_bound _ he
  have h₅ := localHOne_bound _ he
  have h₆ := localHTwo_bound _ he
  rw [show formula10 = xOneFormula from rfl, hx₁] at h₁
  rw [show formula15 = xTwoFormula from rfl, hx₂] at h₂
  rw [show formula21 = yThreeFormula from rfl, hy₃] at h₃
  rw [show formula28 = xFourFormula from rfl, hx₄] at h₄
  rw [show formula42 = hOneFormula from rfl, hh₁] at h₅
  rw [show formula50 = hTwoFormula from rfl, hh₂] at h₆
  exact ⟨by linarith only [h₁.1],by linarith only [h₁.2],by linarith only [h₂.1],
    by linarith only [h₂.2],by linarith only [h₃.1],by linarith only [h₃.2],
    by linarith only [h₄.1],by linarith only [h₄.2],by linarith only [h₅.1],
    by linarith only [h₅.2],by linarith only [h₆.1],by linarith only [h₆.2]⟩

theorem radical_isChain {q y z : ℝ} (he : localBox.Mem ![q,y,z]) :
    (radicalCoordinates q y z).IsChain := by
  obtain ⟨hx₁,_,hx₂,_,hy₃,_,_,hx₄,_⟩ := radical_local_bounds he
  have h₁ : 0 < (radicalCoordinates q y z).x₁ := by linarith only [hx₁]
  have h₂ : 0 < (radicalCoordinates q y z).x₂ := by linarith only [hx₂]
  have h₃ : 0 < (radicalCoordinates q y z).y₃ := by linarith only [hy₃]
  have h₄ : (radicalCoordinates q y z).x₄ < 0 := by linarith only [hx₄]
  have r₁ : 0 ≤ q-y^2 := (Real.sqrt_pos.mp h₁).le
  have r₂ : 0 ≤ q-(y+2)^2 := (Real.sqrt_pos.mp h₂).le
  have r₃ : 0 ≤ q-(Real.sqrt (q-(y+2)^2)-3)^2 := (Real.sqrt_pos.mp h₃).le
  have r₄ : 0 ≤ q-(Real.sqrt (q-(Real.sqrt (q-(y+2)^2)-3)^2)-2)^2 := by
    apply le_of_lt (Real.sqrt_pos.mp ?_)
    dsimp [radicalCoordinates] at h₄
    linarith only [h₄]
  refine ⟨h₁,h₂,h₃,h₄,?_,?_,?_,?_⟩ <;>
    simp [radicalCoordinates,x₃,y₄,Real.sq_sqrt,r₁,r₂,r₃,r₄]

theorem familyValue_radical (q y z : ℝ) :
    familyValue q (y,z) = (radicalCoordinates q y z).defect := by
  simp [familyValue,F_eval,scalarF,radicalCoordinates,defect,h₁,h₂,c,s,y₄,
    halfAngleCos,halfAngleSin,div_eq_mul_inv,sub_eq_add_neg]

theorem familyY_radical {q y z : ℝ}
    (h : (radicalCoordinates q y z).IsChain) :
    familyY q (y,z) = (radicalCoordinates q y z).positionDerivative := by
  have hn₁ := ne_of_gt h.x₁_pos
  have hn₂ := ne_of_gt h.x₂_pos
  have hn₃ := ne_of_gt h.y₃_pos
  have hn₄ := ne_of_lt h.x₄_neg
  have hden := ne_of_gt (halfAngle_den_pos z)
  simp only [familyY,Fy_eval]
  dsimp [scalarFy,positionDerivative,h₁deriv,h₂deriv,y₄deriv,
    h₁,h₂,c,s,x₃,y₄,halfAngleCos,halfAngleSin,radicalCoordinates] at *
  push_cast
  simp only [sub_eq_add_neg]
  ring_nf

theorem familyZ_radical (q y z : ℝ) :
    familyZ q (y,z) = (2/(1+z^2))*(radicalCoordinates q y z).tiltDerivative := by
  simp only [familyZ,Fz_eval]
  dsimp [scalarFz,tiltDerivative,h₁,h₂,c,s,y₄,halfAngleCos,halfAngleSin,
    radicalCoordinates]
  field_simp [ne_of_gt (halfAngle_den_pos z)]
  ring_nf

theorem sharp_endpoint_signs : 0 < minimumValue sharpLower ∧ minimumValue sharpUpper < 0 := by
  have hL := sharpLowF_bound ![sharpLower,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpLower,sharpLowFBox,QInterval.Mem,trialY,trialZ])
  have hU := sharpHighF_bound ![sharpUpper,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpUpper,sharpHighFBox,QInterval.Mem,trialY,trialZ])
  have hy := sharpLowFy_bound ![sharpLower,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpLower,sharpLowFyBox,QInterval.Mem,trialY,trialZ])
  have hz := sharpLowFz_bound ![sharpLower,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpLower,sharpLowFzBox,QInterval.Mem,trialY,trialZ])
  have hlo := minimum_trial_lower (q:=sharpLower) (by norm_num [sharpLower,radiusBox])
  have hup := minimumValue_le sharpUpper trial_mem
  change _ ≤ familyValue sharpLower trial ∧ _ at hL
  change _ ∧ familyValue sharpUpper trial ≤ _ at hU
  change _ ≤ familyY sharpLower trial ∧ familyY sharpLower trial ≤ _ at hy
  change _ ≤ familyZ sharpLower trial ∧ familyZ sharpLower trial ≤ _ at hz
  constructor <;> nlinarith only [hlo, hL, hy, hz, hup, hU]

theorem qStar_bracket : sharpLower < qStar ∧ qStar < sharpUpper := by
  obtain ⟨hL,hU⟩ := sharp_endpoint_signs
  constructor
  · by_contra! h
    have hh := (minimum_radius_difference qStar_mem
      (by norm_num [sharpLower,radiusBox]) h).2
    linarith [minimum_qStar]
  · by_contra! h
    have hh := (minimum_radius_difference
      (by norm_num [sharpUpper,radiusBox]) qStar_mem h).2
    linarith [minimum_qStar]

theorem qStar_limits : 7831/2000 < qStar ∧
    qStar < 1957767069/500000000 ∧ qStar < 9789/2500 := by
  have hh := qStar_bracket
  norm_num [sharpLower,sharpUpper] at hh
  constructor
  · linarith
  constructor <;> linarith

theorem sharpPose_close : |sharpPose.1-trialY| < 1/1000000000000 ∧
    |sharpPose.2-trialZ| < 1/1000000000000 := by
  have hq := qStar_bracket
  have hy := sharpTrialFy_bound ![qStar,trialY,trialZ] (by
    intro i; fin_cases i <;> norm_num [sharpTrialFyBox,QInterval.Mem,trialY,trialZ]
    norm_num [sharpLower,sharpUpper] at hq
    exact ⟨hq.1.le,hq.2.le⟩)
  have hz := sharpTrialFz_bound ![qStar,trialY,trialZ] (by
    intro i; fin_cases i <;> norm_num [sharpTrialFzBox,QInterval.Mem,trialY,trialZ]
    norm_num [sharpLower,sharpUpper] at hq
    exact ⟨hq.1.le,hq.2.le⟩)
  have hc := family_strong_convex qStar_mem trial_mem (minimizingPose_mem qStar)
  have hm := minimumValue_le qStar trial_mem
  change _ ≤ familyY qStar trial ∧ familyY qStar trial ≤ _ at hy
  change _ ≤ familyZ qStar trial ∧ familyZ qStar trial ≤ _ at hz
  have hr : (sharpPose.1-trialY)^2+(sharpPose.2-trialZ)^2 <
      (1/1000000000000:ℝ)^2 := by
    dsimp [sharpPose,minimumValue,trial] at *
    nlinarith only [sq_nonneg ((minimizingPose qStar).1-trialY+8*familyY qStar (trialY,trialZ)),
      sq_nonneg ((minimizingPose qStar).2-trialZ+8*familyZ qStar (trialY,trialZ)), hc, hm, hy, hz]
  exact ⟨abs_lt_of_sq_lt_sq (by linarith only [hr,sq_nonneg (sharpPose.2-trialZ)]) (by norm_num),
    abs_lt_of_sq_lt_sq (by linarith only [hr,sq_nonneg (sharpPose.1-trialY)]) (by norm_num)⟩

theorem sharpBox_mem : sharpBox.Mem ![qStar,sharpPose.1,sharpPose.2] := by
  have hq := qStar_bracket
  obtain ⟨hy,hz⟩ := sharpPose_close
  have hy' := abs_lt.mp hy
  have hz' := abs_lt.mp hz
  intro i; fin_cases i <;>
    norm_num [sharpBox,QInterval.Mem,sharpLower,sharpUpper,trialY,trialZ] at * <;>
    constructor <;> linarith only [hq, hy', hz']

def sharpData : Coordinates := radicalCoordinates qStar sharpPose.1 sharpPose.2

theorem sharpData_stationary : sharpData.IsStationary := by
  have he := local_mem qStar_mem (minimizingPose_mem qStar)
  have hchain : sharpData.IsChain := radical_isChain he
  have hrad := radical_local_bounds he
  have hy := (minimizingPose_mem qStar).1
  have hz := (minimizingPose_mem qStar).2
  norm_num [poseBox] at hy hz
  refine { hchain with
    q_lower := by dsimp [sharpData,radicalCoordinates]; linarith only [qStar_mem.1]
    q_upper := qStar_mem.2
    y_lower := by dsimp [sharpData,sharpPose,radicalCoordinates]; linarith only [hy]
    y_upper := by dsimp [sharpData,sharpPose,radicalCoordinates]; linarith only [hy]
    y₄_lower := ?_
    y₄_upper := ?_
    position_order := ?_
    z_pos := by dsimp [sharpData,sharpPose,radicalCoordinates]; linarith only [hz]
    tilt_range := ?_
    z_lt_one := by dsimp [sharpData,sharpPose,radicalCoordinates]; linarith only [hz]
    zero_defect := ?_
    position_stationary := ?_
    tilt_stationary := ?_ }
  · dsimp [sharpData,sharpPose,y₄]; linarith only [hrad.2.2.2.2.1]
  · dsimp [sharpData,sharpPose,y₄]; linarith only [hrad.2.2.2.2.2.1]
  · dsimp [sharpData,sharpPose,y₄,radicalCoordinates] at *
    linarith only [hrad.2.2.2.2.1, hy]
  · dsimp [sharpData,sharpPose,radicalCoordinates]
    rw [div_lt_iff₀ (by nlinarith only [hz] : 0<1-(minimizingPose qStar).2^2)]
    nlinarith only [hz]
  · exact (familyValue_radical qStar sharpPose.1 sharpPose.2).symm.trans sharpPose_value
  · exact (familyY_radical hchain).symm.trans sharpPose_stationary.1
  · have hzv := sharpPose_stationary.2
    rw [familyZ_radical] at hzv
    exact (mul_eq_zero.mp hzv).resolve_left
      (ne_of_gt (div_pos (by norm_num) (halfAngle_den_pos sharpPose.2)))

theorem stationary_unique {d : Coordinates} (hd : d.IsStationary) : d=sharpData :=
  FiveCornerGeometry.stationary_chain_unique hd sharpData_stationary

theorem exact_stationary_existsUnique : ∃! d : Coordinates, d.IsStationary :=
  ⟨sharpData,sharpData_stationary,fun _ h => stationary_unique h⟩

theorem sharp_coordinates :
    175152/100000 ≤ sharpData.x₁ ∧ sharpData.x₁ ≤ 175159/100000 ∧
    165843/100000 ≤ sharpData.x₂ ∧ sharpData.x₂ ≤ 165852/100000 ∧
    145455/100000 ≤ sharpData.y₃ ∧ sharpData.y₃ ≤ 145464/100000 ∧
    -190214/100000 ≤ sharpData.x₄ ∧ sharpData.x₄ ≤ -190211/100000 ∧
    99231/100000 ≤ sharpData.c ∧ sharpData.c ≤ 99242/100000 ∧
    12327/100000 ≤ sharpData.s ∧ sharpData.s ≤ 12338/100000 ∧
    -136797/100000 ≤ sharpData.h₁ ∧ sharpData.h₁ ≤ -136748/100000 ∧
    -143022/100000 ≤ sharpData.h₂ ∧ sharpData.h₂ ≤ -142976/100000 := by
  have hv := radical_formula_values qStar sharpPose.1 sharpPose.2
  have h₁ := sharpXOne_bound _ sharpBox_mem
  have h₂ := sharpXTwo_bound _ sharpBox_mem
  have h₃ := sharpYThree_bound _ sharpBox_mem
  have h₄ := sharpXFour_bound _ sharpBox_mem
  have h₅ := sharpCosine_bound _ sharpBox_mem
  have h₆ := sharpSine_bound _ sharpBox_mem
  have h₇ := sharpHOne_bound _ sharpBox_mem
  have h₈ := sharpHTwo_bound _ sharpBox_mem
  rcases hv with ⟨hx₁,hx₂,hy₃,hx₄,hc,hs,hh₁,hh₂⟩
  rw [show formula10 = xOneFormula from rfl, hx₁] at h₁
  rw [show formula15 = xTwoFormula from rfl, hx₂] at h₂
  rw [show formula21 = yThreeFormula from rfl, hy₃] at h₃
  rw [show formula28 = xFourFormula from rfl, hx₄] at h₄
  rw [show formula34 = cosineFormula from rfl, hc] at h₅
  rw [show formula36 = sineFormula from rfl, hs] at h₆
  rw [show formula42 = hOneFormula from rfl, hh₁] at h₇
  rw [show formula50 = hTwoFormula from rfl, hh₂] at h₈
  unfold sharpData
  exact ⟨by linarith only [h₁.1],by linarith only [h₁.2],by linarith only [h₂.1],
    by linarith only [h₂.2],by linarith only [h₃.1],by linarith only [h₃.2],
    by linarith only [h₄.1],by linarith only [h₄.2],by linarith only [h₅.1],
    by linarith only [h₅.2],by linarith only [h₆.1],by linarith only [h₆.2],
    by linarith only [h₇.1],by linarith only [h₇.2],by linarith only [h₈.1],
    by linarith only [h₈.2]⟩

theorem sharp_y : -92071/100000 < sharpData.y ∧ sharpData.y < -92059/100000 := by
  have h := abs_lt.mp sharpPose_close.1
  dsimp [sharpData,radicalCoordinates]
  norm_num [trialY] at h
  constructor <;> linarith

end SquaresInCircles.Eight.Stationary
end
end
end
