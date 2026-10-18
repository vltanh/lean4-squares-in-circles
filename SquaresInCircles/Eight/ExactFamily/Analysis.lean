module

public import SquaresInCircles.Common.Analysis
public import SquaresInCircles.Eight.ExactFamily.Generated.LocalStationaryBounds
public import SquaresInCircles.Eight.ExactFamily.Generated.StationaryLocalization
public import SquaresInCircles.Eight.ExactFamily.Coordinates

/-!
# Existence and uniqueness of the stationary zero

Uncompiled draft.  The local argument uses the minimum on a fixed compact
rectangle.  The complete generated closed cover sends every admissible
stationary zero to that rectangle.  The cover does not supply existence;
existence follows from continuity, two opposite value signs, and the
intermediate value theorem.  The Hessian certificate gives curvature 1/4
in the position and half-angle coordinates.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set

namespace SquaresInCircles.Eight.ExactFamily
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
  intro i; fin_cases i
  · exact hq
  · exact hp.1
  · exact hp.2

theorem trial_mem : trial ∈ poseBox := by
  norm_num [trial,poseBox,trialY,trialZ]

theorem family_continuous : Continuous (fun x : ℝ × Pose => familyValue x.1 x.2) := by
  simp only [familyValue,F_eval]
  unfold scalarF
  fun_prop (disch := positivity)

theorem family_continuous_pose (q : ℝ) : Continuous (familyValue q) := by
  exact family_continuous.comp (continuous_const.prod_mk continuous_id)

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
  · convert (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).mul_const a.1).add
      ((hasDerivAt_id t).mul_const b.1) using 1 <;> simp [segment] <;> ring
  · convert (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).mul_const a.2).add
      ((hasDerivAt_id t).mul_const b.2) using 1 <;> simp [segment] <;> ring

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
  simpa [segment] using hcurv

theorem stationary_pose_unique {q : ℝ} (hq : q ∈ radiusBox)
    {a b : Pose} (ha : a ∈ poseBox) (hb : b ∈ poseBox)
    (haY : familyY q a=0) (haZ : familyZ q a=0)
    (hbY : familyY q b=0) (hbZ : familyZ q b=0) : a=b := by
  have h₁ := family_strong_convex hq ha hb
  have h₂ := family_strong_convex hq hb ha
  rw [haY,haZ] at h₁
  rw [hbY,hbZ] at h₂
  ext <;> nlinarith [sq_nonneg (b.1-a.1),sq_nonneg (b.2-a.2)]

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
  have hY := trialFy_bound ![q,trialY,trialZ] (by
    intro i; fin_cases i <;> norm_num [trialFyBox,QInterval.Mem] <;> exact hq)
  have hZ := trialFz_bound ![q,trialY,trialZ] (by
    intro i; fin_cases i <;> norm_num [trialFzBox,QInterval.Mem] <;> exact hq)
  exact ⟨abs_le.mpr hY,abs_le.mpr hZ⟩

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
  convert h using 1
  · funext y
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  · rfl

theorem family_partial_z {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun z => familyValue q (p.1,z)) (familyZ q p) p.2 := by
  have h := Formula.hasDerivAt_partial FFormula 2 ![q,p.1,p.2] (family_regular hq hp).1
  rw [Fz_diff] at h
  convert h using 1
  · funext z
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  · rfl

theorem family_partial_q {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun r => familyValue r p) (familyQ q p) q := by
  have h := Formula.hasDerivAt_partial FFormula 0 ![q,p.1,p.2] (family_regular hq hp).1
  rw [Fq_diff] at h
  convert h using 1
  · funext r
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  · rfl

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

theorem stationary_is_minimum {q : ℝ} (hq : q ∈ radiusBox) {p : Pose}
    (hp : p ∈ poseBox) (hy : familyY q p=0) (hz : familyZ q p=0) :
    minimumValue q = familyValue q p := by
  have hm := minimizingPose_stationary hq
  have heq := stationary_pose_unique hq (minimizingPose_mem q) hp hm.1 hm.2 hy hz
  rw [minimumValue,heq]

theorem family_radius_difference {q r : ℝ} (hq : q ∈ radiusBox) (hr : r ∈ radiusBox)
    (hqr : q ≤ r) {p : Pose} (hp : p ∈ poseBox) :
    -4*(r-q) ≤ familyValue r p-familyValue q p ∧
      familyValue r p-familyValue q p ≤ -3*(r-q) := by
  have hanti := antiOn_of_hasDeriv_nonpos (l:=7831/2000) (u:=9789/2500)
    (f:=fun x => familyValue x p+3*x) (d:=fun x => familyQ x p+3)
    (by exact ((family_continuous.comp (continuous_id.prod_mk continuous_const)).add
      (continuous_const.mul continuous_id)).continuousOn)
    (fun x hx => by
      convert (family_partial_q ⟨hx.1.le,hx.2.le⟩ hp).add
        ((hasDerivAt_id x).const_mul 3) using 1 <;> ring)
    (fun x hx => by linarith [(family_q_bound ⟨hx.1.le,hx.2.le⟩ hp).2])
  have hmono := monoOn_of_hasDeriv_nonneg (l:=7831/2000) (u:=9789/2500)
    (f:=fun x => familyValue x p+4*x) (d:=fun x => familyQ x p+4)
    (by exact ((family_continuous.comp (continuous_id.prod_mk continuous_const)).add
      (continuous_const.mul continuous_id)).continuousOn)
    (fun x hx => by
      convert (family_partial_q ⟨hx.1.le,hx.2.le⟩ hp).add
        ((hasDerivAt_id x).const_mul 4) using 1 <;> ring)
    (fun x hx => by linarith [(family_q_bound ⟨hx.1.le,hx.2.le⟩ hp).1])
  have h₁ := hanti hq hr hqr
  have h₂ := hmono hq hr hqr
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
  exact continuousOn_iff_continuous_restrict.mpr hlip.continuous

theorem minimum_trial_lower {q : ℝ} (hq : q ∈ radiusBox) :
    familyValue q trial-2*(familyY q trial)^2-2*(familyZ q trial)^2 ≤ minimumValue q := by
  have h := family_strong_convex hq trial_mem (minimizingPose_mem q)
  dsimp [minimumValue]
  nlinarith [sq_nonneg ((minimizingPose q).1-trial.1+4*familyY q trial),
    sq_nonneg ((minimizingPose q).2-trial.2+4*familyZ q trial)]

theorem minimum_endpoint_signs :
    0 < minimumValue (7831/2000) ∧ minimumValue (9789/2500) < 0 := by
  have hL := lowerTest_bound ![7831/2000,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [lowerTestBox,QInterval.Mem])
  have hU := upperTest_bound ![9789/2500,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [upperTestBox,QInterval.Mem])
  have hcurv := minimum_trial_lower (q:=7831/2000) (by norm_num [radiusBox])
  obtain ⟨hy,hz⟩ := trial_gradients (q:=7831/2000) (by norm_num [radiusBox])
  have hy' := abs_le.mp hy
  have hz' := abs_le.mp hz
  have hupper := minimumValue_le (9789/2500) trial_mem
  change (1/8000:ℝ) ≤ familyValue (7831/2000) trial ∧ _ at hL
  change _ ∧ familyValue (9789/2500) trial ≤ -(1/5000) at hU
  constructor <;> nlinarith

theorem unique_minimum_zero : ∃! q : ℝ, q ∈ radiusBox ∧ minimumValue q=0 := by
  have hs := minimum_endpoint_signs
  have hcont : ContinuousOn (fun q => -minimumValue q) radiusBox := minimum_continuous.neg
  obtain ⟨q,hq,hzero⟩ := intermediate_value_Icc (by norm_num : (7831/2000:ℝ) ≤ 9789/2500)
    hcont ⟨by linarith [hs.1],by linarith [hs.2]⟩
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

/-- This is the stationary root theorem in value/derivative coordinates.  The
algebraic `Coordinates.IsStationary` adapter is given in `Stationary.lean`. -/
theorem stationary_existsUnique : ∃! x : ℝ × Pose,
    x.1 ∈ radiusBox ∧ x.2 ∈ poseBox ∧ familyValue x.1 x.2=0 ∧
      familyY x.1 x.2=0 ∧ familyZ x.1 x.2=0 := by
  refine ⟨(qStar,sharpPose),⟨qStar_mem,minimizingPose_mem _,sharpPose_value,
    sharpPose_stationary.1,sharpPose_stationary.2⟩,?_⟩
  intro x hx
  have hmin := stationary_is_minimum hx.1 hx.2.1 hx.2.2.2.1 hx.2.2.2.2
  have hq : x.1=qStar := (Classical.choose_spec unique_minimum_zero).2 x.1
    ⟨hx.1,by linarith [hx.2.2.1]⟩
  have hp : x.2=sharpPose := stationary_pose_unique hx.1 hx.2.1
    (by simpa [hq,sharpPose] using minimizingPose_mem qStar)
    hx.2.2.2.1 hx.2.2.2.2
    (by simpa [hq] using sharpPose_stationary.1)
    (by simpa [hq] using sharpPose_stationary.2)
  exact Prod.ext hq hp

end SquaresInCircles.Eight.ExactFamily
