module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAEBT3Scalar

/-!
# The increasing convex penalty in the separated BT3 alternative

Uncompiled transcription of Section 5 of the joint-negative BT3 proof.
For the unaffected term, convexity of its derivative and monotonicity
of the penalty derivative give the endpoint principle directly. The
maximum defining the cost is handled by its two exact branches; their
endpoint values agree at every corner. For the affected term, the
secant penalty is a convex square root after the tangent substitution.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Penalty
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open SecantNormCurvature
open JointNegativeAETD2.CommonGain

def cost (c S : ℝ) : ℝ :=
  if c<1 then (109/200)*secant S else max (13/20) (max ((109/200)*c) ((109/200)*secant S))
def constantCost (c : ℝ) : ℝ := if c<1 then 0 else max (13/20) ((109/200)*c)

theorem cost_max (c : ℝ) {S : ℝ} (hS : S∈Icc 0 frameCap) :
    cost c S=max (constantCost c) ((109/200)*secant S) := by
  have hs := (full_secant_domain hS).1
  by_cases hc : c<1
  · simp only [cost,constantCost,if_pos hc]
    exact (max_eq_right (by nlinarith)).symm
  · simp only [cost,constantCost,if_neg hc,max_assoc]

theorem cost_bounds {c S : ℝ} (hc : c≤7/5) (hS : S∈Icc 0 frameCap) :
    0≤cost c S ∧ cost c S≤763/1000 := by
  have hs := full_secant_domain hS
  by_cases hh : c<1
  · simp only [cost,if_pos hh]
    constructor <;> nlinarith [hs.1,hs.2]
  · simp only [cost,if_neg hh]
    exact ⟨(by norm_num : (0:ℝ)≤13/20).trans (le_max_left _ _),
      max_le (by norm_num) (max_le (by nlinarith) (by nlinarith [hs.2]))⟩

theorem secant_monotone : MonotoneOn secant (Icc (0:ℝ) frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro x hx
    exact (secant_hasDerivAt (show Real.cos x≠0 by linarith [(transport_trig hx).1])).continuousAt.continuousWithinAt
  · intro x hx
    exact secant_hasDerivAt (show Real.cos x≠0 by linarith [(transport_trig (Ioo_subset_Icc_self hx)).1])
  · intro x hx
    exact div_nonneg (transport_trig (Ioo_subset_Icc_self hx)).2.2.1 (sq_nonneg _)

theorem first_nonnegative {x : ℝ} (hx : x∈Icc 0 frameCap) : 0≤first x :=
  div_nonneg (transport_trig hx).2.2.1 (sq_nonneg _)

theorem first_monotone : MonotoneOn first (Icc (0:ℝ) frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro x hx
    exact (first_hasDerivAt (show Real.cos x≠0 by linarith [(transport_trig hx).1])).continuousAt.continuousWithinAt
  · intro x hx
    exact first_hasDerivAt (show Real.cos x≠0 by linarith [(transport_trig (Ioo_subset_Icc_self hx)).1])
  · intro x hx
    dsimp [second]
    have hc : 0<Real.cos x := by linarith [(transport_trig (Ioo_subset_Icc_self hx)).1]
    positivity

/-- A nonnegative increasing penalty derivative cannot create a new
minimum in a function whose derivative is convex and nonpositive at
the right endpoint. The proof uses only two-point convexity. -/
theorem endpoint_after_penalty {f g u v : ℝ→ℝ} {t s : ℝ}
    (ht : 0≤t) (hs : s∈Icc 0 t)
    (hf : ∀x∈Icc 0 t,HasDerivAt f (u x) x)
    (hg : ∀x∈Icc 0 t,HasDerivAt g (v x) x)
    (hu : ConcaveOn ℝ (Icc 0 t) (fun x => -u x)) (hut : u t≤0)
    (hv : ∀x∈Icc 0 t,0≤v x) (hvm : MonotoneOn v (Icc 0 t)) :
    min (f 0-g 0) (f t-g t)≤f s-g s := by
  have hright {a b : ℝ} (ha : a∈Icc 0 t) (hb : b∈Icc a t)
      (hderiv : u a-v a≤0) : u b-v b≤0 := by
    have hb' : b∈Icc 0 t := ⟨ha.1.trans hb.1,hb.2⟩
    have hh := hu.min_le_of_mem_Icc ha ⟨ht,le_rfl⟩ hb
    have hlo : -v a≤min (-u a) (-u t) := le_min (by linarith) (by linarith [hv a ha])
    have hm := hvm ha hb' hb.1
    linarith
  by_cases hsign : u s-v s≤0
  · have hm : AntitoneOn (fun x => f x-g x) (Icc s t) := by
      apply antiOn_of_hasDeriv_nonpos
      · intro x hx
        exact ((hf x ⟨hs.1.trans hx.1,hx.2⟩).sub (hg x ⟨hs.1.trans hx.1,hx.2⟩)).continuousAt.continuousWithinAt
      · intro x hx
        exact (hf x ⟨hs.1.trans hx.1.le,hx.2.le⟩).sub (hg x ⟨hs.1.trans hx.1.le,hx.2.le⟩)
      · intro x hx
        exact hright hs (Ioo_subset_Icc_self hx) hsign
    exact (min_le_right _ _).trans (hm ⟨le_rfl,hs.2⟩ ⟨hs.2,le_rfl⟩ hs.2)
  · have hm : MonotoneOn (fun x => f x-g x) (Icc 0 s) := by
      apply monoOn_of_hasDeriv_nonneg
      · intro x hx
        exact ((hf x ⟨hx.1,hx.2.trans hs.2⟩).sub (hg x ⟨hx.1,hx.2.trans hs.2⟩)).continuousAt.continuousWithinAt
      · intro x hx
        exact (hf x ⟨hx.1.le,hx.2.le.trans hs.2⟩).sub (hg x ⟨hx.1.le,hx.2.le.trans hs.2⟩)
      · intro x hx
        by_contra hh
        have hnon : u x-v x≤0 := (lt_of_not_ge hh).le
        exact hsign (hright ⟨hx.1.le,hx.2.le.trans hs.2⟩ ⟨hx.2.le,hs.2⟩ hnon)
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hs.1⟩ ⟨hs.1,le_rfl⟩ hs.1)

theorem unaffected_secant_penalty {k b S : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hb : 0≤b) (hS : S∈Icc 0 frameCap) :
    min (V R k 1 frameCap-b) (F k frameCap-b*secant frameCap)≤
      F k S+V R k 1 (frameCap-S)-b*secant S := by
  have hk0 : 0<k := by linarith [hk.1]
  have ht : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hconc : ConcaveOn ℝ (Icc 0 frameCap) (fun x => -unaffectedFirst k frameCap x) := by
    apply concave_of_deriv2
      (fun x hx => (unaffectedFirst_derivative hk0 ht hx).neg)
      (fun x hx => (unaffectedSecond_derivative hk0 ht hx).neg)
    intro x hx
    linarith [unaffectedThird_positive hk ht hx]
  have hright : unaffectedFirst k frameCap frameCap≤0 := by
    have hF := first_upper_long hk (show frameCap∈Icc (3/20:ℝ) frameCap by norm_num [frameCap])
    have hV := zero_slope_lower hk
    simp only [unaffectedFirst,sub_self]
    linarith
  have hh := endpoint_after_penalty (f:=unaffected k frameCap) (g:=fun x => b*secant x)
    (u:=unaffectedFirst k frameCap) (v:=fun x => b*first x) ht.1 hS
    (fun x hx => unaffected_derivative hk0 ht hx)
    (fun x hx => (secant_hasDerivAt (show Real.cos x≠0 by linarith [(transport_trig hx).1])).const_mul b)
    hconc hright (fun x hx => mul_nonneg hb (first_nonnegative hx))
    (fun x hx y hy hxy => mul_le_mul_of_nonneg_left (first_monotone hx hy hxy) hb)
  simpa [unaffected,F_zero,secant] using hh

theorem secant_tan_identity {S : ℝ} (hS : S∈Icc 0 frameCap) :
    NegativeAPositiveTD.SecantCoordinate.radical 1 (Real.tan S)=secant S := by
  have hc : 0<Real.cos S := by linarith [(transport_trig hS).1]
  have hi := (NegativeAPositiveTD.AffectedNorm.tan_identity hc).2
  have hs := NegativeAPositiveTD.SecantCoordinate.radical_square (A:=1) (x:=Real.tan S) (by norm_num)
  have hp := NegativeAPositiveTD.SecantCoordinate.radical_positive (A:=1) (x:=Real.tan S) (by norm_num)
  have hsec : 0<secant S := div_pos (by norm_num) hc
  dsimp [secant] at ⊢ hsec
  nlinarith

theorem affected_secant_penalty {k b S : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hb : 0≤b) (hS : S∈Icc 0 frameCap) :
    min (V R k 1 frameCap-b) (F k frameCap-b*secant frameCap)≤
      F k S+V R k (secant S) (frameCap-S)-b*secant S := by
  have ht : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hv := NegativeAPositiveTD.AffectedNorm.second_coordinate_pos
    (show k∈Icc (0:ℝ) (71/50) from ⟨by linarith [hk.1],by linarith [hk.2]⟩) ht
  let f : ℝ→ℝ := fun x => affectedAffine k frameCap x-b*NegativeAPositiveTD.SecantCoordinate.radical 1 x
  let df : ℝ→ℝ := fun x => K+Real.sin frameCap-R*NegativeAPositiveTD.AffectedNorm.first k frameCap x-
    b*(x/NegativeAPositiveTD.SecantCoordinate.radical 1 x)
  have hd (x : ℝ) : HasDerivAt f (df x) x := by
    have hA := (((((hasDerivAt_id x).const_mul (K+Real.sin frameCap)).add_const (Real.cos frameCap)).sub_const 1).add_const
      (R*Real.sqrt (k^2+1))).sub ((NegativeAPositiveTD.AffectedNorm.norm_hasDerivAt hv).const_mul R)
    exact hA.sub ((NegativeAPositiveTD.SecantCoordinate.radical_hasDerivAt (A:=1) (by norm_num)).const_mul b)
  have hdd (x : ℝ) : HasDerivAt df
      (-R*NegativeAPositiveTD.AffectedNorm.second k frameCap x-
        b/(NegativeAPositiveTD.SecantCoordinate.radical 1 x)^3) x := by
    have hA := ((NegativeAPositiveTD.AffectedNorm.first_hasDerivAt hv).const_mul R).const_sub (K+Real.sin frameCap)
    have hB := (NegativeAPositiveTD.SecantCoordinate.radicalFirst_hasDerivAt (A:=1) (x:=x) (by norm_num)).const_mul b
    convert hA.sub hB using 1 <;> dsimp [df] <;> ring
  have hconc : ConcaveOn ℝ (Icc 0 (Real.tan frameCap)) f := by
    apply concave_of_deriv2 (fun x _ => hd x) (fun x _ => hdd x)
    intro x hx
    have hfirst : 0≤R*NegativeAPositiveTD.AffectedNorm.second k frameCap x := by
      dsimp [NegativeAPositiveTD.AffectedNorm.second]
      positivity
    have hsecond : 0≤b/(NegativeAPositiveTD.SecantCoordinate.radical 1 x)^3 := by
      exact div_nonneg hb (pow_nonneg (Real.sqrt_nonneg _) 3)
    linarith
  have ht0 := NegativeAPositiveTD.SecantCoordinate.tan_nonnegative ht
  have hx : Real.tan S∈Icc 0 (Real.tan frameCap) :=
    ⟨NegativeAPositiveTD.SecantCoordinate.tan_nonnegative hS,
      NegativeAPositiveTD.SecantCoordinate.tan_monotone hS ht hS.2⟩
  have hh := hconc.min_le_of_mem_Icc ⟨le_rfl,ht0⟩ ⟨ht0,le_rfl⟩ hx
  have h0 := affected_identity hk ht (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have h1 := affected_identity hk ht ht
  have hmid := affected_identity hk ht hS
  have hroot0 : NegativeAPositiveTD.SecantCoordinate.radical 1 0=1 := by
    norm_num [NegativeAPositiveTD.SecantCoordinate.radical]
  simp only [f,Real.tan_zero,hroot0,secant_tan_identity ht,secant_tan_identity hS] at hh
  simp only [Real.tan_zero,F_zero,zero_add,sub_zero,sub_self,V_zero,add_zero,
    secant,Real.cos_zero,div_one] at h0 h1
  rw [←h0,←h1,←hmid] at hh
  exact hh

theorem secant_penalty_endpoint {k b S : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hb : 0≤b) (hS : S∈Icc 0 frameCap) :
    min (V R k 1 frameCap-b) (F k frameCap-b*secant frameCap)≤
      F k S+min (V R k 1 (frameCap-S)) (V R k (secant S) (frameCap-S))-b*secant S := by
  have h1 := unaffected_secant_penalty hk hb hS
  have h2 := affected_secant_penalty hk hb hS
  rcases le_total (V R k 1 (frameCap-S)) (V R k (secant S) (frameCap-S)) with h|h
  · rw [min_eq_left h]; exact h1
  · rw [min_eq_right h]; exact h2

theorem endpoint {k c P S : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hP : 0≤P) (hS : S∈Icc 0 frameCap) :
    min (V R k 1 frameCap-P*cost c 0) (F k frameCap-P*cost c frameCap)≤
      F k S+min (V R k 1 (frameCap-S)) (V R k (secant S) (frameCap-S))-P*cost c S := by
  have h0 : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hc0 := cost_max c h0
  have hch := cost_max c hh
  have hcS := cost_max c hS
  have ha0 : constantCost c≤cost c 0 := by rw [hc0]; exact le_max_left _ _
  have hah : constantCost c≤cost c frameCap := by rw [hch]; exact le_max_left _ _
  have hb0 : (109/200:ℝ)≤cost c 0 := by
    rw [hc0]
    simpa [secant] using le_max_right (constantCost c) ((109/200)*secant 0)
  have hbh : (109/200)*secant frameCap≤cost c frameCap := by rw [hch]; exact le_max_right _ _
  by_cases hbranch : (109/200)*secant S≤constantCost c
  · rw [hcS,max_eq_left hbranch]
    have he := JointNegativeAETD2.CommonGain.endpoint hk hh hS
    have hleft := mul_le_mul_of_nonneg_left ha0 hP
    have hright := mul_le_mul_of_nonneg_left hah hP
    have hmin : min (V R k 1 frameCap-P*cost c 0) (F k frameCap-P*cost c frameCap)≤
        min (V R k 1 frameCap) (F k frameCap)-P*constantCost c := by
      rcases le_total (V R k 1 frameCap) (F k frameCap) with h|h
      · rw [min_eq_left h]
        exact (min_le_left _ _).trans (by linarith)
      · rw [min_eq_right h]
        exact (min_le_right _ _).trans (by linarith)
    linarith
  · rw [hcS,max_eq_right (le_of_lt (lt_of_not_ge hbranch))]
    have he := secant_penalty_endpoint (b:=P*(109/200)) hk (by positivity) hS
    have hleft := mul_le_mul_of_nonneg_left hb0 hP
    have hright := mul_le_mul_of_nonneg_left hbh hP
    have hmin : min (V R k 1 frameCap-P*cost c 0) (F k frameCap-P*cost c frameCap)≤
        min (V R k 1 frameCap-P*(109/200)) (F k frameCap-(P*(109/200))*secant frameCap) := by
      apply min_le_min <;> nlinarith
    nlinarith

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Penalty
