module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.Ordinary.PositiveEnvelope
public import SquaresInCircles.Eight.Owners.GA.HybridConcentration
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3PolynomialData
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3SourceData
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2CommonEndpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeAConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves

/-!
# Eight squares: canonical negative forms and the actual BT3 positive charge

The charge retains the combined primary magnitude S. The B pair
keeps the actual ordering of its two coefficients; the single ordinary
D case has pair (c,1). Same-block reduction is used only for ordinary
blocks, leaving the distinguished D term separated.
-/

section
/-!
## The increasing convex penalty in the separated BT3 alternative

For the unaffected term, convexity of its derivative and monotonicity
of the penalty derivative give the endpoint principle directly. The
maximum defining the cost is handled by its two exact branches; their
endpoint values agree at every corner. For the affected term, the
secant penalty is a convex square root after the tangent substitution.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Penalty
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
  · simp only [cost,constantCost,ite_eq_left hc]
    exact (max_eq_right (by nlinarith)).symm
  · simp only [cost,constantCost,ite_eq_right hc,max_assoc]

theorem cost_bounds {c S : ℝ} (hc : c≤7/5) (hS : S∈Icc 0 frameCap) :
    0≤cost c S ∧ cost c S≤763/1000 := by
  have hs := full_secant_domain hS
  by_cases hh : c<1
  · simp only [cost,ite_eq_left hh]
    constructor <;> nlinarith [hs.1,hs.2]
  · simp only [cost,ite_eq_right hh]
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
    have hlo : -v a≤ min (-u a) (-u t) := le_min (by linarith) (by linarith [hv a ha])
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
    convert hA.sub ((NegativeAPositiveTD.SecantCoordinate.radical_hasDerivAt (A:=1) (x:=x)
      (by norm_num)).const_mul b) using 1
    · funext y
      simp only [f,affectedAffine,Pi.sub_apply,id]
    · simp only [df]
      ring
  have hdd (x : ℝ) : HasDerivAt df
      (-R*NegativeAPositiveTD.AffectedNorm.second k frameCap x-
        b/(NegativeAPositiveTD.SecantCoordinate.radical 1 x)^3) x := by
    have hA := ((NegativeAPositiveTD.AffectedNorm.first_hasDerivAt (x:=x) hv).const_mul R).const_sub (K+Real.sin frameCap)
    have hB := (NegativeAPositiveTD.SecantCoordinate.radicalFirst_hasDerivAt (A:=1) (x:=x) (by norm_num)).const_mul b
    convert hA.sub hB using 1
    ring
  have hconc : ConcaveOn ℝ (Icc 0 (Real.tan frameCap)) f := by
    apply concave_of_deriv2 (fun x _ => hd x) (fun x _ => hdd x)
    intro x hx
    have hfirst : 0≤R*NegativeAPositiveTD.AffectedNorm.second k frameCap x := by
      apply mul_nonneg (by linarith [radius_bounds.1])
      exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) 3)
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
  simp only [f,hroot0,secant_tan_identity ht,secant_tan_identity hS,mul_one] at hh
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
    simp [secant]
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

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Penalty
end
end
end

section
/-!
## The three negative forms and the common positive charge

The B comparison keeps its actual ordered pair, including the
switch at m = lambdaB. The secant sine estimate uses the full remaining
negative budget, so it also covers both negative primaries at once.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.BlockBounds
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope OrdinaryNegativeSlope Source
open Certificate (Row)

def canonicalQ (r s : ℝ) : Fin 3→ℝ := ![1,sec r,sec s]
def charge (f : Row) (z : ℝ) : ℝ := (109/200)*Explicit.cap f z

theorem zero_slope_upper {k q : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hq : 1≤q) : Vd R k q 0<(119/100)*q := by
  have hq0 : 0<q := by linarith
  have hr0 : 0≤k/q := div_nonneg (by linarith [hk.1]) hq0.le
  have hr : k/q≤751/1000 := (div_le_iff₀ hq0).2 (by nlinarith [hk.2])
  have hm := NegativeAPositiveTD.Curvature.shapeD0q_monotone
    (show k/q∈Icc (0:ℝ) 1 from ⟨hr0,by linarith⟩)
    (show (751/1000:ℝ)∈Icc (0:ℝ) 1 by norm_num) hr
  have hshape : (5/4:ℝ)<shape (751/1000) := by
    have hh := shape_sq (751/1000:ℝ)
    nlinarith [shape_pos (751/1000:ℝ)]
  have hb : NegativeAPositiveTD.Curvature.shapeD0q (751/1000)<119/100 := by
    dsimp [NegativeAPositiveTD.Curvature.shapeD0q]
    apply (div_lt_iff₀ (shape_pos _)).2
    nlinarith [Secondary.radius_bounds.2]
  have hmul := mul_lt_mul_of_pos_left (hm.trans_lt hb) hq0
  rw [Vd_normalized hq0]
  simpa [NegativeAPositiveTD.Curvature.shapeD0q,VaryingBFunctions.root,
    OrdinaryCurvatureBounds.shape,mul_comm] using hmul

theorem B_negative_lower {k m q d : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hq : q∈Icc (1:ℝ) (539/500))
    (hm : k≤ m) (hmhi : m≤69/50) (hd : d∈Icc 0 frameCap) :
    V R k q d≤V R (min q m) (max q m) d := by
  have hk0 : 0<k := by linarith [hk.1]
  have hq0 : 0<q := by linarith [hq.1]
  have hkq : k≤q := by linarith [hk.2,hq.1]
  have hqk : q≤2*k := by linarith [hk.1,hq.2]
  rcases le_total m q with hmq|hqm
  · rw [min_eq_right hmq,max_eq_left hmq]
    exact V_monotone_smaller (Real.sqrt_nonneg qCap) hq0 hd
      ⟨by linarith,hkq⟩ ⟨by linarith,hmq⟩ hm
  · rw [min_eq_left hqm,max_eq_right hqm]
    have hchord := V_chord_lower hq0 hqm (show m≤2*q by linarith [hq.1]) hd
    have htangent := V_tangent_zero hk0 hkq hqk hd
    have hupper := mul_le_mul_of_nonneg_right (zero_slope_upper hk hq.1).le hd.1
    have hqd : 0≤q*d := mul_nonneg hq0.le hd.1
    nlinarith

theorem negative_index (f : Row) (atG atH : Bool) {r s z d : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hd : d∈Icc 0 frameCap) (i : Fin 4) :
    ∃j : Fin 3,V R (Explicit.k f z) (canonicalQ r s j) d≤
      V R (pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i)
        (qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i) d := by
  rcases Explicit.ranges f hz with ⟨hk,hkc,hc,hkm,hm,hcap,hstrict⟩
  have hl := lambda_bounds atG atH hr hs hH
  fin_cases i
  · cases atH
    · exact ⟨0,by simp [pWeights,qWeights,canonicalQ,lambdaH]⟩
    · exact ⟨2,by simp [pWeights,qWeights,canonicalQ,lambdaH]⟩
  · cases atG
    · exact ⟨0,by simp [pWeights,qWeights,canonicalQ,lambdaG]⟩
    · exact ⟨1,by simp [pWeights,qWeights,canonicalQ,lambdaG]⟩
  · have hh := B_negative_lower hk hl.2.1 hkm (hm.trans hcap) hd
    cases atG
    · exact ⟨1,by simpa [pWeights,qWeights,canonicalQ,lambdaB] using hh⟩
    · exact ⟨0,by simpa [pWeights,qWeights,canonicalQ,lambdaB] using hh⟩
  · exact ⟨0,by simp [pWeights,qWeights,canonicalQ]⟩

theorem cap_lower (f : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    (539/500:ℝ)≤Explicit.cap f z := by
  cases f
  · have hzl : z∈Icc (0:ℝ) (3/20) := by simpa [Certificate.left,Certificate.right] using hz
    have hh := Explicit.low_m_ranges hzl
    change (539/500:ℝ)≤Explicit.m .low z
    linarith [hh.1]
  · norm_num [Explicit.cap]
  · norm_num [Explicit.cap]

theorem charge_bounds (f : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    0≤charge f z ∧ charge f z≤7521/10000 ∧
      (f≠.low → charge f z=58751/100000) := by
  have hlo := cap_lower f hz
  have hhi := (Explicit.ranges f hz).2.2.2.2.2.1
  refine ⟨by dsimp [charge]; positivity,by dsimp [charge]; linarith,?_⟩
  intro hf
  cases f <;> norm_num [charge,Explicit.cap] at *

theorem q_le_cap (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (i : Fin 4) :
    qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i≤Explicit.cap f z := by
  have hcap := cap_lower f hz
  have hm := (Explicit.ranges f hz).2.2.2.2.1
  have hl := lambda_bounds atG atH hr hs hH
  fin_cases i
  · exact hl.2.2.1.2.trans hcap
  · exact hl.1.2.trans hcap
  · exact max_le (hl.2.1.2.trans hcap) hm
  · change (1:ℝ)≤Explicit.cap f z
    linarith

theorem positive_lower (f : Row) (atG atH : Bool) {r s z d : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hd : d∈Icc 0 frameCap) (i : Fin 4) :
    -charge f z*d≤PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2)
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s) 3 i d := by
  have hc := q_le_cap f atG atH hz hr hs hH i
  have hp := pair_domain f atG atH hz hr hs hH i
  by_cases hi : i=3
  · subst i
    have hcap := cap_lower f hz
    have hcoef : GlobalGA.Secondary.diagonal-1/2≤charge f z := by
      dsimp [charge]
      linarith [Secondary.diagonal_bounds.2]
    simpa [PositiveTD.Hybrid.positive] using
      mul_le_mul_of_nonneg_right (neg_le_neg hcoef) hd.1
  · have hu := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap)
      radius_sq.le hp.1 hp.2.1 (show _≤2*_ by linarith [hp.2.2,hp.1]) hd
    have hm := mul_le_mul_of_nonneg_right hc hd.1
    simp only [PositiveTD.Hybrid.positive,ite_eq_right hi]
    dsimp [charge]
    nlinarith

theorem secant_sine_remaining {x S : ℝ} (hx : x∈Icc 0 frameCap)
    (hS : S∈Icc 0 frameCap) (hxS : x≤S) :
    sec x*Real.sin (frameCap-S)<129/200 := by
  have hc : 0<Real.cos x := by linarith [(transport_trig hx).1]
  have hsec : 0≤ sec x := div_nonneg (by norm_num) hc.le
  have hsine : Real.sin (frameCap-S)≤Real.sin (frameCap-x) := by
    have hS2 := hS.2
    have hx1 := hx.1
    simp only [frameCap] at hS2 ⊢
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith [Real.pi_gt_three]
    · linarith [Real.pi_gt_three]
    · linarith
  have hmul := mul_le_mul_of_nonneg_left hsine hsec
  have hid : sec x*Real.sin (frameCap-x)=
      Real.sin frameCap-Real.cos frameCap*Real.tan x := by
    rw [Real.sin_sub]
    dsimp [sec,SecantNormCurvature.secant]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
  rw [hid] at hmul
  have htan : 0≤Real.tan x := NegativeAPositiveTD.SecantCoordinate.tan_nonnegative hx
  have ht := transport_trig (show frameCap∈Icc 0 frameCap by
    exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hprod := mul_nonneg (show 0≤Real.cos frameCap by linarith [ht.1]) htan
  linarith [ht.2.2.2.1]

private theorem r66_fin4 {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) :
    ∀ i,P i := by
  intro i
  fin_cases i
  exacts [h0,h1,h2,h3]

theorem same_block_sine (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hS : r+s≤frameCap) (i : Fin 4) :
    qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i*Real.sin (frameCap-(r+s))≤
      pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i := by
  rcases Explicit.ranges f hz with ⟨hk,hkc,hc,hkm,hm,hcap,hstrict⟩
  have htotal : r+s∈Icc 0 frameCap := ⟨add_nonneg hr.1 hs.1,hS⟩
  have hr' : r∈Icc 0 frameCap := ⟨hr.1,by linarith [hs.1]⟩
  have hzero := secant_sine_remaining (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    htotal htotal.1
  simp only [sec,SecantNormCurvature.secant,Real.cos_zero,div_one,one_mul] at hzero
  have hA := secant_sine_remaining hr' htotal (by linarith [hs.1])
  have hE := secant_sine_remaining hs htotal (by linarith [hr.1])
  have hG : lambdaG atG r*Real.sin (frameCap-(r+s))≤Explicit.k f z := by
    cases atG <;> simp only [lambdaG,Bool.false_eq_true,↓reduceIte,one_mul] <;> linarith [hk.1]
  have hH : lambdaH atH s*Real.sin (frameCap-(r+s))≤Explicit.k f z := by
    cases atH <;> simp only [lambdaH,Bool.false_eq_true,↓reduceIte,one_mul] <;> linarith [hk.1]
  have hB : lambdaB atG r*Real.sin (frameCap-(r+s))≤Explicit.k f z := by
    cases atG <;> simp only [lambdaB,Bool.false_eq_true,↓reduceIte,one_mul] <;> linarith [hk.1]
  revert i
  apply r66_fin4
  · exact hH
  · exact hG
  · change max (lambdaB atG r) (Explicit.m f z)*Real.sin (frameCap-(r+s))≤
      min (lambdaB atG r) (Explicit.m f z)
    rcases le_total (Explicit.m f z) (lambdaB atG r) with hh|hh
    · rw [max_eq_left hh,min_eq_right hh]
      exact hB.trans hkm
    · rw [max_eq_right hh,min_eq_left hh]
      have hlam : 1≤lambdaB atG r := by
        cases atG
        · exact (secant_short hr).1
        · simp [lambdaB]
      have hsin := (transport_trig (show frameCap-(r+s)∈Icc 0 frameCap from
        ⟨by linarith,by linarith [htotal.1]⟩)).2.2.1
      have hupper := mul_le_mul_of_nonneg_right (hm.trans hcap) hsin
      nlinarith
  · change (1:ℝ)*Real.sin (frameCap-(r+s))≤Explicit.k f z
    linarith [hk.1]

theorem unit_negative_growth {k x y : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    (16/25)*(y-x)≤V R k 1 y-V R k 1 x := by
  have hk0 : 0<k := by linarith [hk.1]
  apply derivative_reserve
    (fun t ht => (V_hasDerivAt (R:=R) hk0 (by norm_num) ht).continuousAt.continuousWithinAt)
    (fun t ht => V_hasDerivAt (R:=R) hk0 (by norm_num) (Ioo_subset_Icc_self ht))
    (fun t ht => ?_) hx hy hxy
  have hh := NegativeAPositiveTD.NegativeSlope.lower_bound .ABfull hk0
    (show k≤1 by linarith [hk.2]) (show (1:ℝ)≤2*k by linarith [hk.1])
    (show (NegativeAPositiveTD.NegativeSlope.lowerRatio .ABfull:ℝ)*1≤k by
      simpa [NegativeAPositiveTD.NegativeSlope.lowerRatio] using hk.1)
    (show t∈Icc 0 (NegativeAPositiveTD.NegativeSlope.lowerAngle .ABfull:ℝ) by
      simpa [NegativeAPositiveTD.NegativeSlope.lowerAngle,frameCap] using Ioo_subset_Icc_self ht)
  simpa [NegativeAPositiveTD.NegativeSlope.lowerValue] using hh.le

theorem same_negative (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤z) (i : Fin 4) :
    V R (pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i) (z-(r+s))≤
    PositiveTD.Hybrid.block R (GlobalGA.Secondary.diagonal-1/2)
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s) 3 i
      (frameCap-z) (frameCap-(r+s)) := by
  have hz' := Explicit.frame_domain f hz
  have hp := pair_domain f atG atH hz hr hs hH i
  have htotal := add_nonneg hr.1 hs.1
  by_cases hi : i=3
  · subst i
    have hh := unit_negative_growth (Explicit.ranges f hz).1
      (show z-(r+s)∈Icc 0 frameCap from ⟨by linarith,by linarith [hz'.2]⟩)
      (show frameCap-(r+s)∈Icc 0 frameCap from ⟨by linarith [hz'.2],by linarith⟩)
      (by linarith [hz'.2])
    have hcharge := mul_le_mul_of_nonneg_right
      (show GlobalGA.Secondary.diagonal-1/2≤16/25 by linarith [Secondary.diagonal_bounds.2])
      (show 0≤frameCap-z by linarith [hz'.2])
    simp only [PositiveTD.Hybrid.block,pWeights,qWeights,Matrix.cons_val,↓reduceIte]
    linarith
  · have hh := NegativeAPositiveTD.SameBlock.negative_surplus hp.1.le
      (show frameCap-z∈Icc 0 (frameCap-(r+s)) from ⟨by linarith [hz'.2],by linarith⟩)
      (show frameCap-(r+s)∈Icc 0 frameCap from ⟨by linarith [hz'.2],by linarith⟩)
      (same_block_sine f atG atH hz hr hs (hS.trans hz'.2) i)
    simpa [PositiveTD.Hybrid.block,hi,show frameCap-(r+s)-(frameCap-z)=z-(r+s) by ring] using hh

theorem same_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s∈Icc z frameCap) (i : Fin 4) :
    PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2)
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s) 3 i (r+s-z)≤
    PositiveTD.Hybrid.block R (GlobalGA.Secondary.diagonal-1/2)
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s) 3 i
      (frameCap-z) (frameCap-(r+s)) := by
  have hz' := Explicit.frame_domain f hz
  have hp := pair_domain f atG atH hz hr hs hH i
  have htotal := add_nonneg hr.1 hs.1
  by_cases hi : i=3
  · subst i
    have hh := unit_negative_growth (Explicit.ranges f hz).1
      (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
      (show frameCap-(r+s)∈Icc 0 frameCap from ⟨by linarith [hS.2],by linarith⟩)
      (by linarith [hS.2])
    have hcharge := mul_le_mul_of_nonneg_right
      (show GlobalGA.Secondary.diagonal-1/2≤16/25 by linarith [Secondary.diagonal_bounds.2])
      (show 0≤frameCap-(r+s) by linarith [hS.2])
    simp only [V_zero,sub_zero] at hh
    simp only [PositiveTD.Hybrid.positive,PositiveTD.Hybrid.block,pWeights,qWeights,
      Matrix.cons_val,↓reduceIte]
    linarith
  · have hh := NegativeAPositiveTD.SameBlock.positive_surplus hp.1.le hp.2.2
      (show frameCap-z∈Icc 0 frameCap from ⟨by linarith [hz'.2],by linarith [hz'.1]⟩)
      (show frameCap-(r+s)∈Icc 0 (frameCap-z) from ⟨by linarith [hS.2],by linarith [hS.1]⟩)
    simpa [PositiveTD.Hybrid.positive,PositiveTD.Hybrid.block,hi,
      show frameCap-z-(frameCap-(r+s))=r+s-z by ring] using hh

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.BlockBounds
end
end
end

section
/-!
## The remaining unit-pair chord reserve

The low row uses the actual chord from 0.15 to the angular cap and
concavity on the entire interval to extend that chord to every smaller
left endpoint. The high rows use the uniform 0.64 derivative reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.BlockBounds
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope OrdinaryNegativeSlope
open Certificate (Row)

theorem low_V_cap : (611/1000:ℝ)<V R (13/20) 1 frameCap := by
  have hN := pairNorm_pos (p:=(13/20:ℝ)) (q:=1) (t:=-frameCap)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hN2 := pairNorm_sq (p:=(13/20:ℝ)) (q:=1) (t:=-frameCap)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hZ := pairNorm_pos (p:=(13/20:ℝ)) (q:=1) (t:=0)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hZ2 := pairNorm_sq (p:=(13/20:ℝ)) (q:=1) (t:=0)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_neg,Real.sin_zero] at hN2 hZ2
  have hZlo : (5963/5000:ℝ)<pairNorm (13/20) 1 0 := by nlinarith
  have hNhi : pairNorm (13/20) 1 (-frameCap)<7649/10000 := by
    nlinarith [cap_sin_lower]
  have hgap : (4277/10000:ℝ)<pairNorm (13/20) 1 0-pairNorm (13/20) 1 (-frameCap) := by
    linarith
  have hprod := mul_lt_mul_of_pos_left hgap (by norm_num : (0:ℝ)<19787/10000)
  have hR := mul_lt_mul_of_pos_right sqrt_cap_lower
    (show 0<pairNorm (13/20) 1 0-pairNorm (13/20) 1 (-frameCap) by linarith)
  have hc := (transport_trig (show frameCap∈Icc 0 frameCap from
    ⟨by norm_num [frameCap],le_rfl⟩)).1
  dsimp [V]
  nlinarith

theorem low_V_short : V R (13/20) 1 (3/20)<81/500 := by
  have hs : (5963/5000:ℝ)<shape (13/20) := by
    nlinarith [shape_sq (13/20:ℝ),shape_pos (13/20:ℝ)]
  have hd : Vd R (13/20) 1 0<27/25 := by
    rw [Vd_normalized (by norm_num : (0:ℝ)<1)]
    simp only [Real.sin_zero,Real.cos_zero,div_one,neg_zero,zero_add,mul_one,one_mul,
      VaryingBFunctions.root_zero]
    apply (div_lt_iff₀ (shape_pos _)).2
    linarith [Secondary.radius_bounds.2]
  have ht := V_tangent_zero (p:=(13/20:ℝ)) (q:=1)
    (by norm_num) (by norm_num) (by norm_num)
    (show (3/20:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  linarith

theorem low_unit_chord {z : ℝ} (hz : z∈Icc (0:ℝ) (3/20)) :
    (4/5)*(frameCap-z)<V R (13/20) 1 frameCap-V R (13/20) 1 z := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by norm_num [frameCap]; linarith [hz.2]⟩
  have hcapIcc : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hconc := V_concave (R:=R) (p:=(13/20:ℝ)) (q:=1)
    (Real.sqrt_nonneg qCap) radius_sq.le (by norm_num) (by norm_num) (by norm_num)
  have hcap := low_V_cap
  have hshort := low_V_short
  have hfc : frameCap=(7/10:ℝ) := rfl
  rw [hfc] at hz' hcapIcc hconc hcap ⊢
  obtain ⟨w,hw⟩ : ∃ w : ℝ, w=7/10-z := ⟨_,rfl⟩
  have hw0 : 0<w := by rw [hw]; linarith [hz.2]
  have ha : 0≤(7/10-3/20)/w := div_nonneg (by norm_num) hw0.le
  have hb : 0≤(3/20-z)/w := div_nonneg (by linarith [hz.2]) hw0.le
  have hab : (7/10-3/20)/w+(3/20-z)/w=1 := by
    rw [← add_div,div_eq_one_iff_eq hw0.ne',hw]; ring
  have hh := hconc.2 hz' hcapIcc ha hb hab
  have hpoint : (7/10-3/20)/w*z+(3/20-z)/w*(7/10)=3/20 := by
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,← add_div,div_eq_iff hw0.ne',hw]; ring
  simp only [smul_eq_mul,hpoint] at hh
  have hmul := mul_le_mul_of_nonneg_left hh hw0.le
  have hidentity : w*((7/10-3/20)/w*V R (13/20) 1 z+(3/20-z)/w*V R (13/20) 1 (7/10))=
      (7/10-3/20)*V R (13/20) 1 z+(3/20-z)*V R (13/20) 1 (7/10) := by
    field_simp
  rw [hidentity,hw] at hmul
  have hgap : (449/1000:ℝ)<V R (13/20) 1 (7/10)-V R (13/20) 1 (3/20) := by linarith
  have hprod := mul_lt_mul_of_pos_left hgap (show (0:ℝ)<7/10-z by linarith [hz.2])
  linarith

theorem separated_V_charge (f : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    charge f z*(frameCap-z)≤V R (Explicit.k f z) 1 frameCap-V R (Explicit.k f z) 1 z := by
  have hz' := Explicit.frame_domain f hz
  have hp : 0≤frameCap-z := sub_nonneg.mpr hz'.2
  rcases eq_or_ne f .low with rfl|hf
  · have hz0 : z∈Icc (0:ℝ) (3/20) := by
      have h := hz
      norm_num [Certificate.left,Certificate.right] at h
      exact h
    have hh := low_unit_chord hz0
    have hc := mul_le_mul_of_nonneg_right (charge_bounds .low hz).2.1 hp
    have hk : Explicit.k .low z=13/20 := by simp [Explicit.k,Certificate.k]
    rw [hk]
    simp only [frameCap] at hh hc hp ⊢
    linarith
  · have hh := unit_negative_growth (Explicit.ranges f hz).1 hz'
      (show frameCap∈Icc 0 frameCap from ⟨by norm_num [frameCap],le_rfl⟩) hz'.2
    rw [(charge_bounds f hz).2.2 hf]
    simp only [frameCap] at hh hp ⊢
    linarith

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.BlockBounds
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.BlockBounds
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope Source
open Certificate (Row)

abbrev canonicalQ := JointNegativeAETD2.BlockBounds.canonicalQ

theorem B_negative_lower {k m q d : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hq : q∈Icc (1:ℝ) (539/500))
    (hm : k≤ m) (hmhi : m≤7/5) (hd : d∈Icc 0 frameCap) :
    V R k q d≤V R (min q m) (max q m) d := by
  have hk0 : 0<k := by linarith [hk.1]
  have hq0 : 0<q := by linarith [hq.1]
  have hkq : k≤q := by linarith [hk.2,hq.1]
  have hqk : q≤2*k := by linarith [hk.1,hq.2]
  rcases le_total m q with hmq|hqm
  · rw [min_eq_right hmq,max_eq_left hmq]
    exact V_monotone_smaller (Real.sqrt_nonneg qCap) hq0 hd
      ⟨by linarith,hkq⟩ ⟨by linarith,hmq⟩ hm
  · rw [min_eq_left hqm,max_eq_right hqm]
    have hchord := V_chord_lower hq0 hqm (show m≤2*q by linarith [hq.1]) hd
    have htangent := V_tangent_zero hk0 hkq hqk hd
    have hupper := mul_le_mul_of_nonneg_right
      (JointNegativeAETD2.BlockBounds.zero_slope_upper hk hq.1).le hd.1
    have hqd := mul_nonneg hq0.le hd.1
    nlinarith

theorem negative_index (f : Row) (atG atH : Bool) {r s z d : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hd : d∈Icc 0 frameCap) (i : Fin 5) :
    ∃j : Fin 3,V R (Explicit.k f z) (canonicalQ r s j) d≤
      V R (pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i)
        (qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i) d := by
  have hc := Explicit.ranges f hz
  have hl := JointNegativeAETD2.Source.lambda_bounds atG atH hr hs hH
  fin_cases i
  · cases atH
    · exact ⟨0,by simp [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        lambdaH,JointNegativeAETD2.Source.lambdaH]⟩
    · exact ⟨2,by simp [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        lambdaH,JointNegativeAETD2.Source.lambdaH]⟩
  · cases atG
    · exact ⟨0,by simp [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        lambdaG,JointNegativeAETD2.Source.lambdaG]⟩
    · exact ⟨1,by simp [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        lambdaG,JointNegativeAETD2.Source.lambdaG]⟩
  · have hh := B_negative_lower hc.k_domain hl.2.1 hc.k_le_m (hc.m_le_c.trans hc.c_domain.2) hd
    cases atG
    · exact ⟨1,by simpa [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        lambdaB,JointNegativeAETD2.Source.lambdaB] using hh⟩
    · exact ⟨0,by simpa [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        lambdaB,JointNegativeAETD2.Source.lambdaB] using hh⟩
  · refine ⟨0,?_⟩
    by_cases ho : ordinaryD atH (Explicit.c f z)
    · simp only [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        Fin.reduceFinMk,Fin.isValue,Matrix.cons_val,ho,↓reduceIte]
      exact V_monotone_smaller (Real.sqrt_nonneg qCap) (q:=1) (by norm_num) hd
        ⟨by linarith [hc.k_domain.1],by linarith [hc.k_domain.2]⟩
        ⟨by linarith [hc.c_domain.1],ho.2.le⟩ (hc.k_le_m.trans hc.m_le_c)
    · simp [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,ho]
  · exact ⟨0,by simp [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ]⟩

theorem cost_max_coefficient {c S : ℝ} (hS : S∈Icc 0 frameCap) :
    (109/200)*max (sec S) c≤Penalty.cost c S := by
  have hs := (JointNegativeAETD2.CommonGain.full_secant_domain hS).1
  by_cases hc : c<1
  · rw [max_eq_left (by linarith),Penalty.cost,ite_eq_left hc]
  · simp only [Penalty.cost,hc,↓reduceIte]
    rcases le_total (sec S) c with h|h
    · rw [max_eq_right h]
      exact le_max_of_le_right (le_max_left _ _)
    · rw [max_eq_left h]
      exact le_max_of_le_right (le_max_right _ _)

theorem incident_secants (atG atH : Bool) {r s : ℝ}
    (hr : 0≤r) (hs : 0≤ s) (hS : r+s≤frameCap) :
    lambdaG atG r≤ sec (r+s) ∧ lambdaB atG r≤ sec (r+s) ∧
      lambdaH atH s≤ sec (r+s) ∧ lambdaD atH s≤ sec (r+s) := by
  have htotal : r+s∈Icc 0 frameCap := ⟨add_nonneg hr hs,hS⟩
  have h1 := (JointNegativeAETD2.CommonGain.full_secant_domain htotal).1
  have hA := Penalty.secant_monotone ⟨hr,by linarith⟩ htotal (by linarith)
  have hE := Penalty.secant_monotone ⟨hs,by linarith⟩ htotal (by linarith)
  cases atG <;> cases atH <;>
    simp only [lambdaG,lambdaB,lambdaH,lambdaD,JointNegativeAETD2.Source.lambdaG,
      JointNegativeAETD2.Source.lambdaB,JointNegativeAETD2.Source.lambdaH,
      JointNegativeAETD2.Source.lambdaD,ite_true] <;>
    exact ⟨by assumption,by assumption,by assumption,by assumption⟩

theorem q_charge_le (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : 0≤r) (hs : 0≤ s) (hS : r+s≤frameCap) (i : Fin 5) :
    (109/200)*qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i≤
      Penalty.cost (Explicit.c f z) (r+s) := by
  have hc := Explicit.ranges f hz
  have hl := incident_secants atG atH hr hs hS
  have h1 := (JointNegativeAETD2.CommonGain.full_secant_domain ⟨add_nonneg hr hs,hS⟩).1
  have hq : qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i≤
      max (sec (r+s)) (Explicit.c f z) := by
    fin_cases i
    · exact hl.2.2.1.trans (le_max_left _ _)
    · exact hl.1.trans (le_max_left _ _)
    · exact max_le (hl.2.1.trans (le_max_left _ _)) (hc.m_le_c.trans (le_max_right _ _))
    · exact h1.trans (le_max_left _ _)
    · exact h1.trans (le_max_left _ _)
  exact (mul_le_mul_of_nonneg_left hq (by norm_num)).trans
    (cost_max_coefficient ⟨add_nonneg hr hs,hS⟩)

theorem positive_lower (f : Row) (atG atH : Bool) {r s z d : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (hd : d∈Icc 0 frameCap) (i : Fin 5) :
    -Penalty.cost (Explicit.c f z) (r+s)*d≤
      PositiveTD.Hybrid.positive R (Penalty.cost (Explicit.c f z) (r+s))
        (pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
        (qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
        (distinguished atH (Explicit.c f z)) i d := by
  by_cases hi : i=distinguished atH (Explicit.c f z)
  · simp [PositiveTD.Hybrid.positive,hi]
  · have hp := pair_domain f atG atH hz hr hs hH i
    have hu := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap)
      radius_sq.le hp.1 hp.2.1 (show _≤2*_ by linarith [hp.2.2,hp.1]) hd
    have hq := mul_le_mul_of_nonneg_right (q_charge_le f atG atH hz hr.1 hs.1 hS i) hd.1
    simp only [PositiveTD.Hybrid.positive,ite_eq_right hi]
    linarith

theorem same_block_sine (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hS : r+s≤frameCap) (i : Fin 5) :
    qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i*
        Real.sin (frameCap-(r+s))≤
      pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i := by
  have hc := Explicit.ranges f hz
  have htotal : r+s∈Icc 0 frameCap := ⟨add_nonneg hr.1 hs.1,hS⟩
  have hr' : r∈Icc 0 frameCap := ⟨hr.1,by linarith [hs.1]⟩
  have hzero := JointNegativeAETD2.BlockBounds.secant_sine_remaining
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) htotal htotal.1
  simp only [JointNegativeAETD2.Source.sec,SecantNormCurvature.secant,
    Real.cos_zero,div_one,one_mul] at hzero
  have hA := JointNegativeAETD2.BlockBounds.secant_sine_remaining hr' htotal (by linarith [hs.1])
  have hE := JointNegativeAETD2.BlockBounds.secant_sine_remaining hs htotal (by linarith [hr.1])
  have hG : lambdaG atG r*Real.sin (frameCap-(r+s))≤Explicit.k f z := by
    cases atG <;> simp only [lambdaG,JointNegativeAETD2.Source.lambdaG,Bool.false_eq_true,↓reduceIte] <;>
      linarith [hc.k_domain.1]
  have hH : lambdaH atH s*Real.sin (frameCap-(r+s))≤Explicit.k f z := by
    cases atH <;> simp only [lambdaH,JointNegativeAETD2.Source.lambdaH,Bool.false_eq_true,↓reduceIte] <;>
      linarith [hc.k_domain.1]
  have hB : lambdaB atG r*Real.sin (frameCap-(r+s))≤Explicit.k f z := by
    cases atG <;> simp only [lambdaB,JointNegativeAETD2.Source.lambdaB,Bool.false_eq_true,↓reduceIte] <;>
      linarith [hc.k_domain.1]
  fin_cases i
  · exact hH
  · exact hG
  · change max (lambdaB atG r) (Explicit.m f z)*Real.sin (frameCap-(r+s))≤
      min (lambdaB atG r) (Explicit.m f z)
    rcases le_total (Explicit.m f z) (lambdaB atG r) with hh|hh
    · rw [max_eq_left hh,min_eq_right hh]
      exact hB.trans hc.k_le_m
    · rw [max_eq_right hh,min_eq_left hh]
      have hlam : 1≤lambdaB atG r := by
        cases atG
        · exact (JointNegativeAETD2.Source.secant_short hr).1
        · simp [lambdaB,JointNegativeAETD2.Source.lambdaB]
      have hsin := (transport_trig (show frameCap-(r+s)∈Icc 0 frameCap from
        ⟨by linarith,by linarith [htotal.1]⟩)).2.2.1
      have hupper := mul_le_mul_of_nonneg_right (hc.m_le_c.trans hc.c_domain.2) hsin
      nlinarith
  · by_cases ho : ordinaryD atH (Explicit.c f z)
    · simp only [pWeights,qWeights,Fin.reduceFinMk,Matrix.cons_val,ho,↓reduceIte,one_mul]
      linarith [hc.c_domain.1]
    · simp only [pWeights,qWeights,Fin.reduceFinMk,Matrix.cons_val,ho,↓reduceIte,one_mul]
      linarith [hc.k_domain.1]
  · change (1:ℝ)*Real.sin (frameCap-(r+s))≤Explicit.k f z
    linarith [hc.k_domain.1]

theorem same_negative (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤z) (i : Fin 5)
    (hi : i≠distinguished atH (Explicit.c f z)) :
    V R (pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i) (z-(r+s))≤
    PositiveTD.Hybrid.block R (Penalty.cost (Explicit.c f z) (r+s))
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
      (distinguished atH (Explicit.c f z)) i (frameCap-z) (frameCap-(r+s)) := by
  have hz' := Explicit.frame_domain f hz
  have hp := pair_domain f atG atH hz hr hs hH i
  have htotal := add_nonneg hr.1 hs.1
  have hh := NegativeAPositiveTD.SameBlock.negative_surplus hp.1.le
    (show frameCap-z∈Icc 0 (frameCap-(r+s)) from ⟨by linarith [hz'.2],by linarith⟩)
    (show frameCap-(r+s)∈Icc 0 frameCap from ⟨by linarith [hz'.2],by linarith⟩)
    (same_block_sine f atG atH hz hr hs (hS.trans hz'.2) i)
  simpa [PositiveTD.Hybrid.block,hi,show frameCap-(r+s)-(frameCap-z)=z-(r+s) by ring] using hh

theorem same_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s∈Icc z frameCap) (i : Fin 5)
    (hi : i≠distinguished atH (Explicit.c f z)) :
    PositiveTD.Hybrid.positive R (Penalty.cost (Explicit.c f z) (r+s))
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
      (distinguished atH (Explicit.c f z)) i (r+s-z)≤
    PositiveTD.Hybrid.block R (Penalty.cost (Explicit.c f z) (r+s))
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
      (distinguished atH (Explicit.c f z)) i (frameCap-z) (frameCap-(r+s)) := by
  have hz' := Explicit.frame_domain f hz
  have hp := pair_domain f atG atH hz hr hs hH i
  have hh := NegativeAPositiveTD.SameBlock.positive_surplus hp.1.le hp.2.2
    (show frameCap-z∈Icc 0 frameCap from ⟨by linarith [hz'.2],by linarith [hz'.1]⟩)
    (show frameCap-(r+s)∈Icc 0 (frameCap-z) from ⟨by linarith [hS.2],by linarith [hS.1]⟩)
  simpa [PositiveTD.Hybrid.positive,PositiveTD.Hybrid.block,hi,
    show frameCap-z-(frameCap-(r+s))=r+s-z by ring] using hh

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.BlockBounds
end
end
end
