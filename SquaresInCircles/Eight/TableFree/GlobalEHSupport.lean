module

public import SquaresInCircles.Eight.TableFree.GlobalEHScalar

/-!
# The common endpoint and error supports on the original EH--HG--GA path

Every support uses the actual shifted corner disk and the unchanged
common marker.  Outer rotated endpoints and the genuine flat-core
negative primary are distinguished by their original feasible axes.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalEH

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign GlobalOuterAnchor

theorem endpoint_support (s : State) : unsigned s+lam*s.a<endpointCap := by
  by_cases hcore : s.branch.type=0
  · have ha := (core_bounds s hcore).1
    have hb := s.canonical.trans ha
    have hlo := primary_lower s
    have hmarker : unsigned s≤8*(7/12-s.a)+(11/10)*s.b := by
      cases hbr : s.branch <;> simp [hbr,Branch.type] at hcore
      all_goals
        dsimp [unsigned]
        rw [hbr]
        dsimp [FramePair.label]
        nlinarith [s.b_nonneg]
    dsimp [lam,endpointCap]
    linarith
  · have hm := (outer_marker_bounds s hcore).2
    have hs := state_support s (lam+eta) mass
    let n := Real.sqrt ((lam+eta)^2+mass^2)
    have hn : n^2=(lam+eta)^2+mass^2 := Real.sq_sqrt (by positivity)
    have hR := CommonQuarter.radius_sq
    have hprod : (CommonQuarter.radius*n)^2=Q0*((lam+eta)^2+mass^2) := by
      rw [mul_pow,hR,hn]
    have hstrict : CommonQuarter.radius*n<
        endpointCap+(lam+eta+mass)/2+eta*axialLower := by
      dsimp [endpointCap,lam,eta,mass,axialLower,Q0] at *
      nlinarith
    have ha := FrameLowArc.a0_bounds.1
    change axialLower<a0 at ha
    change (lam+eta)*s.a+mass*s.b≤CommonQuarter.radius*n-(lam+eta+mass)/2 at hs
    dsimp [lam,eta,mass] at *
    linarith

theorem path_base : pathBase<Real.pi+3*lam-2*endpointCap := by
  have hh := Arithmetic.pi_hand_enclosure.1
  dsimp [pathBase,lam,endpointCap]
  linarith

def primaryError (s : State) (d : ℝ) : ℝ :=
  d+lam*(width d-1-s.a*Real.sin d-s.b*(1-Real.cos d))

def zeroError (s : State) (d : ℝ) : ℝ :=
  d+lam*(width d-1-s.a*Real.sin d+s.b*(1-Real.cos d))

def rotatedCost (s : State) (d : ℝ) : ℝ :=
  d+lam*(width d-1)-unsigned s-lam*(s.a*Real.cos d+s.b*Real.sin d)

def lowCost (s t : State) (primary : Bool) (d : ℝ) : ℝ :=
  if primary then -unsigned t-lam*t.a+primaryError s d else rotatedCost t d

@[simp] theorem primaryError_zero (s : State) : primaryError s 0=0 := by
  norm_num [primaryError,width]

@[simp] theorem zeroError_zero (s : State) : zeroError s 0=0 := by
  norm_num [zeroError,width]

theorem rotated_positive_delete (s : State) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    -endpointCap+(9/100)*x<rotatedCost s x := by
  have tr := transport_trig hx
  have hsin := Real.sin_le_self hx.1
  have hcos := sub_nonneg.mpr tr.2.1
  have ha := (coordinates s).1
  have hb := (coordinates s).2.2.2.2
  have hp1 := mul_nonneg (show 0≤s.a-1/2 by linarith) hcos
  have hp2 := mul_nonneg (show 0≤9/10-s.b by linarith) tr.2.2.1
  have he := endpoint_support s
  dsimp [rotatedCost,width,lam] at *
  rw [abs_of_nonneg tr.2.2.1]
  nlinarith

theorem rotated_negative_delete (s : State) (houter : s.branch.type≠0)
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    -endpointCap+(9/100)*z<rotatedCost s (-z) := by
  have tr := transport_trig hz
  have hm := (outer_marker_bounds s houter).2
  have hs := state_support s (eta+lam*Real.cos z) (mass-lam*Real.sin z)
  have hr := rotated_radical_bound hz
  have ha := FrameLowArc.a0_bounds.1
  change axialLower<a0 at ha
  change (eta+lam*Real.cos z)*s.a+(mass-lam*Real.sin z)*s.b≤
    CommonQuarter.radius*rotatedNorm z-
      (eta+lam*Real.cos z+mass-lam*Real.sin z)/2 at hs
  dsimp [rotatedCost,width,rotatedThreshold,lam,eta,mass] at *
  rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg tr.2.2.1]
  nlinarith

theorem rotated_delete (s : State) (houter : s.branch.type≠0)
    {d : ℝ} (hd : |d|≤frameCap) :
    -endpointCap+(9/100)*|d|<rotatedCost s d := by
  by_cases hp : 0≤d
  · rw [abs_of_nonneg hp]
    exact rotated_positive_delete s ⟨hp,(le_abs_self d).trans hd⟩
  · have hz : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hh := rotated_negative_delete s houter hz
    simpa only [neg_neg,abs_of_neg (lt_of_not_ge hp)] using hh

theorem half_angle_norm {x : ℝ} (hx : x∈Icc 0 frameCap) :
    Real.sqrt ((Real.sin x)^2+(1-Real.cos x)^2)=2*Real.sin (x/2) := by
  have ht := transport_trig (show x/2∈Icc 0 frameCap by constructor <;> linarith [hx.1,hx.2])
  have hdouble := Real.cos_two_mul (x/2)
  have hhalf := Real.sin_sq_add_cos_sq (x/2)
  have hunit := Real.sin_sq_add_cos_sq x
  have hid : (Real.sin x)^2+(1-Real.cos x)^2=(2*Real.sin (x/2))^2 := by
    have hc : Real.cos x=2*(Real.cos (x/2))^2-1 := by simpa using hdouble
    nlinarith
  have hp : 0≤2*Real.sin (x/2) := mul_nonneg (by norm_num) ht.2.2.1
  rw [hid,Real.sqrt_sq_eq_abs,abs_of_nonneg hp]

theorem primaryError_positive (s : State) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    positiveCost x≤primaryError s x := by
  have tr := transport_trig hx
  have hs := state_support s (Real.sin x) (1-Real.cos x)
  rw [half_angle_norm hx] at hs
  dsimp [primaryError,positiveCost,width,lam]
  rw [abs_of_nonneg tr.2.2.1]
  nlinarith

theorem zeroError_positive (s : State) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    positiveCost x≤zeroError s x := by
  have hh := primaryError_positive s hx
  have hp := mul_nonneg s.b_nonneg (sub_nonneg.mpr (Real.cos_le_one x))
  dsimp [primaryError,zeroError,lam] at *
  linarith

theorem zeroError_negative (s : State) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    negativeCost z≤zeroError s (-z) := by
  have tr := transport_trig hz
  have ha := primary_lower s
  have hp1 := mul_nonneg (show 0≤s.a-primaryLower by exact ha.le) tr.2.2.1
  have hp2 := mul_nonneg s.b_nonneg (sub_nonneg.mpr (Real.cos_le_one z))
  dsimp [negativeCost,zeroError,width,lam]
  rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg tr.2.2.1]
  nlinarith

def lowOwner (primary : Bool) : Fin 4 := if primary then 1 else 0

/-- A quarter reduction retains an actual weak axis at the original
error.  The separate `error` is only a scalar stress parameter. -/
structure LowReduction (s t : State) (d : ℝ) where
  primary : Bool
  feasible : s.Feasible t (lowOwner primary) (Real.pi/2+d)
  error : ℝ
  error_nonneg : 0≤error
  error_eq : error=0 ∨ error=d
  cost_gain : -endpointCap+primaryError s error+(9/100)*|d-error|<lowCost s t primary d

theorem low_reduction (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (hs : transverse s≤0) (ht : 0≤transverse t)
    (j : Fin 4) (hj : j=0 ∨ j=1)
    (hf : s.Feasible t j (Real.pi/2+d)) : Nonempty (LowReduction s t d) := by
  have hsecondary (hm : s.Feasible t 0 (Real.pi/2+d)) : Nonempty (LowReduction s t d) := by
    have ho := GlobalZeroLow.secondary_target_outer s t hd hs ht hm
    refine ⟨⟨false,hm,0,le_rfl,Or.inl rfl,?_⟩⟩
    simpa [lowCost] using rotated_delete t ho hd
  rcases hj with rfl | rfl
  · exact hsecondary hf
  · by_cases hdpos : 0≤d
    · refine ⟨⟨true,hf,d,hdpos,Or.inr rfl,?_⟩⟩
      have he := endpoint_support t
      simp only [lowCost,if_true,sub_self,abs_zero,mul_zero,add_zero]
      linarith
    · by_cases hsecondaryAxis : s.Feasible t 0 (Real.pi/2+d)
      · exact hsecondary hsecondaryAxis
      · have hz : -d∈Ioc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
        have hg := GlobalQuarterNegativePrimary.exceptional_gain s t hz hs ht
          (by simpa using hf) (by simpa using hsecondaryAxis)
        have tr := transport_trig (show -d∈Icc 0 frameCap from ⟨hz.1.le,hz.2⟩)
        have he := endpoint_support t
        have hcost : (9/100)*(-d)<primaryError s d := by
          dsimp [primaryError,width,lam]
          have hsin : Real.sin d≤0 := by
            simpa only [Real.sin_neg,neg_nonneg] using tr.2.2.1
          rw [abs_of_nonpos hsin]
          simp only [Real.sin_neg,Real.cos_neg] at hg
          nlinarith
        refine ⟨⟨true,hf,0,le_rfl,Or.inl rfl,?_⟩⟩
        simp only [lowCost,if_true,primaryError_zero,add_zero,sub_zero,
          abs_of_neg (lt_of_not_ge hdpos)]
        linarith

end SquaresInCircles.Eight.TableFree.GlobalEH
