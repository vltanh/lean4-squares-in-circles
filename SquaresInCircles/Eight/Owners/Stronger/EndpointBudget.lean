module

public import SquaresInCircles.Eight.Owners.E.NegativePairMinimum
public import SquaresInCircles.Eight.Owners.Stronger.EndpointStress

/-!
# Eight squares: the stronger original H/D/E budget for the one-negative anchor barrier

The same original mixed-owner split is exhausted at
coefficient 41/40 and reserve 27/160000. Signed rotation, short positive
remainder, and both negative remainder ranges have all been reproved for
these constants. No radial boundary or intermediate sign is required.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace StrongerEndpointBudget
open EndpointBudgetScalars EndpointECharge StrongerEndpointScalars StrongerEndpointStress

theorem positive_remainder {E : SignedPoint} {r : ℝ}
    (hEs : E.Sorted) (hEc : E.circle≤qCap) (hr : r∈Icc 0 frameCap) :
    ∃ l∈Icc (4/5 : ℝ) 2,
      baseline l+l*EPairMinimum.J E.a E.y r-StrongerEndpointScalars.charge*r+S0<2-StrongerEndpointScalars.epsilon := by
  by_cases hrh : r≤1/2
  · have hshort : r∈Icc 0 (1/2 : ℝ) := ⟨hr.1,hrh⟩
    obtain ⟨l,hl,hscalar⟩ := StrongerEndpointScalars.positive_short_choice hshort
    have hJ := mul_le_mul_of_nonneg_left (positive_J_short hEs hEc hshort)
      (show 0≤l by linarith [hl.1])
    exact ⟨l,hl,by linarith⟩
  · have hJ := mul_le_mul_of_nonneg_left (positive_J_long hEc hr)
      (by norm_num : (0:ℝ)≤4/5)
    exact ⟨4/5,by norm_num,by
      linarith [StrongerEndpointScalars.positive_long
        (show r∈Icc (1/2 : ℝ) frameCap from ⟨by linarith,hr.2⟩)]⟩

theorem primary_H_remainder {q r : ℝ} {E H : SignedPoint}
    (hEs : E.Sorted) (hEc : E.AvoidsCore) (hEcont : E.Contained q)
    (hHs : H.Sorted) (hHc : H.AvoidsCore) (hHcont : H.Contained q)
    (hq : q≤qCap) (hyE : E.y≤0) (hr : |r|≤frameCap)
    (hEH : quarterFeasible E H r 1) :
    ∃ l∈Icc (4/5 : ℝ) 2,
      baseline l+l*JH E r-StrongerEndpointScalars.charge*r+S0<2-StrongerEndpointScalars.epsilon := by
  by_cases hr0 : 0≤r
  · have hr' : r∈Icc 0 frameCap := ⟨hr0,(le_abs_self r).trans hr⟩
    obtain ⟨l,hl,hstress⟩ := positive_remainder hEs (hEcont.trans hq) hr'
    exact ⟨l,hl,by rw [JH_positive hyE hr']; exact hstress⟩
  · have hz : -r∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs r).trans hr⟩
    have hEH' : quarterFeasible E H (-(-r)) 1 := by rw [neg_neg]; exact hEH
    obtain ⟨hb,hbstrong⟩ := negative_EH_tangent hEs hEc hEcont hHs hHc hHcont
      hq hyE hz hEH'
    by_cases hzsmall : -r≤6/25
    · have hJ : JH E r≤negativeGain (183/200) (-r) := by
        have h := JH_negative_bound hEs hEc hEcont hq
          (show -E.y+1/2≤183/200 by linarith) hz
        rwa [neg_neg] at h
      have hm := mul_le_mul_of_nonneg_left hJ (by norm_num : (0:ℝ)≤7/6)
      refine ⟨7/6,by norm_num,?_⟩
      have hscalar := StrongerEndpointScalars.negative_short
        (show -r∈Icc 0 (6/25 : ℝ) from ⟨hz.1,hzsmall⟩)
      linarith
    · have hb' := hbstrong (show 3/25≤-r by linarith)
      have hJ : JH E r≤negativeGain (4/5) (-r) := by
        have h := JH_negative_bound hEs hEc hEcont hq
          (show -E.y+1/2≤4/5 by linarith) hz
        rwa [neg_neg] at h
      have hm := mul_le_mul_of_nonneg_left hJ (by norm_num : (0:ℝ)≤7/4)
      refine ⟨7/4,by norm_num,?_⟩
      have hscalar := StrongerEndpointScalars.negative_long
        (show -r∈Icc (6/25 : ℝ) frameCap from ⟨by linarith,hz.2⟩)
      linarith

theorem primary_D_remainder {q r : ℝ} {E : SignedPoint}
    (hEs : E.Sorted) (hEc : E.AvoidsCore) (hEcont : E.Contained q)
    (hq : q≤qCap) (hyE : E.y≤0) (hr : |r|≤frameCap) :
    ∃ l∈Icc (4/5 : ℝ) 2,
      baseline l+l*JD E r-StrongerEndpointScalars.charge*r+S0<2-StrongerEndpointScalars.epsilon := by
  by_cases hr0 : 0≤r
  · have hr' : r∈Icc 0 frameCap := ⟨hr0,(le_abs_self r).trans hr⟩
    obtain ⟨l,hl,hstress⟩ := positive_remainder hEs (hEcont.trans hq) hr'
    have hJ : JD E r≤EPairMinimum.J E.a E.y r := by
      rw [← JH_positive hyE hr']
      exact JD_le_JH hyE r
    have hm := mul_le_mul_of_nonneg_left hJ (show 0≤l by linarith [hl.1])
    exact ⟨l,hl,by linarith⟩
  · have hz : -r∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs r).trans hr⟩
    by_cases hzsmall : -r≤6/25
    · have hJ : JD E r≤negativeGain (183/200) (-r) := by
        have h := JD_negative_bound hEs hEc hEcont hq hyE
          (by norm_num : (1/2:ℝ)≤183/200) hz
        rwa [neg_neg] at h
      have hm := mul_le_mul_of_nonneg_left hJ (by norm_num : (0:ℝ)≤7/6)
      refine ⟨7/6,by norm_num,?_⟩
      have hscalar := StrongerEndpointScalars.negative_short
        (show -r∈Icc 0 (6/25 : ℝ) from ⟨hz.1,hzsmall⟩)
      linarith
    · have hJ : JD E r≤negativeGain (4/5) (-r) := by
        have h := JD_negative_bound hEs hEc hEcont hq hyE
          (by norm_num : (1/2:ℝ)≤4/5) hz
        rwa [neg_neg] at h
      have hm := mul_le_mul_of_nonneg_left hJ (by norm_num : (0:ℝ)≤7/4)
      refine ⟨7/4,by norm_num,?_⟩
      have hscalar := StrongerEndpointScalars.negative_long
        (show -r∈Icc (6/25 : ℝ) frameCap from ⟨by linarith,hz.2⟩)
      linarith

theorem primary_pair {q u v : ℝ} {H D E : SignedPoint}
    (hHs : H.Sorted) (hDs : D.Sorted) (hEs : E.Sorted)
    (hHc : H.AvoidsCore) (hDc : D.AvoidsCore) (hEc : E.AvoidsCore)
    (hHcont : H.Contained q) (hDcont : D.Contained q) (hEcont : E.Contained q)
    (hq : q≤qCap) (hyH : 0≤H.y) (hyD : D.y≤0)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap) (hsum : |u+v|≤frameCap)
    (hDE : quarterFeasible D E u 3) (hEH : quarterFeasible E H v 1) :
    objective H D u v+S0<2-StrongerEndpointScalars.epsilon := by
  have hcH : H.circle≤qCap := hHcont.trans hq
  have hcD : D.circle≤qCap := hDcont.trans hq
  by_cases he0 : 0≤u+v
  · have he : u+v∈Icc 0 frameCap := ⟨he0,(le_abs_self (u+v)).trans hsum⟩
    have hprim := EPairMinimum.actual_positive_total hEs hEc hEcont hq hu hv he hDE hEH
    obtain ⟨l,hl,hscalar⟩ := positive_remainder hEs (hEcont.trans hq) he
    have hraw := primary_sum (u := u) (v := v) hyH hyD hcH hcD
      (show 0≤l by linarith [hl.1]) hprim
    linarith
  · have he : -(u+v)∈Icc 0 frameCap :=
      ⟨by linarith,(neg_le_abs (u+v)).trans hsum⟩
    have hpair := ENegativePairMinimum.actual_negative_total hHs hDs hEs hHc hDc hEc
      hHcont hDcont hEcont hq hu hv he (by ring : u+v= -(-(u+v))) hDE hEH
    by_cases hesmall : -(u+v)≤6/25
    · have hprim : 2-negativeGain (183/200) (-(u+v))≤H.a+D.a := by
        have hp := hpair.1
        simp only [negativeGain,K]
        simp only [ENegativePairMinimum.K] at hp
        linarith
      have hraw := primary_sum (u := u) (v := v) hyH hyD hcH hcD
        (by norm_num : (0:ℝ)≤7/6) hprim
      have hscalar := StrongerEndpointScalars.negative_short
        (show -(u+v)∈Icc 0 (6/25 : ℝ) from ⟨he.1,hesmall⟩)
      linarith
    · have hlong : 6/25≤-(u+v) := by linarith
      have hprim : 2-negativeGain (4/5) (-(u+v))≤H.a+D.a := by
        have hp := hpair.2 hlong
        simp only [negativeGain,K]
        simp only [ENegativePairMinimum.K] at hp
        linarith
      have hraw := primary_sum (u := u) (v := v) hyH hyD hcH hcD
        (by norm_num : (0:ℝ)≤7/4) hprim
      have hscalar := StrongerEndpointScalars.negative_long
        (show -(u+v)∈Icc (6/25 : ℝ) frameCap from ⟨hlong,he.2⟩)
      linarith

/-- All four actual weak owner pairs at their unchanged source points. -/
theorem actual_mixed {q u v : ℝ} {H D E : SignedPoint}
    (hHs : H.Sorted) (hDs : D.Sorted) (hEs : E.Sorted)
    (hHc : H.AvoidsCore) (hDc : D.AvoidsCore) (hEc : E.AvoidsCore)
    (hHcont : H.Contained q) (hDcont : D.Contained q) (hEcont : E.Contained q)
    (hq : q≤qCap) (hyH : 0≤H.y) (hyD : D.y≤0) (hyE : E.y≤0)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap) (hsum : |u+v|≤frameCap)
    (hDE : quarterFeasible D E u 2 ∨ quarterFeasible D E u 3)
    (hEH : quarterFeasible E H v 0 ∨ quarterFeasible E H v 1) :
    objective H D u v+S0<2-StrongerEndpointScalars.epsilon := by
  have hcH : H.circle≤qCap := hHcont.trans hq
  have hcD : D.circle≤qCap := hDcont.trans hq
  rcases hDE with hDE | hDE
  · rcases hEH with hEH | hEH
    · have hraw := two_rotated hyH hyD hcH hcD
        (by norm_num : (0:ℝ)≤7/6) hu hv hDE hEH
      have hdu := defect_upper (l := 7/6) (by norm_num) hu
      have hdv := defect_upper (l := 7/6) (by norm_num) hv
      linarith [rotated_baseline,abs_nonneg u,abs_nonneg v]
    · obtain ⟨l,hl,hscalar⟩ := primary_H_remainder hEs hEc hEcont hHs hHc hHcont
        hq hyE hv hEH
      have hraw := rotated_D_primary_H hyH hyD hcH hcD
        (show 0≤l by linarith [hl.1]) hu hv hDE hEH
      have hd := defect_upper hl hu
      linarith [abs_nonneg u]
  · rcases hEH with hEH | hEH
    · obtain ⟨l,hl,hscalar⟩ := primary_D_remainder hEs hEc hEcont hq hyE hu
      have hraw := primary_D_rotated_H hyH hyD hcH hcD
        (show 0≤l by linarith [hl.1]) hu hv hDE hEH
      have hd := defect_upper hl hv
      linarith [abs_nonneg v]
    · exact primary_pair hHs hDs hEs hHc hDc hEc hHcont hDcont hEcont
        hq hyH hyD hu hv hsum hDE hEH

end StrongerEndpointBudget

namespace SignedCycle
open Candidate EndpointBudgetScalars StrongerEndpointScalars

/-- Strict H/D/E budget for a necessary cycle with its original physical
DE and EH witnesses.  In particular, this does not require hard GA/BT. -/
theorem stronger_endpoint_budget {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hyE : (C.point E).y≤0) (w : C.Witnesses) :
    (C.point H).y-(C.point D).y-StrongerEndpointScalars.charge*(C.theta H-C.theta D)+S0<2-StrongerEndpointScalars.epsilon := by
  have hownerD : w.owner D=2 ∨ w.owner D=3 := by
    simpa [normalOwners,D] using w.allowed D
  have hownerE : w.owner E=0 ∨ w.owner E=1 := by
    simpa [normalOwners,E] using w.allowed E
  have hde : quarterFeasible (C.point D) (C.point E) (C.theta E-C.theta D) 2 ∨
      quarterFeasible (C.point D) (C.point E) (C.theta E-C.theta D) 3 := by
    have hw := w.feasible D
    rcases hownerD with ho | ho
    · left
      rw [ho] at hw
      simpa [Feasible,slack,edge,delta,next,word,D,E,quarterFeasible] using hw
    · right
      rw [ho] at hw
      simpa [Feasible,slack,edge,delta,next,word,D,E,quarterFeasible] using hw
  have heh : quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 0 ∨
      quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 1 := by
    have hw := w.feasible E
    rcases hownerE with ho | ho
    · left
      rw [ho] at hw
      simpa [Feasible,slack,edge,delta,next,word,E,H,quarterFeasible] using hw
    · right
      rw [ho] at hw
      simpa [Feasible,slack,edge,delta,next,word,E,H,quarterFeasible] using hw
  have hsumeq : (C.theta E-C.theta D)+(C.theta H-C.theta E)=C.theta H-C.theta D := by ring
  have hsum : |(C.theta E-C.theta D)+(C.theta H-C.theta E)|≤frameCap := by
    rw [hsumeq]; exact hC.spread H D
  have h := StrongerEndpointBudget.actual_mixed (hC.sorted H) (hC.sorted D) (hC.sorted E)
    (hC.core H) (hC.core D) (hC.core E) (hC.contained H) (hC.contained D) (hC.contained E)
    hq hn.H_nonneg hn.D_nonpos hyE (hC.spread E D) (hC.spread H E) hsum hde heh
  unfold StrongerEndpointStress.objective at h
  rw [hsumeq] at h
  exact h

theorem HardInput.stronger_endpoint_budget {q : ℝ} (I : HardInput q) (hq : q≤qCap) :
    (I.cycle.point H).y-(I.cycle.point D).y-
      (41/40)*(I.cycle.theta H-I.cycle.theta D)+
      (2*Real.sqrt (qCap-1)-3)<2-(27/160000 : ℝ) := by
  have h := SignedCycle.stronger_endpoint_budget hq I.necessary I.anchors_normal
    I.E_nonpos I.witnesses
  simp only [StrongerEndpointScalars.charge,S0,StrongerEndpointScalars.epsilon] at h
  exact h

end SignedCycle
end SquaresInCircles.Eight
