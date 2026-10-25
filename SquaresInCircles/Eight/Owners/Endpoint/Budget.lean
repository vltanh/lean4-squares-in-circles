module

public import SquaresInCircles.Eight.Owners.E.NegativePairMinimum
public import SquaresInCircles.Eight.Owners.Endpoint.MixedStress

/-!
# Eight squares: the strict H/D/E budget for every mixed owner

For the circles of H and D and the point E of a necessary cycle, each of the four pairs of an
owner of DE in `{2, 3}` and of EH in `{0, 1}` gives, from its weak inequalities, the budget
`H.y - D.y - charge (θ_H - θ_D) + S0 < 2 - epsilon` (`primary_pair`, `actual_mixed`,
`endpoint_budget`); no sign of G or T, frame order or radial kind enters.

For a hard input the reserve is `1/8000` (`HardInput.endpoint_budget`), which exceeds the error
`1/10000` of the argument for a small wrong intermediate sign.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace EndpointBudget
open EndpointRotationPenalty EndpointBudgetScalars EndpointECharge EndpointMixedStress

theorem rotated_baseline : baseline (7/6)+S0<2-epsilon := by
  have hN := fixed_norm_bounds.1
  have hS := radical_bounds.2.2.2
  dsimp [baseline,epsilon]
  linarith

theorem positive_remainder {E : SignedPoint} {r : ℝ}
    (hEs : E.Sorted) (hEc : E.circle≤qCap) (hr : r∈Icc 0 frameCap) :
    ∃ l∈Icc (4/5 : ℝ) 2,
      baseline l+l*EPairMinimum.J E.a E.y r-EndpointRotationPenalty.charge*r+S0<2-epsilon := by
  by_cases hrh : r≤1/2
  · have hshort : r∈Icc 0 (1/2 : ℝ) := ⟨hr.1,hrh⟩
    have hl := weight_bounds hshort
    have hJ := mul_le_mul_of_nonneg_left (positive_J_short hEs hEc hshort)
      (show 0≤weight r by linarith [hl.1])
    exact ⟨weight r,hl,by linarith [positive_short hshort]⟩
  · have hJ := mul_le_mul_of_nonneg_left (positive_J_long hEc hr)
      (by norm_num : (0:ℝ)≤4/5)
    exact ⟨4/5,by norm_num,by
      linarith [positive_long (show r∈Icc (1/2 : ℝ) frameCap from ⟨by linarith,hr.2⟩)]⟩

theorem primary_H_remainder {q r : ℝ} {E H : SignedPoint}
    (hEs : E.Sorted) (hEc : E.AvoidsCore) (hEcont : E.Contained q)
    (hHs : H.Sorted) (hHc : H.AvoidsCore) (hHcont : H.Contained q)
    (hq : q≤qCap) (hyE : E.y≤0) (hr : |r|≤frameCap)
    (hEH : quarterFeasible E H r 1) :
    ∃ l∈Icc (4/5 : ℝ) 2,
      baseline l+l*JH E r-EndpointRotationPenalty.charge*r+S0<2-epsilon := by
  by_cases hr0 : 0≤r
  · have hr' : r∈Icc 0 frameCap := ⟨hr0,(le_abs_self r).trans hr⟩
    obtain ⟨l,hl,hstress⟩ := positive_remainder hEs (hEcont.trans hq) hr'
    exact ⟨l,hl,by simpa only [JH_positive hyE hr'] using hstress⟩
  · have hz : -r∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs r).trans hr⟩
    have hEH' : quarterFeasible E H (-(-r)) 1 := by simpa only [neg_neg] using hEH
    obtain ⟨hb,hbstrong⟩ := negative_EH_tangent hEs hEc hEcont hHs hHc hHcont
      hq hyE hz hEH'
    by_cases hzsmall : -r≤6/25
    · have hJ : JH E r≤negativeGain (183/200) (-r) := by
        simpa only [neg_neg] using JH_negative_bound hEs hEc hEcont hq
          (show -E.y+1/2≤183/200 by linarith) hz
      have hm := mul_le_mul_of_nonneg_left hJ (by norm_num : (0:ℝ)≤7/6)
      refine ⟨7/6,by norm_num,?_⟩
      have hscalar := negative_short (show -r∈Icc 0 (6/25 : ℝ) from ⟨hz.1,hzsmall⟩)
      linarith
    · have hb' := hbstrong (show 3/25≤-r by linarith)
      have hJ : JH E r≤negativeGain (4/5) (-r) := by
        simpa only [neg_neg] using JH_negative_bound hEs hEc hEcont hq
          (show -E.y+1/2≤4/5 by linarith) hz
      have hm := mul_le_mul_of_nonneg_left hJ (by norm_num : (0:ℝ)≤7/4)
      refine ⟨7/4,by norm_num,?_⟩
      have hscalar := negative_long (show -r∈Icc (6/25 : ℝ) frameCap from ⟨by linarith,hz.2⟩)
      linarith

theorem primary_D_remainder {q r : ℝ} {E : SignedPoint}
    (hEs : E.Sorted) (hEc : E.AvoidsCore) (hEcont : E.Contained q)
    (hq : q≤qCap) (hyE : E.y≤0) (hr : |r|≤frameCap) :
    ∃ l∈Icc (4/5 : ℝ) 2,
      baseline l+l*JD E r-EndpointRotationPenalty.charge*r+S0<2-epsilon := by
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
        simpa only [neg_neg] using JD_negative_bound hEs hEc hEcont hq hyE
          (by norm_num : (1/2:ℝ)≤183/200) hz
      have hm := mul_le_mul_of_nonneg_left hJ (by norm_num : (0:ℝ)≤7/6)
      refine ⟨7/6,by norm_num,?_⟩
      have hscalar := negative_short (show -r∈Icc 0 (6/25 : ℝ) from ⟨hz.1,hzsmall⟩)
      linarith
    · have hJ : JD E r≤negativeGain (4/5) (-r) := by
        simpa only [neg_neg] using JD_negative_bound hEs hEc hEcont hq hyE
          (by norm_num : (1/2:ℝ)≤4/5) hz
      have hm := mul_le_mul_of_nonneg_left hJ (by norm_num : (0:ℝ)≤7/4)
      refine ⟨7/4,by norm_num,?_⟩
      have hscalar := negative_long (show -r∈Icc (6/25 : ℝ) frameCap from ⟨by linarith,hz.2⟩)
      linarith

theorem primary_pair {q u v : ℝ} {H D E : SignedPoint}
    (hHs : H.Sorted) (hDs : D.Sorted) (hEs : E.Sorted)
    (hHc : H.AvoidsCore) (hDc : D.AvoidsCore) (hEc : E.AvoidsCore)
    (hHcont : H.Contained q) (hDcont : D.Contained q) (hEcont : E.Contained q)
    (hq : q≤qCap) (hyH : 0≤H.y) (hyD : D.y≤0)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap) (hsum : |u+v|≤frameCap)
    (hDE : quarterFeasible D E u 3) (hEH : quarterFeasible E H v 1) :
    objective H D u v+S0<2-epsilon := by
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
        dsimp [negativeGain,K]
        dsimp [ENegativePairMinimum.K] at hp
        linarith
      have hraw := primary_sum (u := u) (v := v) hyH hyD hcH hcD
        (by norm_num : (0:ℝ)≤7/6) hprim
      have hscalar := negative_short
        (show -(u+v)∈Icc 0 (6/25 : ℝ) from ⟨he.1,hesmall⟩)
      linarith
    · have hlong : 6/25≤-(u+v) := by linarith
      have hprim : 2-negativeGain (4/5) (-(u+v))≤H.a+D.a := by
        have hp := hpair.2 hlong
        dsimp [negativeGain,K]
        dsimp [ENegativePairMinimum.K] at hp
        linarith
      have hraw := primary_sum (u := u) (v := v) hyH hyD hcH hcD
        (by norm_num : (0:ℝ)≤7/4) hprim
      have hscalar := negative_long (show -(u+v)∈Icc (6/25 : ℝ) frameCap from ⟨hlong,he.2⟩)
      linarith

/-- The budget for each of the four weak owner pairs of DE and EH, at the points H, D, E. -/
theorem actual_mixed {q u v : ℝ} {H D E : SignedPoint}
    (hHs : H.Sorted) (hDs : D.Sorted) (hEs : E.Sorted)
    (hHc : H.AvoidsCore) (hDc : D.AvoidsCore) (hEc : E.AvoidsCore)
    (hHcont : H.Contained q) (hDcont : D.Contained q) (hEcont : E.Contained q)
    (hq : q≤qCap) (hyH : 0≤H.y) (hyD : D.y≤0) (hyE : E.y≤0)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap) (hsum : |u+v|≤frameCap)
    (hDE : quarterFeasible D E u 2 ∨ quarterFeasible D E u 3)
    (hEH : quarterFeasible E H v 0 ∨ quarterFeasible E H v 1) :
    objective H D u v+S0<2-epsilon := by
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

end EndpointBudget

namespace SignedCycle
open Candidate EndpointRotationPenalty EndpointBudgetScalars

/-- The strict H/D/E budget of a necessary cycle with nonpositive E, from its DE and EH witnesses;
GA and BT need not be hard. -/
theorem endpoint_budget {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hyE : (C.point E).y≤0) (w : C.Witnesses) :
    (C.point H).y-(C.point D).y-EndpointRotationPenalty.charge*(C.theta H-C.theta D)+S0<2-epsilon := by
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
      unfold SignedCycle.Feasible SignedCycle.slack SignedCycle.edge at hw
      rw [ite_eq_right (by decide : ¬Candidate.word D=0)] at hw
      exact sub_nonneg.mp hw
    · right
      rw [ho] at hw
      unfold SignedCycle.Feasible SignedCycle.slack SignedCycle.edge at hw
      rw [ite_eq_right (by decide : ¬Candidate.word D=0)] at hw
      exact sub_nonneg.mp hw
  have heh : quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 0 ∨
      quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 1 := by
    have hw := w.feasible E
    rcases hownerE with ho | ho
    · left
      rw [ho] at hw
      unfold SignedCycle.Feasible SignedCycle.slack SignedCycle.edge at hw
      rw [ite_eq_right (by decide : ¬Candidate.word E=0)] at hw
      exact sub_nonneg.mp hw
    · right
      rw [ho] at hw
      unfold SignedCycle.Feasible SignedCycle.slack SignedCycle.edge at hw
      rw [ite_eq_right (by decide : ¬Candidate.word E=0)] at hw
      exact sub_nonneg.mp hw
  have hsum : |(C.theta E-C.theta D)+(C.theta H-C.theta E)|≤frameCap := by
    convert hC.spread H D using 1 <;> congr 1 <;> ring
  have h := EndpointBudget.actual_mixed (hC.sorted H) (hC.sorted D) (hC.sorted E)
    (hC.core H) (hC.core D) (hC.core E) (hC.contained H) (hC.contained D) (hC.contained E)
    hq hn.H_nonneg hn.D_nonpos hyE (hC.spread E D) (hC.spread H E) hsum hde heh
  simpa only [EndpointMixedStress.objective,show (C.theta E-C.theta D)+
    (C.theta H-C.theta E)=C.theta H-C.theta D by ring] using h

theorem HardInput.endpoint_budget {q : ℝ} (I : HardInput q) (hq : q≤qCap) :
    (I.cycle.point H).y-(I.cycle.point D).y-
      (50/49)*(I.cycle.theta H-I.cycle.theta D)+
      (2*Real.sqrt (qCap-1)-3)<2-(1/8000 : ℝ) := by
  simpa only [EndpointRotationPenalty.charge,S0,epsilon] using
    SignedCycle.endpoint_budget hq I.necessary I.anchors_normal
    I.E_nonpos I.witnesses

end SignedCycle
end SquaresInCircles.Eight
