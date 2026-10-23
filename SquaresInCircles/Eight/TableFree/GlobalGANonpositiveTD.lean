module

public import SquaresInCircles.Eight.TableFree.GlobalGASecondaryExclusion

/-!
# The actual nonpositive-TD2 extension of the four-circle obstruction

Uncompiled source.  TD is set to zero only in an algebraic reference
expression.  The actual TD2 inequality is retained, and its original T
point supplies the compensating gain.  No aligned TD0 witness or moved
cycle is introduced.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
open Candidate SignedStress

def tdOwners (hg : Fin 4) : Vertex → Fin 4 := ![hg,2,0,2,2,2,0]

def actualTDStress (hg : Fin 4) (C : SignedCycle) : ℝ :=
  demand C fourCircleWeights-
    ∑ i,work (force C (tdOwners hg) fourCircleWeights i) (C.point i)

def tdIncrement (z : ℝ) (P : SignedPoint) : ℝ :=
  2*(edgeWidth z-1)-2*(P.a*Real.sin z+P.y*(Real.cos z-1))+charge*z

theorem nonpositive_td_gain {z : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hcore : P.AvoidsCore)
    (hz : z≤0) (hsmall : |z|≤frameCap) : 0≤tdIncrement z P := by
  let s := -z
  have hsint : s∈Icc 0 frameCap :=
    ⟨neg_nonneg.mpr hz,(neg_le_abs z).trans hsmall⟩
  have hzs : z = -s := by dsimp [s]; ring
  obtain ⟨hc,hc1,hs0,hs1,hsc⟩ := transport_trig hsint
  have hphi : 0≤Real.sin s+Real.cos s-1 := by
    have h := one_le_abs_cos_add_abs_sin s
    simpa [abs_of_nonneg hs0,abs_of_pos hc,add_comm] using sub_nonneg.mpr h
  have hhalf := SignedPoint.primary_gt_half hs hcore
  have hy := (abs_le.mp hs.2).1
  have hycos := mul_le_mul_of_nonpos_right hy
    (show Real.cos s-1≤0 by linarith)
  have hprimary := mul_nonneg (show 0≤P.a-1/2 by linarith) hphi
  have hsin := Real.sin_ge_sub_cube hsint.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=s)
  have hs2 : s^2≤(7/10)*s := by
    have := mul_le_mul_of_nonneg_right hsint.2 hsint.1
    norm_num [frameCap] at this
    nlinarith
  have hs2' : s^2≤(7/10:ℝ)^2 :=
    pow_le_pow_left₀ hsint.1 (by simpa [frameCap] using hsint.2) 2
  have hs3 := mul_le_mul_of_nonneg_right hs2' hsint.1
  have hcharge : charge*s≤2*(Real.sin s+Real.cos s-1) := by
    dsimp [charge]
    nlinarith [hsint.1]
  rw [tdIncrement,hzs,edgeWidth_negative_formula hsint]
  simp only [Real.sin_neg,Real.cos_neg]
  nlinarith

theorem td_stress_nonpos {C : SignedCycle} {hg : Fin 4}
    (hHG : C.Feasible H hg) (hGA : C.Feasible G 2)
    (hAB : C.Feasible A 0) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) :
    actualTDStress hg C≤0 := by
  have hf (i : Vertex) : C.Feasible i (tdOwners hg i) := by
    fin_cases i
    · simpa [tdOwners,H] using hHG
    · simpa [tdOwners,G] using hGA
    · simpa [tdOwners,A] using hAB
    · simpa [tdOwners,B] using hBT
    · simpa [tdOwners,T] using hTD
    · simpa [tdOwners,D] using hDE
    · simpa [tdOwners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation fourCircleWeights_nonneg hf)

theorem zero_td_stress_decomposition (C : SignedCycle) :
    actualTDStress 0 C=baseStress+
      oneIncrement k 1 (delta C.theta E) (C.point H)+
      pairIncrement k l (delta C.theta H) (delta C.theta G) (C.point G).reflect+
      pairIncrement l 2 (delta C.theta A) (delta C.theta B) (C.point B).reflect+
      dIncrement 0 (delta C.theta D) (C.point D).reflect+
      tdIncrement (delta C.theta T) (C.point T) := by
  simp [actualTDStress,demand,force,source,target,work,add,scale,
    previous,tdOwners,fourCircleWeights,Fin.sum_univ_succ,
    word,delta,next,H,G,A,B,T,D,E,baseStress,oneIncrement,pairIncrement,
    pairF,pairG,dIncrement,dF,dG,tdIncrement,edgeWidth,pairWidth,
    SignedPoint.reflect,k,l,charge]
  ring

theorem two_td_stress_decomposition (C : SignedCycle) :
    actualTDStress 2 C=baseStress+
      pairIncrement k 1 (delta C.theta H) (delta C.theta E) (C.point H)+
      oneIncrement k l (delta C.theta G) (C.point G).reflect+
      pairIncrement l 2 (delta C.theta A) (delta C.theta B) (C.point B).reflect+
      dIncrement 0 (delta C.theta D) (C.point D).reflect+
      tdIncrement (delta C.theta T) (C.point T) := by
  simp [actualTDStress,demand,force,source,target,work,add,scale,
    previous,tdOwners,fourCircleWeights,Fin.sum_univ_succ,
    word,delta,next,H,G,A,B,T,D,E,baseStress,oneIncrement,pairIncrement,
    pairF,pairG,dIncrement,dF,dG,tdIncrement,edgeWidth,pairWidth,
    SignedPoint.reflect,k,l,charge]
  ring

theorem actual_nonpositive_TD_false {q : ℝ} {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G 2) (hAB : C.Feasible A 0) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D 2) (hEH : C.Feasible E 0)
    (hz : delta C.theta T≤0) : False := by
  have hn : negativeVariation C.theta≤frameCap := by
    rw [← variations_equal]
    exact hvar
  have herror (i : Vertex) := original_error_bound hvar hn i
  have hbb := original_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B])
  have hB := actual_B_pair (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  have hD := actual_dIncrement_nonneg (P:=(C.point D).reflect)
    (z:=0) (d:=delta C.theta D)
    (by simpa using hs D)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq (by norm_num [frameCap]) (herror D)
    (by simpa using herror D)
  have hT := nonpositive_td_gain (hs T) hcoreT hz (herror T)
  rcases hHG with hHG | hHG
  · have hupper := td_stress_nonpos hHG hGA hAB hBT hTD hDE hEH
    have hH := actual_H_one (x:=delta C.theta E) hHy (hc H) hq (herror E)
    have hgb := original_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G])
    have hG := actual_G_pair (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq hgb.1 hgb.2
    rw [zero_td_stress_decomposition] at hupper
    linarith [baseStress_reserve]
  · have hupper := td_stress_nonpos hHG hGA hAB hBT hTD hDE hEH
    have hhb := original_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E])
    have hH := actual_H_pair hHy (hc H) hq hhb.1 hhb.2
    have hG := actual_G_one (P:=(C.point G).reflect) (x:=delta C.theta G)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq (herror G)
    rw [two_td_stress_decomposition] at hupper
    linarith [baseStress_reserve]

/-- In the full secondary A/E sector, the original TD2 error must be
strictly positive.  The conclusion includes a weak zero-error tie. -/
theorem actual_TD2_positive {q : ℝ} {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G 2) (hAB : C.Feasible A 0) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) :
    0<delta C.theta T := by
  by_contra! h
  exact actual_nonpositive_TD_false hs hc hcoreT hq hHy hGy hBy hDy hvar
    hHG hGA hAB hBT hTD hDE hEH h

end SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
