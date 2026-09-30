import SquaresInCircles.Six.Analytic.SmallDiagonalStressTools

/-!
# One frozen-center stress for negative OWN W and small D

Use the fixed multipliers 3/2 on C--W, 2 on C--D and 1 on W--D.
The last edge uses D-secondary. Keeping the local centers fixed makes the
stress separately concave on the entire rectangle 0<=v<=2/3, 0<=d<=1/2.
The curvature estimate is proved before any support maximization. Consequently
only the four original rectangle corners need scalar support estimates.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def ownSmallDStress (aw bw ad bd cx cy v d : ℝ) : ℝ :=
  frozenTrig (9/4-(3/2)*aw-2*ad-bd)
    ((3/2)*(1/2-cx)) ((3/2)*(1/2+cy)) (2*(1/2-cx)) (2*(1/2-cy))
    (1/2+bw) (1/2-aw) v d

def ownSmallDThreshold (v d : ℝ) : ℝ :=
  9/4+(3/4)*(Real.cos v+Real.sin v)+(Real.cos d+Real.sin d)+
    (Real.cos (v+d)+Real.sin (v+d))/2

def ownSmallDCentralX (v d : ℝ) : ℝ := (3/2)*Real.cos v+2*Real.cos d
def ownSmallDCentralY (v d : ℝ) : ℝ := 2*Real.sin d-(3/2)*Real.sin v

lemma ownSmallD_work (aw bw ad bd cx cy v d : ℝ) :
    ownSmallDStress aw bw ad bd cx cy v d = ownSmallDThreshold v d-
      (ownSmallDCentralX v d*cx+ownSmallDCentralY v d*cy)-
      ((3/2+Real.sin (v+d))*aw-Real.cos (v+d)*bw)-(2*ad+bd) := by
  dsimp [ownSmallDStress,frozenTrig,ownSmallDThreshold,ownSmallDCentralX,ownSmallDCentralY]
  ring

lemma ownSmallD_concave_v {aw bw ad bd cx cy d : ℝ}
    (hW : ContainedChart aw |bw|) (hb : |bw|≤1/2)
    (hC : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) (hd : 0≤d ∧ d≤1/2) :
    ConcaveOn ℝ (Set.Icc 0 (2/3)) (fun v => ownSmallDStress aw bw ad bd cx cy v d) := by
  apply frozenTrig_concave_v_of_curvature
  intro v hv
  have hA : 387/1000≤1/2-cx := by dsimp [c0] at hC; linarith [hC.1.2,rho0_upper]
  have hB : 387/1000≤1/2+cy := by linarith [hC.2.1]
  have h := frozen_secondary_curvature (k := (3:ℝ)/2) (by norm_num) hA hB
    hW.half_le hW.a_le_rho0 (abs_le.mp hb).1 hv
    (show 0≤v+d ∧ v+d≤7/6 by constructor <;> linarith [hv.1,hv.2,hd.1,hd.2])
  nlinarith only [h]

lemma ownSmallD_concave_d {aw bw ad bd cx cy v : ℝ}
    (hW : ContainedChart aw |bw|) (hb : |bw|≤1/2)
    (hC : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) (hv : 0≤v ∧ v≤2/3) :
    ConcaveOn ℝ (Set.Icc 0 (1/2)) (fun d => ownSmallDStress aw bw ad bd cx cy v d) := by
  apply frozenTrig_concave_d_of_curvature
  intro d hd
  have hA : 387/1000≤1/2-cx := by dsimp [c0] at hC; linarith [hC.1.2,rho0_upper]
  have hB : 387/1000≤1/2-cy := by dsimp [c0] at hC; linarith [hC.2.2,rho0_upper]
  have h := frozen_secondary_curvature (k := (2:ℝ)) (by norm_num) hA hB
    hW.half_le hW.a_le_rho0 (abs_le.mp hb).1
    (show 0≤d ∧ d≤2/3 by constructor <;> linarith [hd.1,hd.2])
    (show 0≤v+d ∧ v+d≤7/6 by constructor <;> linarith [hv.1,hv.2,hd.1,hd.2])
  nlinarith only [h]

lemma ownSmallDCentralX_nonneg {v d : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2) : 0≤ownSmallDCentralX v d := by
  have hcv := (small_secondary_trig ⟨hv.1,by linarith [hv.2]⟩).1
  have hcd := (small_secondary_trig ⟨hd.1,by linarith [hd.2]⟩).1
  dsimp [ownSmallDCentralX]
  linarith

def ownSmallDVertexMinorant (v d L : ℝ) : ℝ :=
  ownSmallDThreshold v d-(5641/50000)*(ownSmallDCentralX v d+max (ownSmallDCentralY v d) 0)-
    ((33771/20000)*L-(3/2+Real.sin (v+d)+Real.cos (v+d))/2)-
    ((33771/20000)*(223607/100000)-3/2)

def ownSmallDCapMinorant (v d : ℝ) : ℝ :=
  ownSmallDThreshold v d-(5641/50000)*(ownSmallDCentralX v d+max (ownSmallDCentralY v d) 0)-
    (55641/50000)*(3/2+Real.sin (v+d))-
    ((33771/20000)*(223607/100000)-3/2)

lemma ownSmallD_above_vertex {aw bw ad bd cx cy v d L : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hC : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2)
    (hL : 0≤L) (hnorm : (3/2+Real.sin (v+d))^2+(Real.cos (v+d))^2≤L^2) :
    ownSmallDVertexMinorant v d L≤ownSmallDStress aw bw ad bd cx cy v d := by
  have ht := small_secondary_trig
    (show 0≤v+d ∧ v+d≤7/6 by constructor <;> linarith [hv.1,hv.2,hd.1,hd.2])
  have hWbox : (aw+1/2)^2+(|-bw|+1/2)^2≤Q0 := by simpa only [abs_neg] using hW.containment
  have hWU := circle_vertex_from_root_bound (U := 3/2+Real.sin (v+d))
    (V := Real.cos (v+d)) hWbox ht.1 hL hnorm
  have hDU := circle_vertex_from_root_bound (U := (2:ℝ)) (V := (1:ℝ))
    (L := (223607:ℝ)/100000) hD.containment (by norm_num) (by norm_num) (by norm_num)
  have hCU := central_projection_bound hC (ownSmallDCentralX_nonneg hv hd)
    (Y := ownSmallDCentralY v d)
  rw [ownSmallD_work]
  dsimp [ownSmallDVertexMinorant]
  nlinarith only [hWU,hDU,hCU]

lemma ownSmallD_above_cap {aw bw ad bd cx cy v d : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hC : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2)
    (hslope : 2*(rho0+1/2)*Real.cos (v+d)≤3/2+Real.sin (v+d)) :
    ownSmallDCapMinorant v d≤ownSmallDStress aw bw ad bd cx cy v d := by
  have ht := small_secondary_trig
    (show 0≤v+d ∧ v+d≤7/6 by constructor <;> linarith [hv.1,hv.2,hd.1,hd.2])
  have hWbox : (aw+1/2)^2+(|-bw|+1/2)^2≤Q0 := by simpa only [abs_neg] using hW.containment
  have hWU := circle_primary_from_slope (U := 3/2+Real.sin (v+d))
    (V := Real.cos (v+d)) hWbox (by linarith [ht.2.1]) ht.1 hslope
  have hDU := circle_vertex_from_root_bound (U := (2:ℝ)) (V := (1:ℝ))
    (L := (223607:ℝ)/100000) hD.containment (by norm_num) (by norm_num) (by norm_num)
  have hCU := central_projection_bound hC (ownSmallDCentralX_nonneg hv hd)
    (Y := ownSmallDCentralY v d)
  rw [ownSmallD_work]
  dsimp [ownSmallDCapMinorant]
  nlinarith only [hWU,hDU,hCU]

end SquaresInCircles.Six.Analytic
