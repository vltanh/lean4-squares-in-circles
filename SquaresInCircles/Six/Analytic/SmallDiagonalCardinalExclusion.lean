import SquaresInCircles.Six.Analytic.SmallDiagonalCardinalMinorant
import SquaresInCircles.Six.Analytic.OwnSmallDiagonalExclusion

/-!
# The unconditional analytic d>1/2 reduction

For cardinal W use weights (1,3/2,1). The exact W-force norm loses its v
dependence, yielding the separately concave minorant already proved on the
whole rectangle. For OWN W use the frozen-center stress from the preceding
module. W-secondary and nonnegative-W cases have independent geometric
exclusions. Together they force d>1/2 for every actual normalized packing.

No D/S source choice, pair Domain, fixed stress table or candidate-tail
certificate is imported to obtain this angle reduction.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private lemma circle_vertex_actual {a b U V : ℝ}
    (hbox : (a+1/2)^2+(|b|+1/2)^2≤Q0) (hV : 0≤V) :
    U*a+V*b≤R0*Real.sqrt (U^2+V^2)-(U+V)/2 := by
  have hp : normSq (a+1/2,|b|+1/2)≤R0^2 := by simpa only [normSq,R0_sq] using hbox
  have hd := Stress.dot_le_radius (v := (U,V)) R0_nonneg hp
  have hb := mul_le_mul_of_nonneg_left (le_abs_self b) hV
  dsimp [dot,Stress.vectorLength,normSq] at hd
  nlinarith only [hd,hb]

def cardinalSmallDStress (aw bw ad bd cx cy v d : ℝ) : ℝ :=
  (1/2-cx+(1/2-aw)*Real.cos v+(1/2-bw)*Real.sin v)+
    (3/2)*(1/2-ad+(1/2-cx)*Real.cos d+(1/2-cy)*Real.sin d)+
    (1/2+(1/2+bw)*Real.cos (v+d)+(1/2-aw)*Real.sin (v+d)-bd)

lemma cardinalSmallD_force_norm (v d : ℝ) :
    (Real.cos v+Real.sin (v+d))^2+(Real.cos (v+d)-Real.sin v)^2=2+2*Real.sin d := by
  have hsin : Real.sin (v+d)*Real.cos v-Real.cos (v+d)*Real.sin v=Real.sin d := by
    rw [← Real.sin_sub,show v+d-v=d by ring]
  nlinarith only [hsin,Real.sin_sq_add_cos_sq v,Real.sin_sq_add_cos_sq (v+d)]

lemma cardinalSmallD_force_transverse_nonneg {v d : ℝ}
    (hv : 0≤v ∧ v≤2/5) (hd : 0≤d ∧ d≤1/2) :
    0≤Real.cos (v+d)-Real.sin v := by
  have hq0 : 0≤v+d := by linarith [hv.1,hd.1]
  have hq1 : v+d≤9/10 := by linarith [hv.2,hd.2]
  have hsq := mul_nonneg (sub_nonneg.mpr hq1) (show 0≤9/10+(v+d) by linarith)
  have hc := Real.one_sub_sq_div_two_le_cos (x := v+d)
  have hs := Real.sin_le hv.1
  nlinarith [hv.2]

lemma cardinalSmallD_above_minorant {aw bw ad bd cx cy v d : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hC : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hv : 0≤v ∧ v≤2/5) (hd : 0≤d ∧ d≤1/2) :
    cardinalSmallDMinorant v d≤cardinalSmallDStress aw bw ad bd cx cy v d := by
  have hWbox : (aw+1/2)^2+(|-bw|+1/2)^2≤Q0 := by simpa only [abs_neg] using hW.containment
  have hWsupport := circle_vertex_actual
    (U := Real.cos v+Real.sin (v+d)) (V := Real.cos (v+d)-Real.sin v)
    hWbox (cardinalSmallD_force_transverse_nonneg hv hd)
  rw [cardinalSmallD_force_norm] at hWsupport
  have hDsupport := circle_vertex_actual (U := (3:ℝ)/2) (V := (1:ℝ)) hD.containment (by norm_num)
  have hnorm : (3/2:ℝ)^2+(1:ℝ)^2=13/4 := by norm_num
  rw [hnorm] at hDsupport
  have ht := small_secondary_trig ⟨hd.1,by linarith [hd.2]⟩
  have hcx := mul_le_mul_of_nonneg_left hC.1.2
    (show 0≤1+(3/2)*Real.cos d by linarith [ht.1])
  have hcy := mul_le_mul_of_nonneg_left hC.2.2
    (show 0≤(3/2)*Real.sin d by linarith [ht.2.1])
  dsimp [cardinalSmallDMinorant,cardinalSmallDStress]
  nlinarith only [hWsupport,hDsupport,hcx,hcy]

lemma cardinalSmallD_nonpositive {aw bw ad bd cx cy v d : ℝ}
    (hv : 0≤v ∧ v≤2/5) (hd : 0≤d ∧ d≤1/2)
    (hCW : 0≤centralMargin .west (Real.pi-v) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (normalY (orientedSquare (Real.pi+d) ad bd))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center)) :
    cardinalSmallDStress aw bw ad bd cx cy v d≤0 := by
  have htv := small_secondary_trig ⟨hv.1,by linarith [hv.2]⟩
  have htd := small_secondary_trig ⟨hd.1,by linarith [hd.2]⟩
  have htq := small_secondary_trig
    (show 0≤v+d ∧ v+d≤7/6 by constructor <;> linarith [hv.1,hv.2,hd.1,hd.2])
  have hWgap : 1/2-cx+(1/2-aw)*Real.cos v+(1/2-bw)*Real.sin v≤0 := by
    simp only [centralMargin,centerX,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
      abs_neg,abs_of_nonneg htv.1,abs_of_nonneg htv.2.1] at hCW
    nlinarith only [hCW]
  have hDgap : 1/2-ad+(1/2-cx)*Real.cos d+(1/2-cy)*Real.sin d≤0 := by
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,Real.sin_pi_add,
      abs_neg,abs_of_nonneg htd.1,abs_of_nonneg htd.2.1] at hCD
    nlinarith only [hCD]
  have hq : (Real.pi+d)-(Real.pi-v)=v+d := by ring
  change Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
      (orientedSquare (Real.pi+d) ad bd)≤
    frameY (orientedSquare (Real.pi+d) ad bd)
      (sub (orientedSquare (Real.pi+d) ad bd).center
        (orientedSquare (Real.pi-v) aw bw).center) at hWD
  rw [pair_frameY_right,oriented_pair_threshold,hq,angularWidth,
    abs_of_nonneg htq.1,abs_of_nonneg htq.2.1] at hWD
  have hgap : 1/2+(1/2+bw)*Real.cos (v+d)+(1/2-aw)*Real.sin (v+d)-bd≤0 := by
    nlinarith only [hWD]
  dsimp [cardinalSmallDStress]
  nlinarith only [hWgap,hDgap,hgap]

/-- The complete cardinal negative-W rectangle is excluded analytically. -/
theorem cardinal_small_diagonal_Dsecondary_impossible {aw bw ad bd cx cy v d : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hC : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hv : 0≤v ∧ v≤2/5) (hd : 0≤d ∧ d≤1/2)
    (hCW : 0≤centralMargin .west (Real.pi-v) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (normalY (orientedSquare (Real.pi+d) ad bd))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center)) : False := by
  have hp := (cardinalSmallD_positive hv hd).trans_le (cardinalSmallD_above_minorant hW hD hC hv hd)
  have hn := cardinalSmallD_nonpositive hv hd hCW hCD hWD
  linarith

/-- The former d-tail reduction, now independent of all fixed-row certificates
and of the still-unproved final secondary-source classification. -/
theorem normalized_diagonal_gt_half {R : ℝ} (P : NormalizedPacking R) : 1/2<P.diagonalAngle := by
  cases hbit : P.ownBits 2
  · by_cases hw : 0≤P.helperAngle 2
    · exact nonnegative_W_forces_large_diagonal P hw
    · by_contra! hdsmall
      have hd : 0≤P.diagonalAngle ∧ P.diagonalAngle≤1/2 := ⟨P.diagonal_angle_range.1.le,hdsmall⟩
      have hangle := abs_lt.mp (P.cardinal_angle 2 hbit)
      have hv : 0≤-P.helperAngle 2 ∧ -P.helperAngle 2≤2/5 := by
        constructor <;> linarith [hangle.1]
      obtain ⟨k,hsep,hk⟩ := DW_secondary_exists P
      rcases hk with rfl | rfl
      · linarith [W_secondary_forces_large_diagonal P hsep]
      · have hwphase : P.phase 2=Real.pi-(-P.helperAngle 2) := by
          have hh : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
          linarith
        have hdphase : P.phase 3=Real.pi+P.diagonalAngle := by
          dsimp [NormalizedPacking.diagonalAngle]
          ring
        apply cardinal_small_diagonal_Dsecondary_impossible (P.contained 2) (P.contained 3) P.box hv hd
        · simpa only [hwphase] using P.cardinal_separator 2 hbit
        · simpa only [hdphase] using P.own_separator 3 P.diagonal_own
        · change Seven.SAT.threshold (P.square 2) (P.square 3)≤
            dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center) at hsep
          simpa only [P.square_def,hwphase,hdphase] using hsep
  · exact ownW_forces_large_diagonal P hbit

end SquaresInCircles.Six.Analytic
