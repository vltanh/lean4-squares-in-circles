import SquaresInCircles.Six.Analytic.LowDWestSource.Scalar
import SquaresInCircles.Six.Stress.Reverse

/-!
# W and D separated along the secondary axis of D

If W and D are separated along the secondary axis of D, at the phase `π + d`,
then `d > 3/5`. When W is separated from C along the west side of C, its phase
is within `2/5` of `π`, and the phase gap of more than one radian between W and
D gives this at once. When W, at the phase `π - v`, is separated from C along
its primary axis and `d ≤ 3/5`, the gap and the windows put `(v, d)` in the
quadrilateral `1/2 ≤ d ≤ 3/5`, `1 - d ≤ v ≤ 2/3`. There the weights `39/100`
and `43/100` on the separations of C from W and D along their primary axes and
`18/100` on that of W and D give forces whose works are at most the support of
the box `[0, c0]²` for C, for either sign of the second component of its force,
the cap support of W and the vertex support of D; and the threshold sum
exceeds these bounds by the minorant of `LowDWestSource.Scalar`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.LowDWestSource
open Normalization

def forceC (v d : ℝ) : Point :=
  ((39/100)*Real.cos v+(43/100)*Real.cos d,
   -(39/100)*Real.sin v+(43/100)*Real.sin d)
def forceW (v d : ℝ) : Point :=
  (-(39/100)*Real.cos v-(18/100)*Real.sin d,
   (39/100)*Real.sin v+(18/100)*Real.cos d)
def forceD (d : ℝ) : Point :=
  (-(43/100)*Real.cos d+(18/100)*Real.sin d,
   -(43/100)*Real.sin d-(18/100)*Real.cos d)

def system (v d : ℝ) : Stress.System 3 3 where
  source := ![0,0,1]
  target := ![1,2,2]
  normal := ![(-Real.cos v,Real.sin v),(-Real.cos d,-Real.sin d),
    (Real.sin d,-Real.cos d)]
  weight := ![39/100,43/100,18/100]
  threshold := ![1/2+angularWidth v,1/2+angularWidth d,1/2+angularWidth (v+d)]

def upperValues (b : Bool) (v d : ℝ) : Fin 3 → ℝ :=
  ![c0*((forceC v d).1+(if b then (forceC v d).2 else 0)),
    rho0*(39/100+(18/100)*Real.sin (v+d)),
    R0*Real.sqrt (2173/10000)-61/200]

def raw (b : Bool) (v d : ℝ) : ℝ :=
  (39/100)*(1/2-rho0)+61/100-R0*Real.sqrt (2173/10000)+
    (39/100)*(1/2-c0)*Real.cos v+
    (39/100)*(if b then 1/2+c0 else 1/2)*Real.sin v+
    (43/100)*(1/2-c0)*Real.cos d+
    (43/100)*(if b then 1/2-c0 else 1/2)*Real.sin d+
    (9/100)*Real.cos (v+d)+(18/100)*(1/2-rho0)*Real.sin (v+d)

private lemma cos_pi_add' (x : ℝ) : Real.cos (Real.pi+x) = -Real.cos x := by
  rw [add_comm]; exact Real.cos_add_pi x

private lemma sin_pi_add' (x : ℝ) : Real.sin (Real.pi+x) = -Real.sin x := by
  rw [add_comm]; exact Real.sin_add_pi x

private lemma quadrant {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 4/3) :
    0 ≤ Real.cos x ∧ 0 ≤ Real.sin x :=
  ⟨Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2,Real.pi_gt_d2]⟩,
   Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_d2])⟩

lemma system_nonnegative (v d : ℝ) : (system v d).Nonnegative := by
  intro i
  fin_cases i <;> norm_num [system]

lemma system_forces (v d : ℝ) (i : Fin 3) :
    (system v d).force i = ![forceC v d,forceW v d,forceD d] i := by
  fin_cases i <;> apply Prod.ext <;>
    simp [Stress.System.force,system,forceC,forceW,forceD,Fin.sum_univ_succ] <;> ring

private lemma cap_slope {v d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 3/5) (hv : 1-d ≤ v ∧ v ≤ 2/3) :
    0 ≤ (18/100)*Real.cos (v+d) ∧
    (rho0+1/2)*((18/100)*Real.cos (v+d)) ≤
      (1/2)*(39/100+(18/100)*Real.sin (v+d)) := by
  have hq : 1 ≤ v+d ∧ v+d ≤ 19/15 := by constructor <;> linarith [hd.2,hv.1,hv.2]
  have ht := quadrant (x := v+d) ⟨by linarith [hq.1],by linarith [hq.2]⟩
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (show (0:ℝ) ≤ 1 by norm_num) (show v+d ≤ Real.pi by linarith [hq.2,Real.pi_gt_d2]) hq.1
  have hc1 := Seven.cos_upper_four (x := 1) (by norm_num)
  have hV : (18/100)*Real.cos (v+d) ≤ 39/400 := by nlinarith
  have hV0 : 0 ≤ (18/100)*Real.cos (v+d) := mul_nonneg (by norm_num) ht.1
  have hprod := mul_le_mul
    (show rho0+1/2 ≤ 1613/1000 by linarith [rho0_upper]) hV hV0
    (by norm_num : (0:ℝ) ≤ 1613/1000)
  exact ⟨hV0,by nlinarith [ht.2]⟩

/-- The work of the force on W is at most its cap support
`ρ0 (39/100 + (18/100) sin (v + d))`: on the quadrilateral the force meets the
slope condition of the cap case. -/
lemma west_support {v d a b : ℝ} (hc : ContainedChart a |b|)
    (hd : 1/2 ≤ d ∧ d ≤ 3/5) (hv : 1-d ≤ v ∧ v ≤ 2/3) :
    dot (forceW v d) (orientedSquare (Real.pi-v) a b).center ≤
      rho0*(39/100+(18/100)*Real.sin (v+d)) := by
  let U := 39/100+(18/100)*Real.sin (v+d)
  let V := (18/100)*Real.cos (v+d)
  have hq := quadrant (x := v+d) ⟨by linarith [hv.1],by linarith [hv.2,hd.2]⟩
  have hU : 0 ≤ U := by
    show 0 ≤ 39/100+(18/100)*Real.sin (v+d)
    linarith [hq.2]
  have hs := cap_slope hd hv
  have hbox : (a+1/2)^2+(|b|+1/2)^2 ≤ Q0 := hc.containment
  have hcorner := disk_corner_support
    (A := a+1/2) (B := |b|+1/2) (a := rho0+1/2) (b := (1:ℝ)/2)
    (c := U) (s := V) (by linarith [rho0_lower])
    (by linarith [abs_nonneg b]) hU (by nlinarith [rho0_sq]) hbox hs.2
  have hb : -b*V ≤ |b| * V := mul_le_mul_of_nonneg_right (neg_le_abs b) hs.1
  have he : dot (forceW v d) (orientedSquare (Real.pi-v) a b).center=U*a-V*b := by
    dsimp [forceW,dot,orientedSquare,U,V]
    rw [Real.cos_pi_sub,Real.sin_pi_sub,Real.cos_add,Real.sin_add]
    linear_combination (39/100)*a*(Real.sin_sq_add_cos_sq v)
  rw [he]
  change U*a-V*b ≤ rho0*U
  linarith only [hcorner,hb]

/-- The work of the force on D is at most its vertex support
`R0 √(2173/10000) - 61/200`. -/
lemma diagonal_support {d a b : ℝ} (hc : ContainedChart a |b|) :
    dot (forceD d) (orientedSquare (Real.pi+d) a b).center ≤
      R0*Real.sqrt (2173/10000)-61/200 := by
  have h := Stress.center_le_vertexSupport R0_nonneg
    (oriented_contained_of_chart (t := Real.pi+d) hc) (forceD d)
  have hn : normSq (forceD d)=2173/10000 := by
    dsimp [normSq,forceD]
    linear_combination (2173/10000)*(Real.sin_sq_add_cos_sq d)
  have hx : frameX (orientedSquare (Real.pi+d) a b) (forceD d)=43/100 := by
    simp only [frameX,orientedSquare,forceD,cos_pi_add',sin_pi_add']
    linear_combination (43/100)*(Real.sin_sq_add_cos_sq d)
  have hy : frameY (orientedSquare (Real.pi+d) a b) (forceD d)=18/100 := by
    simp only [frameY,orientedSquare,forceD,cos_pi_add',sin_pi_add']
    linear_combination (18/100)*(Real.sin_sq_add_cos_sq d)
  have hw : width (orientedSquare (Real.pi+d) a b) (forceD d)=61/200 := by
    simp only [width,hx,hy]
    norm_num
  simpa only [Stress.vertexSupport,Stress.vectorLength,hn,hw] using h

private lemma minorant_le_raw (b : Bool) {v d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 3/5) (hv : 1-d ≤ v ∧ v ≤ 2/3) :
    minorant b v d ≤ raw b v d := by
  have tv := quadrant (x := v) ⟨by linarith [hv.1,hd.2],by linarith [hv.2]⟩
  have td := quadrant (x := d) ⟨by linarith [hd.1],by linarith [hd.2]⟩
  have tq := quadrant (x := v+d) ⟨by linarith [hv.1],by linarith [hv.2,hd.2]⟩
  have cu : c0 ≤ 113/1000 := by dsimp [c0]; linarith [rho0_upper]
  have cl : 11/100 ≤ c0 := by dsimp [c0]; linarith [rho0_lower]
  have pvc := mul_nonneg (sub_nonneg.mpr cu) tv.1
  have pdc := mul_nonneg (sub_nonneg.mpr cu) td.1
  have pvs := mul_nonneg (sub_nonneg.mpr cl) tv.2
  have pds := mul_nonneg (sub_nonneg.mpr cu) td.2
  have prho := mul_nonneg
    (show 0 ≤ 1113/1000-rho0 by linarith [rho0_upper])
    (show 0 ≤ 39/100+(18/100)*Real.sin (v+d) by linarith [tq.2])
  have hroot : Real.sqrt (2173/10000) ≤ 2331/5000 := by
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2173/10000 by norm_num)
    have hn := Real.sqrt_nonneg (2173/10000:ℝ)
    by_contra! h
    nlinarith
  have pnorm := mul_le_mul R0_lt_1689_1000.le hroot (Real.sqrt_nonneg _)
    (by norm_num : (0:ℝ) ≤ 1689/1000)
  cases b <;> dsimp [raw,minorant,vSin,dSin] <;>
    nlinarith only [pvc,pdc,pvs,pds,prho,pnorm]

private lemma defect_eq_raw (b : Bool) {v d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 3/5) (hv : 1-d ≤ v ∧ v ≤ 2/3) :
    (system v d).thresholdSum-(∑ i,upperValues b v d i)=raw b v d := by
  have tv := quadrant (x := v) ⟨by linarith [hv.1,hd.2],by linarith [hv.2]⟩
  have td := quadrant (x := d) ⟨by linarith [hd.1],by linarith [hd.2]⟩
  have tq := quadrant (x := v+d) ⟨by linarith [hv.1],by linarith [hv.2,hd.2]⟩
  cases b <;>
    simp [Stress.System.thresholdSum,system,upperValues,forceC,Fin.sum_univ_succ,
      raw,angularWidth,abs_of_nonneg tv.1,abs_of_nonneg tv.2,
      abs_of_nonneg td.1,abs_of_nonneg td.2,abs_of_nonneg tq.1,abs_of_nonneg tq.2] <;> ring

/-- If W is separated from C along its primary axis and `d ≤ 3/5`, then W and D
are not separated along the secondary axis of D. -/
theorem own_low_diagonal_impossible {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hdhigh : P.diagonalAngle ≤ 3/5)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) : False := by
  let v := -P.helperAngle 2
  let d := P.diagonalAngle
  have hd : 1/2 ≤ d ∧ d ≤ 3/5 := ⟨(normalized_diagonal_gt_half P).le,hdhigh⟩
  have hWphase : P.phase 2=Real.pi-v := by
    have h : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
    rw [h]; dsimp [v]; ring
  have hDphase : P.phase 3=Real.pi+d := by dsimp [d,NormalizedPacking.diagonalAngle]; ring
  have hgap := DW_Dsecondary_gap_gt_one P hsep
  rw [hWphase,hDphase] at hgap
  have hv : 1-d ≤ v ∧ v ≤ 2/3 := by
    dsimp [v] at *
    constructor <;> linarith [P.helper_windows.2.2.1.1]
  let S : Fin 3 → UnitSquare := ![axisSquare P.center,P.square 2,P.square 3]
  have he : (system v d).Separates S := by
    intro i
    fin_cases i
    · have hh := P.own_separator 2 hW
      rw [hWphase] at hh
      have hp := primary_difference (Real.pi-v) (P.radial 2) (P.transverse 2) P.center.1 P.center.2
      simp only [centralMargin] at hh
      have ht := quadrant (x := v) ⟨by linarith [hv.1,hd.2],by linarith [hv.2]⟩
      simp only [angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg,
        abs_of_nonneg ht.1,abs_of_nonneg ht.2] at hh
      change 1/2+angularWidth v ≤ dot (-Real.cos v,Real.sin v)
        (sub (P.square 2).center P.center)
      rw [P.square_def 2,hWphase]
      have hi : dot (-Real.cos v,Real.sin v)
          (sub (orientedSquare (Real.pi-v) (P.radial 2) (P.transverse 2)).center P.center)=
          P.radial 2-centralNormal (Real.pi-v) P.center.1 P.center.2 := by
        simpa [frameX,orientedSquare,dot,Real.cos_pi_sub,Real.sin_pi_sub] using hp
      rw [hi]
      simp only [angularWidth,abs_of_nonneg ht.1,abs_of_nonneg ht.2]
      linarith
    · have hh := P.own_separator 3 P.diagonal_own
      rw [hDphase] at hh
      have hp := primary_difference (Real.pi+d) (P.radial 3) (P.transverse 3) P.center.1 P.center.2
      simp only [centralMargin] at hh
      change 1/2+angularWidth d ≤ dot (-Real.cos d,-Real.sin d)
        (sub (P.square 3).center P.center)
      rw [P.square_def 3,hDphase]
      have hi : dot (-Real.cos d,-Real.sin d)
          (sub (orientedSquare (Real.pi+d) (P.radial 3) (P.transverse 3)).center P.center)=
          P.radial 3-centralNormal (Real.pi+d) P.center.1 P.center.2 := by
        simpa [frameX,orientedSquare,dot,cos_pi_add',sin_pi_add'] using hp
      rw [hi]
      have hw : angularWidth (Real.pi+d)=angularWidth d := by
        simp [angularWidth,cos_pi_add',sin_pi_add']
      rw [hw] at hh
      linarith
    · have hh := hsep
      rw [P.square_def 2,P.square_def 3,hWphase,hDphase,oriented_pair_threshold,
        show (Real.pi+d)-(Real.pi-v)=v+d by ring] at hh
      simpa [system,S,P.square_def,hWphase,hDphase,normalY,orientedSquare,
        cos_pi_add',sin_pi_add'] using hh
  have tx := quadrant (x := v) ⟨by linarith [hv.1,hd.2],by linarith [hv.2]⟩
  have td := quadrant (x := d) ⟨by linarith [hd.1],by linarith [hd.2]⟩
  have gx : 0 ≤ (forceC v d).1 := by dsimp only [forceC]; linarith [tx.1,td.1]
  have hcx := mul_le_mul_of_nonneg_right P.box.1.2 gx
  have finish (b : Bool)
      (hc : dot (forceC v d) P.center ≤ upperValues b v d 0) : False := by
    have hu (i : Fin 3) : dot ((system v d).force i) (S i).center ≤ upperValues b v d i := by
      rw [system_forces]
      fin_cases i
      · exact hc
      · dsimp [S,upperValues]
        rw [P.square_def 2,hWphase]
        exact west_support (P.contained 2) hd hv
      · dsimp [S,upperValues]
        rw [P.square_def 3,hDphase]
        exact diagonal_support (P.contained 3)
    have hn := (system v d).defect_nonpos S (upperValues b v d)
      (system_nonnegative v d) he hu
    rw [defect_eq_raw b hd hv] at hn
    have hp := (positive b hd hv).trans_le (minorant_le_raw b hd hv)
    linarith
  by_cases hy : 0 ≤ (forceC v d).2
  · apply finish true
    have hcy := mul_le_mul_of_nonneg_right P.box.2.2 hy
    dsimp [dot,upperValues]
    nlinarith only [hcx,hcy]
  · apply finish false
    have hcy := mul_nonpos_of_nonneg_of_nonpos P.box.2.1 (le_of_not_ge hy)
    dsimp [dot,upperValues]
    nlinarith only [hcx,hcy]

end SquaresInCircles.Six.Analytic.LowDWestSource

namespace SquaresInCircles.Six.Analytic
open Normalization

/-- If W and D are separated along the secondary axis of D, then `d > 3/5`. -/
theorem DW_Dsecondary_diagonal_gt_three_fifths {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    3/5 < P.diagonalAngle := by
  cases hW : P.ownBits 2
  · have hw := (abs_lt.mp (P.cardinal_angle 2 hW)).1
    have hg := DW_Dsecondary_gap_gt_one P hsep
    have h2 : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
    rw [h2] at hg
    dsimp [NormalizedPacking.diagonalAngle]
    linarith
  · by_contra! h
    exact LowDWestSource.own_low_diagonal_impossible P hW h hsep

lemma MissingWestWing.diagonal_gt_three_fifths {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : 3/5 < P.diagonalAngle :=
  DW_Dsecondary_diagonal_gt_three_fifths P h.from_diagonal

end SquaresInCircles.Six.Analytic
