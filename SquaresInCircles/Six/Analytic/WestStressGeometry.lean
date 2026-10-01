import SquaresInCircles.Six.Analytic.WestStressDPositive
import SquaresInCircles.Six.Analytic.CapChart
import SquaresInCircles.Six.Stress.Support

/-!
# The actual three-square geometry behind the analytic Appendix A stress

The multipliers are (3/10,9/20,1/4), on C--D, C--W and W--D. The central
force and both exterior forces are computed exactly. Universal vertex support
is used; selected signed projections give valid lower bounds for the widths,
so no unproved cap-branch or absolute-value sign is assumed. The two remaining
secondary normals give precisely the expressions proved positive above.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private lemma west_cos_pi_add (x:ℝ) : Real.cos (Real.pi+x)=-Real.cos x := by
  rw [add_comm,Real.cos_add_pi]

private lemma west_sin_pi_add (x:ℝ) : Real.sin (Real.pi+x)=-Real.sin x := by
  rw [add_comm,Real.sin_add_pi]

def westForceC (t:ℝ) : Point := (3/10+(9/20)*Real.cos t,(9/20)*Real.sin t)
def westForceW (t z:ℝ) : Point :=
  (-(9/20)*Real.cos t-(1/4)*Real.sin z,-(9/20)*Real.sin t+(1/4)*Real.cos z)
def westForceD (z:ℝ) : Point := (-3/10+(1/4)*Real.sin z,-(1/4)*Real.cos z)
def westNormal (z:ℝ) : Point := (Real.sin z,-Real.cos z)

def westThreshold (t u:ℝ) : ℝ :=
  (3/10)*(1/2+angularWidth u)+(9/20)*(1/2+angularWidth t)+(1/4)*(1/2+angularWidth (u-t))

def westWidthW (t z:ℝ) : ℝ := 9/40+(1/8)*(Real.sin (z-t)+Real.cos (z-t))
def westWidthD (u z:ℝ) : ℝ :=
  (3/20)*Real.cos u-(3/20)*Real.sin u+(1/8)*(Real.sin (u-z)+Real.cos (u-z))

def westGeometricDefect (t u z:ℝ) : ℝ :=
  westThreshold t u-westCentralSupport t-
    R0*Real.sqrt (53/200+(9/40)*Real.sin (z-t))-
    R0*Real.sqrt (61/400-(3/20)*Real.sin z)+westWidthW t z+westWidthD u z

lemma west_force_balance (c W D:Point) (t z:ℝ) :
    (3/10)*dot (-1,0) (sub D c)+(9/20)*dot (-Real.cos t,-Real.sin t) (sub W c)+
      (1/4)*dot (westNormal z) (sub D W) =
      dot (westForceC t) c+dot (westForceW t z) W+dot (westForceD z) D := by
  dsimp [dot,sub,westNormal,westForceC,westForceW,westForceD]
  ring

lemma west_forceW_norm (t z:ℝ) : normSq (westForceW t z)=53/200+(9/40)*Real.sin (z-t) := by
  dsimp [normSq,westForceW]
  rw [Real.sin_sub]
  linear_combination (81/400)*(Real.sin_sq_add_cos_sq t)+(1/16)*(Real.sin_sq_add_cos_sq z)

lemma west_forceD_norm (z:ℝ) : normSq (westForceD z)=61/400-(3/20)*Real.sin z := by
  dsimp [normSq,westForceD]
  linear_combination (1/16)*(Real.sin_sq_add_cos_sq z)

lemma west_forceW_frameX (t z a b:ℝ) :
    frameX (orientedSquare (Real.pi+t) a b) (westForceW t z)=9/20+(1/4)*Real.sin (z-t) := by
  dsimp [frameX,orientedSquare,westForceW]
  rw [west_cos_pi_add,west_sin_pi_add,Real.sin_sub]
  linear_combination (9/20)*(Real.sin_sq_add_cos_sq t)

lemma west_forceW_frameY (t z a b:ℝ) :
    frameY (orientedSquare (Real.pi+t) a b) (westForceW t z)=-(1/4)*Real.cos (z-t) := by
  dsimp [frameY,orientedSquare,westForceW]
  rw [west_cos_pi_add,west_sin_pi_add,Real.cos_sub]
  ring

lemma west_forceD_frameX (u z A B:ℝ) :
    frameX (orientedSquare (Real.pi+u) A B) (westForceD z)=
      (3/10)*Real.cos u+(1/4)*Real.sin (u-z) := by
  dsimp [frameX,orientedSquare,westForceD]
  rw [west_cos_pi_add,west_sin_pi_add,Real.sin_sub]
  ring

lemma west_forceD_frameY (u z A B:ℝ) :
    frameY (orientedSquare (Real.pi+u) A B) (westForceD z)=
      -(3/10)*Real.sin u+(1/4)*Real.cos (u-z) := by
  dsimp [frameY,orientedSquare,westForceD]
  rw [west_cos_pi_add,west_sin_pi_add,Real.cos_sub]
  ring

lemma west_widthW_lower (t z a b:ℝ) :
    westWidthW t z≤width (orientedSquare (Real.pi+t) a b) (westForceW t z) := by
  rw [width,west_forceW_frameX,west_forceW_frameY]
  have hx := le_abs_self (9/20+(1/4)*Real.sin (z-t))
  have hy := neg_le_abs (-(1/4)*Real.cos (z-t))
  dsimp [westWidthW]
  linarith

lemma west_widthD_lower (u z A B:ℝ) :
    westWidthD u z≤width (orientedSquare (Real.pi+u) A B) (westForceD z) := by
  rw [width,west_forceD_frameX,west_forceD_frameY]
  have hx := le_abs_self ((3/10)*Real.cos u+(1/4)*Real.sin (u-z))
  have hy := le_abs_self (-(3/10)*Real.sin u+(1/4)*Real.cos (u-z))
  dsimp [westWidthD]
  linarith

lemma west_central_support {c:Point} {t:ℝ}
    (hc:(0≤c.1 ∧ c.1≤c0) ∧ (0≤c.2 ∧ c.2≤c0))
    (ht:-2/3≤t ∧ t≤2/5) : dot (westForceC t) c≤westCentralSupport t := by
  have htr := west_angle_bounds ht
  have hx := mul_nonneg (sub_nonneg.mpr hc.1.2)
    (show 0≤3/10+(9/20)*Real.cos t by linarith [htr.1])
  have hy := Stress.scalar_box_support (v:=Real.sin t) hc.2
  dsimp [dot,westForceC,westCentralSupport]
  nlinarith

lemma west_own_separator {c:Point} {t a b:ℝ}
    (h:0≤centralMargin .own (Real.pi+t) a b c.1 c.2) :
    1/2+angularWidth t≤dot (-Real.cos t,-Real.sin t)
      (sub (orientedSquare (Real.pi+t) a b).center c) := by
  have hp := primary_difference (Real.pi+t) a b c.1 c.2
  have hd : dot (-Real.cos t,-Real.sin t)
      (sub (orientedSquare (Real.pi+t) a b).center c)=a-centralNormal (Real.pi+t) c.1 c.2 := by
    simpa only [frameX,orientedSquare,dot,west_cos_pi_add,west_sin_pi_add,Prod.mk.eta] using hp
  rw [hd]
  simp only [centralMargin,angularWidth,west_cos_pi_add,west_sin_pi_add,abs_neg] at h
  dsimp [angularWidth]
  linarith

lemma west_cardinal_separator {c:Point} {u A B:ℝ}
    (h:0≤centralMargin .west (Real.pi+u) A B c.1 c.2) :
    1/2+angularWidth u≤dot (-1,0) (sub (orientedSquare (Real.pi+u) A B).center c) := by
  simp only [centralMargin,angularWidth,west_cos_pi_add,west_sin_pi_add,abs_neg] at h
  dsimp [dot,sub,orientedSquare,centerX,angularWidth] at h ⊢
  simp only [west_cos_pi_add,west_sin_pi_add] at h ⊢
  linarith

/-- Any actual selected forward secondary normal has nonpositive defect. -/
theorem west_geometric_defect_nonpos {c:Point} {t u z a b A B:ℝ}
    (hc:(0≤c.1 ∧ c.1≤c0) ∧ (0≤c.2 ∧ c.2≤c0))
    (hW:ContainedChart a |b|) (hD:ContainedChart A |B|)
    (ht:-2/3≤t ∧ t≤2/5)
    (hCW:0≤centralMargin .own (Real.pi+t) a b c.1 c.2)
    (hCD:0≤centralMargin .west (Real.pi+u) A B c.1 c.2)
    (hWD:1/2+angularWidth (u-t)≤dot (westNormal z)
      (sub (orientedSquare (Real.pi+u) A B).center (orientedSquare (Real.pi+t) a b).center)) :
    westGeometricDefect t u z≤0 := by
  have hCW' := west_own_separator hCW
  have hCD' := west_cardinal_separator hCD
  have hsep : westThreshold t u≤
      dot (westForceC t) c+
      dot (westForceW t z) (orientedSquare (Real.pi+t) a b).center+
      dot (westForceD z) (orientedSquare (Real.pi+u) A B).center := by
    rw [← west_force_balance]
    dsimp [westThreshold]
    linarith
  have hboxW : (|a|+1/2)^2+(|b|+1/2)^2≤Q0 := by
    simpa only [abs_of_nonneg (show 0≤a by linarith [hW.half_le])] using hW.containment
  have hboxD : (|A|+1/2)^2+(|B|+1/2)^2≤Q0 := by
    simpa only [abs_of_nonneg (show 0≤A by linarith [hD.half_le])] using hD.containment
  have hWsup := Stress.center_le_vertexSupport R0_nonneg
    (contained_from_corner (t:=Real.pi+t) hboxW) (westForceW t z)
  have hDsup := Stress.center_le_vertexSupport R0_nonneg
    (contained_from_corner (t:=Real.pi+u) hboxD) (westForceD z)
  simp only [Stress.vertexSupport,Stress.vectorLength,west_forceW_norm,west_forceD_norm] at hWsup hDsup
  have hw := west_widthW_lower t z a b
  have hd := west_widthD_lower u z A B
  have hcc := west_central_support hc ht
  dsimp [westGeometricDefect]
  linarith

lemma west_defect_source_form {t u:ℝ}
    (ht:-2/3≤t) (hu0:-2/5≤u) (hu1:u≤2/5) (htu:t≤u) :
    westGeometricDefect t u t=westStressW t u ∧
      westGeometricDefect t u u=westStressD t u := by
  have hct : 0≤Real.cos t := by
    linarith [(west_angle_bounds ⟨ht,htu.trans hu1⟩).1]
  have hcu : 0≤Real.cos u := by
    linarith [(west_angle_bounds ⟨by linarith,hu1⟩).1]
  have hδ := west_difference_trig (d:=u-t) ⟨by linarith,by linarith⟩
  have hcδ : 0≤Real.cos (u-t) := by linarith [hδ.1]
  have hsδ := hδ.2.1
  have habs : |Real.sin u|-Real.sin u=2*max (-Real.sin u) 0 := by
    by_cases h:0≤Real.sin u
    · rw [abs_of_nonneg h,max_eq_right (by linarith)]
      ring
    · rw [abs_of_neg (lt_of_not_ge h),max_eq_left (by linarith)]
      ring
  constructor
  all_goals simp only [westGeometricDefect,westThreshold,westWidthW,westWidthD,
    westStressW,westStressD,sub_self,Real.sin_zero,Real.cos_zero,mul_zero,add_zero,
    angularWidth,abs_of_nonneg hct,abs_of_nonneg hcu,abs_of_nonneg hcδ,abs_of_nonneg hsδ]
  all_goals linarith only [habs]

/-- Analytic Appendix A on its entire compact triangle. The two explicit core
premises are already outputs of normalization before this theorem is applied. -/
theorem west_cardinal_impossible {c:Point} {t u a b A B:ℝ}
    (hc:(0≤c.1 ∧ c.1≤c0) ∧ (0≤c.2 ∧ c.2≤c0))
    (hW:ContainedChart a |b|) (hD:ContainedChart A |B|)
    (hWcore:AvoidsCore a |b|) (hDcore:AvoidsCore A |B|)
    (ht:-2/3≤t) (hu0:-2/5≤u) (hu1:u≤2/5) (htu:t≤u)
    (hCW:0≤centralMargin .own (Real.pi+t) a b c.1 c.2)
    (hCD:0≤centralMargin .west (Real.pi+u) A B c.1 c.2)
    (hWD:∀ p,¬(openSquare (orientedSquare (Real.pi+t) a b) p ∧
      openSquare (orientedSquare (Real.pi+u) A B) p)) : False := by
  have hforms := west_defect_source_form ht hu0 hu1 htu
  rcases west_secondary_axes hW hD hWcore hDcore ht hu1 htu hWD with h | h
  · have h' : 1/2+angularWidth (u-t)≤dot (westNormal t)
        (sub (orientedSquare (Real.pi+u) A B).center (orientedSquare (Real.pi+t) a b).center) := by
      simpa only [westNormal,normalY,orientedSquare,west_sin_pi_add,west_cos_pi_add,neg_neg] using h
    have hn := west_geometric_defect_nonpos hc hW hD ⟨ht,htu.trans hu1⟩ hCW hCD h'
    rw [hforms.1] at hn
    linarith [westStressW_positive ht hu0 hu1 htu]
  · have h' : 1/2+angularWidth (u-t)≤dot (westNormal u)
        (sub (orientedSquare (Real.pi+u) A B).center (orientedSquare (Real.pi+t) a b).center) := by
      simpa only [westNormal,normalY,orientedSquare,west_sin_pi_add,west_cos_pi_add,neg_neg] using h
    have hn := west_geometric_defect_nonpos hc hW hD ⟨ht,htu.trans hu1⟩ hCW hCD h'
    rw [hforms.2] at hn
    linarith [westStressD_positive ht hu0 hu1 htu]

end SquaresInCircles.Six.Analytic
