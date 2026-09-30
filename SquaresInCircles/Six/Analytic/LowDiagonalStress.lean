import SquaresInCircles.Six.Analytic.CompensatedTrigConcavity
import SquaresInCircles.Six.Analytic.FrozenPrimaryEndpoints
import SquaresInCircles.Six.Normalization.CapSupport

/-!
# Low-diagonal secondary stresses before support maximization

False denotes the W-secondary source, with weights (31,44,25)/100 on
C-D,C-W,W-D. True denotes the D-secondary source, with (42,37,21)/100.
The local centers and the central center are frozen while varying v=-w,d.
Only endpoint supports are maximized. The mixed endpoint uses the genuine
constrained-disk slope condition, not coordinate dominance.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def lowAlpha (ds : Bool) : ℝ := if ds then 42/100 else 31/100
def lowBeta (ds : Bool) : ℝ := if ds then 37/100 else 44/100
def lowMu (ds : Bool) : ℝ := if ds then 21/100 else 25/100

def lowVariable (ds : Bool) : ℝ := if ds then lowBeta ds else lowAlpha ds
def lowFixed (ds : Bool) : ℝ := if ds then lowAlpha ds else lowBeta ds

def lowWForce (ds : Bool) (q : ℝ) : Point :=
  if ds then (lowBeta ds+lowMu ds*Real.sin q,-lowMu ds*Real.cos q)
  else (lowBeta ds,-lowMu ds)

def lowDForce (ds : Bool) (q : ℝ) : Point :=
  if ds then (lowAlpha ds,lowMu ds)
  else (lowAlpha ds+lowMu ds*Real.sin q,lowMu ds*Real.cos q)

def lowFrozen (ds : Bool) (v d aw bw ad bd cx cy : ℝ) : ℝ :=
  1/2+(lowBeta ds/2)*(Real.cos v+Real.sin v)+(lowAlpha ds/2)*(Real.cos d+Real.sin d)+
    (lowMu ds/2)*(Real.cos (v+d)+Real.sin (v+d))-
    dot (lowWForce ds (v+d)) (aw,bw)-dot (lowDForce ds (v+d)) (ad,bd)-
    ((lowBeta ds*Real.cos v+lowAlpha ds*Real.cos d)*cx+
      (lowAlpha ds*Real.sin d-lowBeta ds*Real.sin v)*cy)

lemma low_weights (ds : Bool) :
    0≤lowAlpha ds ∧ 0≤lowBeta ds ∧ 0≤lowMu ds ∧ lowAlpha ds+lowBeta ds+lowMu ds=1 := by
  cases ds <;> norm_num [lowAlpha,lowBeta,lowMu]

lemma low_frozen_formula (ds : Bool) (v d aw bw ad bd cx cy : ℝ) :
    lowFrozen ds v d aw bw ad bd cx cy=
      frozenTrig (1/2-lowBeta ds*aw-lowAlpha ds*ad+
        (if ds then -lowMu ds*bd else lowMu ds*bw))
        (lowBeta ds*(1/2-cx)) (lowBeta ds*(1/2+cy))
        (lowAlpha ds*(1/2-cx)) (lowAlpha ds*(1/2-cy))
        (lowMu ds*(if ds then 1/2+bw else 1/2-bd))
        (lowMu ds*(if ds then 1/2-aw else 1/2-ad)) v d := by
  cases ds <;> dsimp [lowFrozen,lowWForce,lowDForce,frozenTrig] <;> ring

lemma low_rotating_norm (p mu q : ℝ) :
    (p+mu*Real.sin q)^2+(mu*Real.cos q)^2=p^2+mu^2+2*p*mu*Real.sin q := by
  linear_combination mu^2*(Real.sin_sq_add_cos_sq q)

/-- The cap support is used only under the full constrained-circle slope test. -/
lemma cap_linear_upper {a b U V : ℝ} (hc : ContainedChart a |b|)
    (hU : 0≤U) (hV : 0≤V) (hslope : (rho0+1/2)*V≤U/2) :
    U*a-V*b≤(1113/1000)*U := by
  have hh := disk_corner_support (A := a+1/2) (B := |b|+1/2)
    (a := rho0+1/2) (b := (1:ℝ)/2) (c := U) (s := V)
    (by linarith [rho0_gt_one]) (by linarith [abs_nonneg b]) hU
    (by nlinarith [rho0_identity]) hc.containment (by linarith)
  have hsign := mul_le_mul_of_nonneg_left (neg_le_abs b) hV
  have hrad := mul_le_mul_of_nonneg_right rho0_upper.le hU
  nlinarith

/-- One vertex-support rule for both fixed-source choices. L0 and L are root
upper bounds proved at the original rectangle corners by squaring. -/
lemma low_vertex_endpoint_lower (ds : Bool) {v d aw bw ad bd cx cy L0 L X Y : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hcos : 0≤Real.cos (v+d)) (hsin : 0≤Real.sin (v+d))
    (hL0 : 0≤L0) (hL : 0≤L)
    (hn0 : (lowFixed ds)^2+(lowMu ds)^2≤L0^2)
    (hn : (lowVariable ds)^2+(lowMu ds)^2+
      2*lowVariable ds*lowMu ds*Real.sin (v+d)≤L^2)
    (hX : 0≤X) (hY : 0≤Y)
    (hcx : lowBeta ds*Real.cos v+lowAlpha ds*Real.cos d≤X)
    (hcy : lowAlpha ds*Real.sin d-lowBeta ds*Real.sin v≤Y) :
    1+(lowBeta ds/2)*(Real.cos v+Real.sin v)+(lowAlpha ds/2)*(Real.cos d+Real.sin d)+
      lowMu ds*(Real.cos (v+d)+Real.sin (v+d))-
      (1689/1000)*(L0+L)-(113/1000)*(X+Y)≤lowFrozen ds v d aw bw ad bd cx cy := by
  have hD' : ContainedChart ad |-bd| := by simpa only [abs_neg] using hD
  have hcentral := coarse_central_work hc hX hY hcx hcy
  cases ds
  · have hWb := vertex_linear_upper hW (U := 44/100) (V := 25/100) (by norm_num) hL0 hn0
    have hDb := vertex_linear_upper hD' (U := 31/100+(25/100)*Real.sin (v+d))
      (V := (25/100)*Real.cos (v+d)) (by positivity) hL
      (by rw [low_rotating_norm]; exact hn)
    dsimp [lowFrozen,lowWForce,lowDForce,lowAlpha,lowBeta,lowMu,dot]
    nlinarith only [hWb,hDb,hcentral]
  · have hDb := vertex_linear_upper hD' (U := 42/100) (V := 21/100) (by norm_num) hL0 hn0
    have hWb := vertex_linear_upper hW (U := 37/100+(21/100)*Real.sin (v+d))
      (V := (21/100)*Real.cos (v+d)) (by positivity) hL
      (by rw [low_rotating_norm]; exact hn)
    dsimp [lowFrozen,lowWForce,lowDForce,lowAlpha,lowBeta,lowMu,dot]
    nlinarith only [hWb,hDb,hcentral]

/-- The mixed corner uses the proved cap slope; the other force remains on its
universally valid vertex upper bound. No branch is selected by U>|V|. -/
lemma low_cap_endpoint_lower (ds : Bool) {v d aw bw ad bd cx cy L0 X Y : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hcos : 0≤Real.cos (v+d)) (hsin : 0≤Real.sin (v+d))
    (hL0 : 0≤L0) (hn0 : (lowFixed ds)^2+(lowMu ds)^2≤L0^2)
    (hslope : (rho0+1/2)*(lowMu ds*Real.cos (v+d))≤
      (lowVariable ds+lowMu ds*Real.sin (v+d))/2)
    (hX : 0≤X) (hY : 0≤Y)
    (hcx : lowBeta ds*Real.cos v+lowAlpha ds*Real.cos d≤X)
    (hcy : lowAlpha ds*Real.sin d-lowBeta ds*Real.sin v≤Y) :
    (1+lowFixed ds+lowMu ds)/2+
      (lowBeta ds/2)*(Real.cos v+Real.sin v)+(lowAlpha ds/2)*(Real.cos d+Real.sin d)+
      (lowMu ds/2)*(Real.cos (v+d)+Real.sin (v+d))-
      (1689/1000)*L0-(1113/1000)*(lowVariable ds+lowMu ds*Real.sin (v+d))-
      (113/1000)*(X+Y)≤lowFrozen ds v d aw bw ad bd cx cy := by
  have hD' : ContainedChart ad |-bd| := by simpa only [abs_neg] using hD
  have hcentral := coarse_central_work hc hX hY hcx hcy
  cases ds
  · have hWb := vertex_linear_upper hW (U := 44/100) (V := 25/100) (by norm_num) hL0 hn0
    have hDb := cap_linear_upper hD' (U := 31/100+(25/100)*Real.sin (v+d))
      (V := (25/100)*Real.cos (v+d)) (by positivity) (by positivity) hslope
    dsimp [lowFrozen,lowWForce,lowDForce,lowAlpha,lowBeta,lowMu,lowFixed,lowVariable,dot]
    nlinarith only [hWb,hDb,hcentral]
  · have hDb := vertex_linear_upper hD' (U := 42/100) (V := 21/100) (by norm_num) hL0 hn0
    have hWb := cap_linear_upper hW (U := 37/100+(21/100)*Real.sin (v+d))
      (V := (21/100)*Real.cos (v+d)) (by positivity) (by positivity) hslope
    dsimp [lowFrozen,lowWForce,lowDForce,lowAlpha,lowBeta,lowMu,lowFixed,lowVariable,dot]
    nlinarith only [hWb,hDb,hcentral]

end SquaresInCircles.Six.Analytic
