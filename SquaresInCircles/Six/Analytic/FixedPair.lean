import SquaresInCircles.Six.Analytic.PairConstants
import SquaresInCircles.Six.Stress.VertexEnvelope

/-!
# A fixed-central-weight adjacent-pair stress

Both central edge weights are one. The outer weights remain the candidate's
r and m. The central-force excess is paid using the exact candidate box.
The cardinal W/S interval is the full [-2/5,2/5] supplied by normalization;
no extra -1/6 tail bound is required. The OWN helper interval remains an
explicit domain-reduction obligation.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

def Domain (no wo : Bool) (n w : ℝ) : Prop :=
  (if no then -3/10≤n ∧ n≤5/12 else -203/1000≤n ∧ n≤203/1000) ∧
  (if wo then -11/25≤w ∧ w≤2/25 else -2/5≤w ∧ w≤2/5)

def line (w : ℝ) : ℝ := (18/25)*max (-w) 0-(13/50)*max w 0

def penalty (no wo : Bool) (n w : ℝ) : ℝ :=
  (if no then cStar*(max (Real.sin n) 0+1-Real.cos n) else 0)+
  (if wo then cStar*max (Real.sin w) 0 else 0)

def northForce (no : Bool) (u : Fin 4) (n w : ℝ) : Point :=
  ((pairNorthBase no n).1+rStar*(pairNorthSource u (n-w)).1,
   (pairNorthBase no n).2+rStar*(pairNorthSource u (n-w)).2)

def westForce (wo : Bool) (u : Fin 4) (n w : ℝ) : Point :=
  ((pairWestBase wo w).1+rStar*(pairWestSource u (n-w)).1,
   (pairWestBase wo w).2+rStar*(pairWestSource u (n-w)).2-mStar)

def threshold (n w : ℝ) : ℝ :=
  (1/2+angularWidth n)+(1/2+angularWidth w)+rStar*(1/2+angularWidth (n-w))+mStar/2

def value (no wo : Bool) (u : Fin 4) (n w : ℝ) : ℝ :=
  threshold n w-scalarSupport Six.radius (northForce no u n w).1 (northForce no u n w).2-
    scalarSupport Six.radius (westForce wo u n w).1 (westForce wo u n w).2-penalty no wo n w

lemma center_radial_bound {a b : ℝ}
    (hc : (|a|+1/2)^2+(|b|+1/2)^2≤Six.radius^2) : a^2+b^2≤rhoStar^2 := by
  by_contra! hr
  have hsum : |a|+|b|<rhoStar := by
    nlinarith [rhoStar_identity,Six.radius_sq,sq_abs a,sq_abs b]
  have hp := mul_pos (sub_pos.mpr hsum)
    (show 0<rhoStar+|a|+|b| by linarith [rhoStar_gt_11_10,abs_nonneg a,abs_nonneg b])
  nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg b),sq_abs a,sq_abs b]

lemma orderedSupport_le_radial {U V : ℝ} (hV : 0≤V) (hUV : V≤U) :
    orderedSupport Six.radius U V ≤ rhoStar*Real.sqrt (U^2+V^2) := by
  have hU : 0≤U := hV.trans hUV
  have hrad : 0≤rhoStar := by linarith [rhoStar_gt_11_10]
  let L := Real.sqrt (U^2+V^2)
  have hL0 : 0≤L := Real.sqrt_nonneg _
  have hLsq : L^2=U^2+V^2 := Real.sq_sqrt (by positivity)
  have hUL : U≤L := by nlinarith [sq_nonneg V]
  unfold orderedSupport
  split_ifs with hswitch
  · change rhoStar*U≤rhoStar*L
    exact mul_le_mul_of_nonneg_left hUL hrad
  · have hswitch' : L<2*Six.radius*V := lt_of_not_ge hswitch
    have hVpos : 0<V := by nlinarith [Six.radius_pos]
    have hL : 0<L := by nlinarith
    let a := Six.radius*U/L-1/2
    let b := Six.radius*V/L-1/2
    have hb : 0≤b := by
      dsimp [b]
      apply sub_nonneg.mpr
      apply (le_div_iff₀ hL).mpr
      linarith
    have ha : 0≤a := by
      have h := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hUV Six.radius_pos.le) hL.le
      dsimp [a,b] at *
      linarith
    have hcircle : (|a|+1/2)^2+(|b|+1/2)^2=Six.radius^2 := by
      rw [abs_of_nonneg ha,abs_of_nonneg hb]
      dsimp [a,b]
      field_simp [ne_of_gt hL]
      nlinarith [hLsq]
    have hc := center_radial_bound hcircle.le
    have hh := dot_le_radius (v := (U,V)) (p := (a,b)) hrad hc
    have hid : U*a+V*b=Six.radius*L-(U+V)/2 := by
      dsimp [a,b]
      field_simp [ne_of_gt hL]
      nlinarith [hLsq]
    dsimp [dot,vectorLength,normSq] at hh
    rw [hid] at hh
    exact hh

/-- Only the N force of the two strict sources uses this radial upper support. -/
lemma scalarSupport_le_radial (x y : ℝ) :
    scalarSupport Six.radius x y≤rhoStar*Real.sqrt (x^2+y^2) := by
  unfold scalarSupport
  split_ifs with h
  · simpa only [sq_abs] using orderedSupport_le_radial (abs_nonneg y) h
  · have hh := orderedSupport_le_radial (abs_nonneg x) (le_of_not_ge h)
    simpa only [sq_abs,add_comm] using hh

def northRadius (u : Fin 4) : ℝ := if u=0 ∨ u=3 then Six.radius else rhoStar

def northUpper (u : Fin 4) (g : Point) : ℝ :=
  if u=0 ∨ u=3 then northVertex g.1 g.2 else rhoStar*Real.sqrt (g.1^2+g.2^2)

def minorant (no wo : Bool) (u : Fin 4) (n w : ℝ) : ℝ :=
  threshold n w-northUpper u (northForce no u n w)-
    northVertex (westForce wo u n w).1 (westForce wo u n w).2-penalty no wo n w

lemma minorant_le_value (no wo : Bool) (u : Fin 4) (n w : ℝ) :
    minorant no wo u n w≤value no wo u n w := by
  have hN : scalarSupport Six.radius (northForce no u n w).1 (northForce no u n w).2≤
      northUpper u (northForce no u n w) := by
    unfold northUpper
    split_ifs
    · exact scalarSupport_le_northVertex _ _
    · exact scalarSupport_le_radial _ _
  have hW := scalarSupport_le_northVertex (westForce wo u n w).1 (westForce wo u n w).2
  dsimp [minorant,value]
  linarith

@[simp] lemma northForce_zero (no : Bool) (u : Fin 4) :
    northForce no u 0 0=pairNorthForce no false u 0 0 := by
  cases no <;> fin_cases u <;>
    norm_num [northForce,pairNorthForce,pairNorthBase,pairNorthSource,pairAlpha]

@[simp] lemma westForce_zero (wo : Bool) (u : Fin 4) :
    westForce wo u 0 0=pairWestForce false wo u 0 0 := by
  cases wo <;> fin_cases u <;>
    norm_num [westForce,pairWestForce,pairWestBase,pairWestSource,pairGamma]

@[simp] lemma penalty_zero (no wo : Bool) : penalty no wo 0 0=0 := by
  cases no <;> cases wo <;> norm_num [penalty]

@[simp] lemma threshold_zero : threshold 0 0=2+rStar+mStar/2 := by
  norm_num [threshold,angularWidth]
  ring

lemma minorant_zero (no wo : Bool) {u : Fin 4} (hu : u=0 ∨ u=3) :
    minorant no wo u 0 0=pairBase := by
  have hN := (pair_candidate_forces no false hu).1
  have hW := (pair_candidate_forces false wo hu).2
  simp only [minorant,northUpper,if_pos hu,northForce_zero,westForce_zero,
    hN,hW,threshold_zero,penalty_zero,sub_zero]
  exact pairBase_vertex_identity

/-- Excess central force relative to the zero-angle resultant (1,-1). -/
def centralExcess (no wo : Bool) (n w : ℝ) : Point :=
  ((if no then Real.sin n else 0)+(if wo then Real.cos w-1 else 0),
   (if no then 1-Real.cos n else 0)+(if wo then Real.sin w else 0))

lemma central_excess_support {c : Point}
    (hc : (0≤c.1 ∧ c.1≤cStar) ∧ (0≤c.2 ∧ c.2≤cStar))
    (no wo : Bool) (n w : ℝ) : dot (centralExcess no wo n w) c≤penalty no wo n w := by
  have hsn : c.1*Real.sin n≤cStar*max (Real.sin n) 0 := scalar_box_support hc.1
  have hsw : c.2*Real.sin w≤cStar*max (Real.sin w) 0 := scalar_box_support hc.2
  have hwn := mul_nonpos_of_nonneg_of_nonpos hc.1.1 (sub_nonpos.mpr (Real.cos_le_one w))
  have hcn := mul_le_mul_of_nonneg_right hc.2.2 (sub_nonneg.mpr (Real.cos_le_one n))
  cases no <;> cases wo <;> dsimp [centralExcess,penalty,dot] <;> nlinarith

lemma line_decrease (w : ℝ) : pairLine w-line w=(1/100)*max (-w) 0 := by
  dsimp [pairLine,line]
  ring

end SquaresInCircles.Six.Analytic.FixedPair
