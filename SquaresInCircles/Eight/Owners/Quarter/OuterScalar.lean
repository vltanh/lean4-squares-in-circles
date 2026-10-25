module

public import SquaresInCircles.Eight.Owners.Outer.AnchorDomain

/-!
# Eight squares: whole-interval scalar estimates for a core low-quarter target

The primary estimate is multiplied by its positive cosine.  Its
resulting elementary scalar is concave on the complete frame interval,
so only its two intrinsic endpoints enter.  The secondary estimate is
one direct cubic Taylor bound on each sign of the original error.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalQuarterOuter

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign GlobalOuterAnchor

def kappa : ℝ := 49/50

def primaryScalar (x : ℝ) : ℝ :=
  (x+163/1000)*Real.cos x-kappa/12-kappa*(183/200)*Real.sin x

def primaryScalarD (x : ℝ) : ℝ :=
  (1033/10000)*Real.cos x-(x+163/1000)*Real.sin x

def primaryScalarDD (x : ℝ) : ℝ :=
  -(11033/10000)*Real.sin x-(x+163/1000)*Real.cos x

theorem primaryScalar_derivative (x : ℝ) :
    HasDerivAt primaryScalar (primaryScalarD x) x := by
  have h := ((((hasDerivAt_id x).add_const (163/1000)).mul (Real.hasDerivAt_cos x)).sub_const
    (kappa/12)).sub ((Real.hasDerivAt_sin x).const_mul (kappa*(183/200)))
  convert h using 1
  · funext y
    simp only [primaryScalar,Pi.sub_apply,Pi.mul_apply,id]
  · simp only [primaryScalarD,kappa,id]
    ring

theorem primaryScalar_second_derivative (x : ℝ) :
    HasDerivAt primaryScalarD (primaryScalarDD x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul (1033/10000)).sub
    (((hasDerivAt_id x).add_const (163/1000)).mul (Real.hasDerivAt_sin x))
  convert h using 1
  · funext y
    simp only [primaryScalarD,Pi.sub_apply,Pi.mul_apply,id]
  · simp only [primaryScalarDD,id]
    ring

theorem primaryScalar_concave : ConcaveOn ℝ (Icc 0 frameCap) primaryScalar := by
  apply concave_of_deriv2 (fun x _ => primaryScalar_derivative x)
    (fun x _ => primaryScalar_second_derivative x)
  intro x hx
  have tr := transport_trig hx
  have hprod := mul_nonneg (show 0≤x+163/1000 by linarith [hx.1])
    (show 0≤Real.cos x by linarith [tr.1])
  dsimp [primaryScalarDD]
  linarith [tr.2.2.1]

theorem primaryScalar_positive {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0<primaryScalar x := by
  apply concave_gt_of_endpoints primaryScalar_concave hx
    (by norm_num [primaryScalar,kappa])
  have hs := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  norm_num at hs hc
  dsimp [primaryScalar,kappa,frameCap]
  linarith

theorem angle_cos_le_sin {x : ℝ} (hx : x∈Icc 0 frameCap) :
    x*Real.cos x≤Real.sin x := by
  have hd (z : ℝ) : HasDerivAt (fun z : ℝ => Real.sin z-z*Real.cos z) (z*Real.sin z) z := by
    have h := (Real.hasDerivAt_sin z).sub ((hasDerivAt_id z).mul (Real.hasDerivAt_cos z))
    convert h using 1
    · funext y
      simp only [Pi.sub_apply,Pi.mul_apply,id]
    · show z*Real.sin z=Real.cos z-(1*Real.cos z+z*-Real.sin z)
      ring
  have hm : MonotoneOn (fun z : ℝ => Real.sin z-z*Real.cos z) (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z _ => (hd z).continuousAt.continuousWithinAt
    · exact fun z _ => hd z
    · intro z hz
      exact mul_nonneg hz.1.le (transport_trig (Ioo_subset_Icc_self hz)).2.2.1
  have hh := hm (by norm_num [frameCap]) hx hx.1
  norm_num at hh
  linarith

/-- The actual primary projection, with an arbitrary signed source
transverse coordinate, forces this same linear lower charge. -/
theorem core_primary_bound {a A y d : ℝ}
    (ha : a∈Icc (447/800:ℝ) (283/200)) (hA : A≤7/12)
    (hd : |d|≤frameCap)
    (hm : GlobalOuterAnchor.width d≤A+a*Real.sin d+y*Real.cos d) :
    (327/1000:ℝ)<d+kappa*y := by
  have hc : 0<Real.cos d := by linarith [(signed_trig hd).1]
  have hprod : 0<(d+kappa*y-327/1000)*Real.cos d := by
    by_cases hp : 0≤d
    · have hd' : d∈Icc 0 frameCap := ⟨hp,(le_abs_self d).trans hd⟩
      have tr := transport_trig hd'
      have haSin := mul_le_mul_of_nonneg_right ha.2 tr.2.2.1
      have hs := primaryScalar_positive hd'
      dsimp [GlobalOuterAnchor.width] at hm
      rw [abs_of_nonneg tr.2.2.1] at hm
      dsimp [primaryScalar,kappa] at hs ⊢
      nlinarith only [hm,hA,haSin,hs]
    · have hd' : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
      have tr := transport_trig hd'
      have haSin := mul_le_mul_of_nonneg_right ha.1 tr.2.2.1
      have htan := angle_cos_le_sin hd'
      have hlow : 19/25<Real.cos (-d) := by linarith [tr.1]
      have hwidth : GlobalOuterAnchor.width d=(1+Real.cos (-d)+Real.sin (-d))/2 := by
        dsimp [GlobalOuterAnchor.width]
        rw [← Real.cos_neg d,← abs_neg (Real.sin d),← Real.sin_neg d,
          abs_of_nonneg tr.2.2.1]
      rw [hwidth] at hm
      have hsinneg : Real.sin d= -Real.sin (-d) := by simp
      rw [hsinneg,← Real.cos_neg d] at hm
      dsimp [kappa]
      rw [← Real.cos_neg d]
      nlinarith only [hm,hA,haSin,htan,hlow,tr.2.2.1]
  have hh := (mul_pos_iff_of_pos_right hc).1 hprod
  linarith

def secondaryScalar (d : ℝ) : ℝ := d-(kappa/12)*Real.cos d+
  (kappa/2)*|Real.sin d|-kappa*(14/25)*Real.sin d

theorem secondaryScalar_lower {d : ℝ} (hd : |d|≤frameCap) :
    -(3/20:ℝ)<secondaryScalar d := by
  by_cases hp : 0≤d
  · have hd' : d∈Icc 0 frameCap := ⟨hp,(le_abs_self d).trans hd⟩
    have tr := transport_trig hd'
    have hs := Real.sin_le hp
    dsimp [secondaryScalar,kappa]
    rw [abs_of_nonneg tr.2.2.1]
    nlinarith [Real.cos_le_one d]
  · have hx : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hs := Real.sin_ge_sub_cube hx.1
    have hc := Real.cos_le_one (-d)
    have h3 := pow_le_pow_left₀ hx.1 hx.2 3
    have hsin := (transport_trig hx).2.2.1
    dsimp [frameCap] at h3
    norm_num at h3
    have hid : secondaryScalar d= -(-d)-(kappa/12)*Real.cos (-d)+
        kappa*(53/50)*Real.sin (-d) := by
      dsimp [secondaryScalar]
      have hsinneg : Real.sin d= -Real.sin (-d) := by simp
      rw [← Real.cos_neg d,hsinneg]
      rw [abs_neg,abs_of_nonneg hsin]
      ring
    rw [hid]
    dsimp [kappa]
    nlinarith only [hs,hc,h3,hx.1]

theorem core_marker_upper (s : State) (hs : s.branch.type=0) :
    unsigned s<1/5+(27/25)*s.b ∧ s.b≤14/25 := by
  have ha := primary_lower s
  have hchart := FrameCoreArc.state_core_chart s hs
  have hb := (FrameCoreArc.core_bounds hchart).2.2.2
  have hb' : s.b≤14/25 := by linarith [CoreAngleEndpoint.diagonal_bounds.2]
  refine ⟨?_,hb'⟩
  cases hbr : s.branch <;> simp [hbr,Branch.type] at hs
  all_goals
    dsimp [unsigned]
    rw [hbr]
    dsimp [FramePair.label]
    nlinarith [s.b_nonneg]

theorem core_secondary_bound (t : State) {y d : ℝ}
    (hcore : t.branch.type=0) (hd : |d|≤frameCap)
    (hm : GlobalOuterAnchor.width d≤y+t.a*Real.cos d+t.b*Real.sin d) :
    -(581/1250:ℝ)<d+kappa*y-unsigned t := by
  have hc : 0≤Real.cos d := by linarith [(signed_trig hd).1]
  have ha := mul_le_mul_of_nonneg_right (core_bounds t hcore).1 hc
  have hmark := core_marker_upper t hcore
  have hcoef : 0≤(27/25:ℝ)+kappa*Real.sin d := by
    dsimp [kappa]
    linarith [Real.neg_one_le_sin d]
  have hprod := mul_le_mul_of_nonneg_left hmark.2 hcoef
  have hscalar := secondaryScalar_lower hd
  dsimp [secondaryScalar,GlobalOuterAnchor.width,kappa] at *
  nlinarith only [ha,hmark.1,hprod,hscalar,hm]

end SquaresInCircles.Eight.GlobalQuarterOuter
