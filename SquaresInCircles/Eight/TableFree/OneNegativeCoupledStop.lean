module

public import SquaresInCircles.Eight.TableFree.OneNegativeCoupledArc

/-!
# First hard contact or the actual H=D barrier

Uncompiled source. The coupled motion stops at the first BT2 contact or
at H=D, whichever comes first. Its original EH inequality has a strict
reserve at that attained state. The H=D alternative is an explicit
geometric state for the global anchor-order theorem, never an assumed
local impossibility.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace DirectNegativeT
open AlignedNegative PrimaryCap

structure FullCoupledStop {q t : ℝ} {D T B : SignedPoint}
    (I : Source q t D T B) (kind : FullE.ArcKind) (E H : SignedPoint) (e : ℝ) (j : Fin 4) where
  angle : ℝ
  angle_mem : angle∈Ico 0 t
  tangent_mem : coupledTangent D.circle (B.a-1/2) angle∈Icc 0 (-E.y)
  tangent_positive : 0<coupledTangent D.circle (B.a-1/2) angle
  error_mem : e+angle∈Icc 0 (11/50 : ℝ)
  terminal : quarterFeasible (point (B.a-1/2) angle) B.reflect (-angle) 0 ∨ e+angle=0
  mixed_strict : 0<fullCoupledSlack kind q D.circle (B.a-1/2) e H j angle

theorem Source.full_coupled_stop {q t e : ℝ} {D T B E H : SignedPoint}
    {kind : FullE.ArcKind} (I : Source q t D T B) (J : FullE.ArcSource q E kind)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHc : H.Contained q)
    (he : e+t∈Ioc 0 (11/50 : ℝ))
    (jDE jEH : Fin 4) (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E 0 jDE) (hEH : quarterFeasible E H (e+t) jEH) :
    Nonempty (FullCoupledStop I kind E H e jEH) := by
  obtain ⟨O⟩ := I.first_hard hqU
  let P := B.a-1/2
  let r := max O.angle (-e)
  let b : ℝ → ℝ := coupledTangent D.circle P
  let L : ℝ → ℝ := fullCoupledSlack kind q D.circle P e H jEH
  let F : ℝ → ℝ := fun x => L x-(t-x)/500
  let dF : ℝ → ℝ := fun x => fullCoupledDerivative kind q D.circle P e H jEH x+1/500
  have hrO : O.angle≤r := le_max_left _ _
  have hre : -e≤r := le_max_right _ _
  have hr0 : 0≤r := O.angle_mem.1.trans hrO
  have hrt : r<t := max_lt_iff.mpr ⟨O.angle_mem.2,by linarith [he.1]⟩
  have heX (x : ℝ) (hx : x∈Icc r t) : e+x∈Icc 0 (11/50 : ℝ) := by
    constructor <;> linarith [hx.1,hx.2,he.2]
  have hDEraw : 1≤D.a-E.y := by
    rcases hjDE with rfl | rfl <;>
      simpa [quarterFeasible,quarterProjection,edgeWidth_zero] using hDE
  have hbupper {x : ℝ} (hx : x∈Icc r t) : b x≤ -E.y := by
    have hh := (I.path_geometry hqU ⟨hr0.trans hx.1,hx.2⟩).2.2.1
    rw [SignedPoint.reflect_circle] at hh
    change D.a≤(movingAnchor D.circle P x).a at hh
    dsimp [b,coupledTangent]
    linarith
  have hbpositive {x : ℝ} (hx : x∈Icc r t) : 0<b x := by
    have hOx : O.angle≤x := hrO.trans hx.1
    rcases eq_or_lt_of_le hOx with heq | hlt
    · have hcut := (O.high_anchor hqU).2.2
      have hh : (movingAnchor D.circle P O.angle).a<1 := by
        rw [SignedPoint.reflect_circle] at hcut; exact hcut
      rw [← heq]
      dsimp [b,coupledTangent]
      linarith
    · have hnot := O.later_unavailable ⟨hlt,hx.2⟩
      have hcut := ((I.atAngle hqU ⟨O.angle_mem.1.trans_lt hlt,hx.2⟩ hnot).cuts hqU).2.2.2.2.1
      have hh : (movingAnchor D.circle P x).a<1 := by
        rw [SignedPoint.reflect_circle] at hcut; exact hcut
      dsimp [b,coupledTangent]
      linarith
  have hbmem {x : ℝ} (hx : x∈Icc r t) : b x∈Icc 0 (-E.y) :=
    ⟨(hbpositive hx).le,hbupper hx⟩
  have hterminal : quarterFeasible (point P r) B.reflect (-r) 0 ∨ e+r=0 := by
    rcases le_total O.angle (-e) with hle | hle
    · right
      dsimp [r]
      rw [max_eq_right hle]
      ring
    · left
      simpa [r,max_eq_left hle,P,SignedPoint.reflect] using O.hard
  have hderiv (x : ℝ) (hx : x∈Icc r t) : HasDerivAt F (dF x) x := by
    have hx0 : 0≤x := hr0.trans hx.1
    have hc : Real.cos x≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hx0]; exact hx.2.trans I.tilt_cap)).ne'
    have hg := I.path_geometry hqU ⟨hx0,hx.2⟩
    have hL := fullCoupled_hasDerivAt (e := e) (H := H) J hqL (hbmem hx) hc
      (by have h6 := hg.2.2.2.2.2.2; rw [SignedPoint.reflect_circle] at h6; exact h6) jEH
    exact (hL.sub (((hasDerivAt_id x).const_sub t).div_const 500)).congr_deriv
      (by dsimp only [dF]; ring)
  have hcont : ContinuousOn F (Icc r t) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hFt : 0≤F t := by
    have hm := J.mixed_projection_mono (H := H) hqL (hbmem ⟨hrt.le,le_rfl⟩)
      ⟨he.1.le,by linarith [he.2]⟩ jEH hjEH
    have hf : quarterFeasible (kind.point q (b t)) H (e+t) jEH := hEH.trans hm
    have hLstart : 0≤L t := by
      dsimp [L]
      rw [fullCoupledSlack_actual kind H jEH hjEH ⟨he.1.le,by linarith [he.2]⟩]
      exact sub_nonneg.mpr hf
    simpa [F] using hLstart
  have hbarrier : 0≤F r := left_sublevel_barrier hrt hcont
    (fun x hx => hderiv x (Ioo_subset_Icc_self hx))
    (fun x hx _ => by
      have hnot := O.later_unavailable ⟨hrO.trans_lt hx.1,hx.2.le⟩
      have hh := I.full_coupled_derivative_negative J hqL hqU hHs hHcore hHc
        ⟨hr0.trans_lt hx.1,hx.2.le⟩ hnot (hbmem (Ioo_subset_Icc_self hx))
        (heX x (Ioo_subset_Icc_self hx)) jEH hjEH
      dsimp [dF,P]
      linarith) hFt
  have hstrict : 0<L r := by
    have hgrowth : 0<(t-r)/500 := div_pos (sub_pos.mpr hrt) (by norm_num)
    dsimp [F] at hbarrier
    linarith
  exact ⟨{
    angle := r
    angle_mem := ⟨hr0,hrt⟩
    tangent_mem := hbmem ⟨le_rfl,hrt.le⟩
    tangent_positive := hbpositive ⟨le_rfl,hrt.le⟩
    error_mem := heX r ⟨le_rfl,hrt.le⟩
    terminal := hterminal
    mixed_strict := hstrict }⟩


end DirectNegativeT
end SquaresInCircles.Eight.TableFree
