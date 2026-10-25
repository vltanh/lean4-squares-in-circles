module

public import SquaresInCircles.Eight.Owners.BelowERotatedCycle
public import SquaresInCircles.Eight.Owners.Hard.ZeroEReflection
public import SquaresInCircles.Eight.Owners.Nonpositive.DE2ContactRate
public import SquaresInCircles.Eight.Owners.Nonpositive.DE2PrimaryBound

/-!
# Eight squares: the original rotated DE2 source reaches E=D on its own circle

The source tangent first decreases to the
actual DE2 contact, improving EH.  The entire contact segment then has
the proved negative EH derivative.  Any earlier zero-tangent endpoint
is inserted into the actual same-q hard cycle and excluded.  Thus the
endpoint is E=D, on exactly the original E circle, with strict EH slack.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate NonpositiveDE2Contact

theorem HardInput.nonpositive_below_rotated_state {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hED : I.cycle.theta E<I.cycle.theta D) (hDE2 : I.cycle.Feasible D 2) :
    ∃P : EInteriorGeometry.State,
      EInteriorGeometry.Feasible (I.cycle.point H).a (I.cycle.point D).a
        (I.cycle.theta H-I.cycle.theta D) q P ∧
      P.2.2=0 ∧ EInteriorGeometry.corner P=(I.cycle.point E).circle ∧
      P.2.1∈Ioc 0 (-(I.cycle.point E).y) ∧
      EInteriorGeometry.W P.2.2=EInteriorGeometry.deValue (I.cycle.point D).a P ∧
      EInteriorGeometry.W (I.cycle.theta H-I.cycle.theta D-P.2.2)<
        EInteriorGeometry.ehValue (I.cycle.point H).a (I.cycle.theta H-I.cycle.theta D) P := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  have hrad := I.nonpositive_E_radial hcap hAB hAG hGH hDT hTB hHG hTD
  have hEa := I.nonpositive_below_DE2_primary hcap hAB hAG hGH hDT hTB hHG hTD hED hDE2
  have hEc : (I.cycle.point E).circle≤qCap := (I.necessary.contained E).trans hcap
  have hDa : (353/500:ℝ)<(I.cycle.point D).a := by
    have hs : -(I.cycle.point D).y≤(I.cycle.point D).a := by
      simpa [abs_of_nonpos I.anchors_normal.D_nonpos] using (I.necessary.sorted D).2
    exact hb.D_tangent.1.trans_le hs
  have hDy : -(I.cycle.point D).y∈Ioo (353/500:ℝ) (9/10) := hb.D_tangent
  let α := I.cycle.theta H-I.cycle.theta D
  let x := I.cycle.theta D-I.cycle.theta E
  have hα : α∈Icc 0 (27/100:ℝ) := ⟨hb.span_nonneg,hb.span_lt.le⟩
  have hxpos : 0<x := sub_pos.mpr hED
  have hx : x∈Icc 0 (7/10:ℝ) :=
    ⟨hxpos.le,(le_abs_self _).trans (I.necessary.spread D E)⟩
  have hsum : α+x≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread H E)
    dsimp [α,x,frameCap] at *
    linarith
  have hp : α+x∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.1],hsum⟩
  have hEHorder : I.cycle.theta E≤I.cycle.theta H :=
    hED.le.trans (sub_nonneg.mp hb.span_nonneg)
  have hEH1 := I.nonpositive_EH_primary_of_nonneg hcap hAB hAG hGH hDT hTB hHG hTD hEHorder
  have hDEraw : quarterFeasible (I.cycle.point D) (I.cycle.point E) (-x) 2 := by
    have heq : -x=I.cycle.theta E-I.cycle.theta D := by dsimp [x]; ring
    simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg,heq] using hDE2
  have hEHraw : quarterFeasible (I.cycle.point E) (I.cycle.point H) (α+x) 1 := by
    have heq : α+x=I.cycle.theta H-I.cycle.theta E := by dsimp [α,x]; ring
    simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg,heq] using hEH1
  have hsource_DE : b (I.cycle.point D) x≤ -(I.cycle.point E).y := by
    have hh : 0≤quarterProjection (I.cycle.point D)
        (OriginalECircle.point (I.cycle.point E) (-(I.cycle.point E).y)) (-x) 2-edgeWidth (-x) := by
      rw [OriginalECircle.initial (I.necessary.sorted E) I.E_nonpos]
      exact sub_nonneg.mpr hDEraw
    rw [DE2_slack _ _ _ hx] at hh
    linarith
  have hsource_EH : 0≤OriginalECircle.eh (I.cycle.point E) (I.cycle.point H)
      (α+x) (-(I.cycle.point E).y) := by
    rw [OriginalECircle.eh_actual _ _ _ hp,
      OriginalECircle.initial (I.necessary.sorted E) I.E_nonpos]
    exact sub_nonneg.mpr hEHraw
  /- Every floor state is an actual necessary cycle at the same q. -/
  have positive_tangent (z y : ℝ) (hz : z∈Icc 0 x)
      (hy : y∈Icc 0 (-(I.cycle.point E).y))
      (hcontact : b (I.cycle.point D) z≤y)
      (hEH : 0≤OriginalECircle.eh (I.cycle.point E) (I.cycle.point H) (α+z) y) : 0<y := by
    have hzrange : z∈Icc 0 (7/10:ℝ) := ⟨hz.1,hz.2.trans hx.2⟩
    have hprange : α+z∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.1,hz.1],by linarith [hz.2]⟩
    have hgeom := OriginalECircle.geometry (I.necessary.sorted E) I.E_nonpos hrad.1 hy
    let p := OriginalECircle.point (I.cycle.point E) y
    let θ := I.cycle.theta D-z
    have hpq : p.Contained q := hgeom.2.2.1.trans_le (I.necessary.contained E)
    have hpnegative : p.y≤0 := neg_nonpos.mpr hy.1
    have hprad : max |(I.cycle.point H).y| |(I.cycle.point D).y|≤p.a :=
      hrad.2.trans hgeom.2.2.2
    have hθ : θ∈Icc (I.cycle.theta E) (I.cycle.theta D) := by
      have hzu : z≤I.cycle.theta D-I.cycle.theta E := hz.2
      dsimp [θ]
      constructor <;> linarith [hz.1]
    have hDEactual : quarterFeasible (I.cycle.point D) p (θ-I.cycle.theta D) 2 := by
      have heq : θ-I.cycle.theta D= -z := by dsimp [θ]; ring
      rw [heq]
      apply sub_nonneg.mp
      rw [show p=OriginalECircle.point (I.cycle.point E) y from rfl,DE2_slack _ _ _ hzrange]
      exact sub_nonneg.mpr hcontact
    have hEHactual : quarterFeasible p (I.cycle.point H) (I.cycle.theta H-θ) 1 := by
      have heq : I.cycle.theta H-θ=α+z := by dsimp [θ,α]; ring
      rw [heq]
      have hh := hEH
      rw [OriginalECircle.eh_actual _ _ _ hprange] at hh
      exact sub_nonneg.mp hh
    let J := I.fromBelowERotated hgeom.1 hpq hgeom.2.1 hpnegative hprad hθ hDEactual hEHactual
    have hfixed (i : Vertex) (hi : i≠E) :
        J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i :=
      belowEPrimaryCycle_unchanged I.cycle p θ i hi
    have hH := hfixed H (by decide)
    have hG := hfixed G (by decide)
    have hA := hfixed A (by decide)
    have hB := hfixed B (by decide)
    have hT := hfixed T (by decide)
    have hD := hfixed D (by decide)
    have hJHG : J.cycle.Feasible H 0 :=
      (replacePoint_other_feasible (v := E) (by decide : H≠E) (by decide : next H≠E)).2 hHG
    have hJTD : J.cycle.Feasible T 2 :=
      (replacePoint_other_feasible (v := E) (by decide : T≠E) (by decide : next T≠E)).2 hTD
    have hJnegative := J.nonpositive_E_strict_negative hqL hq
      (by rw [hA.2,hB.2]; exact hAB)
      (by rw [hA.1,hB.1]; exact hnorm)
      (by rw [hA.2,hG.2]; exact hAG)
      (by rw [hG.2,hH.2]; exact hGH)
      (by rw [hD.2,hT.2]; exact hDT)
      (by rw [hT.2,hB.2]; exact hTB) hJHG hJTD
    change -y<0 at hJnegative
    linarith
  let y₀ := max 0 (b (I.cycle.point D) x)
  have hy₀ : y₀∈Icc 0 (-(I.cycle.point E).y) :=
    ⟨le_max_left _ _,max_le (neg_nonneg.mpr I.E_nonpos) hsource_DE⟩
  have hcontact₀ : b (I.cycle.point D) x≤y₀ := le_max_right _ _
  have hEH₀ : 0≤OriginalECircle.eh (I.cycle.point E) (I.cycle.point H) (α+x) y₀ :=
    hsource_EH.trans (eh_tangent_antitone _ _ hp hy₀.1 hy₀.2)
  have hy₀positive := positive_tangent x y₀ ⟨hx.1,le_rfl⟩ hy₀ hcontact₀ hEH₀
  have hbx : 0<b (I.cycle.point D) x := by
    by_contra! hbad
    have hh : y₀=0 := max_eq_left hbad
    linarith
  have hy₀eq : y₀=b (I.cycle.point D) x := max_eq_right hbx.le
  have hJx_nonneg : 0≤J (I.cycle.point E) (I.cycle.point D) (I.cycle.point H) α x := by
    simpa only [J,hy₀eq] using hEH₀
  have hbzero : 0<b (I.cycle.point D) 0 := by
    by_contra! hbad
    have hcontinuous : Continuous (b (I.cycle.point D)) :=
      continuous_iff_continuousAt.2 fun z => (b_derivative _ z).continuousAt
    have himage : 0∈b (I.cycle.point D) '' Icc 0 x := by
      apply intermediate_value_Icc hxpos.le hcontinuous.continuousOn
      exact ⟨hbad,hbx.le⟩
    obtain ⟨z,hz,hbz⟩ := himage
    have hJgrow := J_reverse_growth (H := I.cycle.point H)
      (I.necessary.sorted E) I.E_nonpos hEa hEc hDa hDy hα
      hz.1 hz.2 hx.2 hsum (by rw [hbz]) hsource_DE
    have hJz : 0≤J (I.cycle.point E) (I.cycle.point D) (I.cycle.point H) α z := by
      linarith [hz.2]
    have hzero : 0<(0:ℝ) := positive_tangent z 0 hz
      ⟨le_rfl,neg_nonneg.mpr I.E_nonpos⟩ (by rw [hbz])
      (by simpa only [J,hbz] using hJz)
    exact (lt_irrefl (0:ℝ)) hzero
  have hmon := b_monotone hb.D_primary.1.le hDy.1
  have hbupper : b (I.cycle.point D) 0≤ -(I.cycle.point E).y :=
    (hmon (by norm_num) hx hx.1).trans hsource_DE
  have hJgrow := J_reverse_growth (H := I.cycle.point H)
    (I.necessary.sorted E) I.E_nonpos hEa hEc hDa hDy hα
    (le_rfl : (0:ℝ)≤0) hx.1 hx.2 hsum hbzero.le hsource_DE
  have hJzero : 0<J (I.cycle.point E) (I.cycle.point D) (I.cycle.point H) α 0 := by
    linarith
  let P : EInteriorGeometry.State :=
    (OriginalECircle.primary (I.cycle.point E) (b (I.cycle.point D) 0),b (I.cycle.point D) 0,0)
  have hgeom := OriginalECircle.geometry (I.necessary.sorted E) I.E_nonpos hrad.1
    ⟨hbzero.le,hbupper⟩
  have hPcircle : EInteriorGeometry.corner P=(I.cycle.point E).circle := by
    simpa [P,EInteriorGeometry.corner,OriginalECircle.point,SignedPoint.circle,
      abs_neg,abs_of_nonneg hbzero.le,-b_zero] using hgeom.2.2.1
  have hPDE : EInteriorGeometry.W P.2.2=EInteriorGeometry.deValue (I.cycle.point D).a P := by
    simp [P,EInteriorGeometry.W,EInteriorGeometry.deValue]
  have hPEH : EInteriorGeometry.W (α-P.2.2)<EInteriorGeometry.ehValue (I.cycle.point H).a α P := by
    dsimp [J,OriginalECircle.eh] at hJzero
    dsimp [P,EInteriorGeometry.W,EInteriorGeometry.ehValue]
    simp only [add_zero,sub_zero] at *
    linarith
  refine ⟨P,?_,rfl,hPcircle,⟨hbzero,hbupper⟩,hPDE,hPEH⟩
  exact {
    b_nonneg := hbzero.le
    sorted := by
      simpa [P,OriginalECircle.point,abs_neg,abs_of_nonneg hbzero.le,-b_zero] using hgeom.1.2
    angle := ⟨le_rfl,hα.1⟩
    circle := hPcircle.trans_le (I.necessary.contained E)
    DE := hPDE.le
    EH := hPEH.le }

end SquaresInCircles.Eight.SignedCycle
