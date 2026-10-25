module

public import Mathlib.Topology.Instances.Real.Lemmas
public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: the relaxation of E and its active mixed contacts

The relaxation `Feasible h d α q` contains the point E of the cycle, with the primaries `h`, `d` of
H and D and the total frame span `α` fixed, and the circle `q` of the cycle as its ceiling. Its
feasible set is compact (`feasibleSet_isCompact`), so the corner circle has a minimum
(`exists_minimum`). Inward moves with positive steps chosen from the slacks show that at an
interior minimum both mixed contacts are active: with DE slack the tangent decreases
(`lower_tangent`), and with EH slack alone E slides along DE (`slide_DE`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EInteriorGeometry

abbrev State := ℝ×ℝ×ℝ

def W (x : ℝ) : ℝ := (1+Real.cos x+Real.sin x)/2
def corner (P : State) : ℝ := (P.1+1/2)^2+(P.2.1+1/2)^2
def deValue (d : ℝ) (P : State) : ℝ :=
  d+P.1*Real.sin P.2.2+P.2.1*Real.cos P.2.2
def ehValue (h α : ℝ) (P : State) : ℝ :=
  h+P.1*Real.sin (α-P.2.2)-P.2.1*Real.cos (α-P.2.2)
def deSlack (d : ℝ) (P : State) : ℝ := deValue d P-W P.2.2
def ehSlack (h α : ℝ) (P : State) : ℝ := ehValue h α P-W (α-P.2.2)

structure Feasible (h d α q : ℝ) (P : State) : Prop where
  b_nonneg : 0≤P.2.1
  sorted : P.2.1≤P.1
  angle : P.2.2∈Icc 0 α
  circle : corner P≤q
  DE : W P.2.2≤deValue d P
  EH : W (α-P.2.2)≤ehValue h α P

def feasibleSet (h d α q : ℝ) : Set State := {P | Feasible h d α q P}

theorem feasible_iff (h d α q : ℝ) (P : State) :
    Feasible h d α q P ↔
      0≤P.2.1 ∧ P.2.1≤P.1 ∧ 0≤P.2.2 ∧ P.2.2≤α ∧
      corner P≤q ∧ W P.2.2≤deValue d P ∧ W (α-P.2.2)≤ehValue h α P := by
  constructor
  · intro hp
    exact ⟨hp.b_nonneg,hp.sorted,hp.angle.1,hp.angle.2,hp.circle,hp.DE,hp.EH⟩
  · rintro ⟨hb,ha,hd0,hda,hq,hde,heh⟩
    exact ⟨hb,ha,⟨hd0,hda⟩,hq,hde,heh⟩

theorem corner_coordinates {h d α q : ℝ} {P : State}
    (hq : q≤qCap) (hp : Feasible h d α q P) :
    0≤P.1 ∧ P.1<283/200 ∧ P.2.1<9/10 := by
  have ha : 0≤P.1 := hp.b_nonneg.trans hp.sorted
  have hc : (P.1+1/2)^2+(P.2.1+1/2)^2≤qCap := hp.circle.trans hq
  have hminor := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2)
    (show 1/2≤P.2.1+1/2 by linarith [hp.b_nonneg]) 2
  have hprimary : P.1<283/200 := by
    by_contra! hbad
    have hmajor := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤383/200)
      (show 383/200≤P.1+1/2 by linarith) 2
    dsimp [qCap] at hc
    nlinarith
  have htangent : P.2.1<9/10 := by
    by_contra! hbad
    have hmajor := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7/5)
      (show 7/5≤P.1+1/2 by linarith [hp.sorted]) 2
    have hminor' := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7/5)
      (show 7/5≤P.2.1+1/2 by linarith) 2
    dsimp [qCap] at hc
    nlinarith
  exact ⟨ha,hprimary,htangent⟩

theorem short_sine {α : ℝ} (hα : α∈Icc 0 (11/50 : ℝ)) :
    (99/100)*α≤Real.sin α := by
  have hs := Real.sin_ge_sub_cube hα.1
  have hsquare := pow_le_pow_left₀ hα.1 hα.2 2
  have hcube := mul_le_mul_of_nonneg_right hsquare hα.1
  linarith [hα.1]

/-- For `α ≤ 11/50`, every feasible point of the relaxation, also one without a core-avoidance
condition, has primary coordinate above `21/20`; a coarse Taylor estimate leaves a strict
reserve. -/
theorem primary_lower {h d α q : ℝ} {P : State}
    (hq : q≤qCap) (hα : α∈Icc 0 (11/50 : ℝ))
    (hsum : h+d<1248/625-(359/500)*Real.sin α)
    (hp : Feasible h d α q P) : 21/20<P.1 := by
  have hb := (corner_coordinates hq hp).2.2
  have hu : P.2.2∈Icc 0 (7/10 : ℝ) :=
    ⟨hp.angle.1,by linarith [hp.angle.2,hα.2]⟩
  have hv : α-P.2.2∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith [hp.angle.2],by linarith [hp.angle.1,hα.2]⟩
  have hsu := (transport_trig hu).2.2.1
  have hsv := (transport_trig hv).2.2.1
  have hT : Real.sin P.2.2+Real.sin (α-P.2.2)≤α := by
    linarith [Real.sin_le hu.1,Real.sin_le hv.1]
  have hbu := mul_nonneg hp.b_nonneg
    (sub_nonneg.mpr (Real.cos_le_one P.2.2))
  have hbv := mul_nonneg (show 0≤9/10-P.2.1 by linarith)
    (sub_nonneg.mpr (Real.cos_le_one (α-P.2.2)))
  have hB : P.2.1*(Real.cos P.2.2-Real.cos (α-P.2.2))≤
      (9/10)*(1-Real.cos (α-P.2.2)) := by linarith
  have hcu := Real.one_sub_sq_div_two_le_cos (x := P.2.2)
  have hcv := Real.one_sub_sq_div_two_le_cos (x := α-P.2.2)
  have hcross := mul_nonneg hu.1 hv.1
  have hsquares : P.2.2^2+(α-P.2.2)^2≤α^2 := by linarith
  have hquadratic := mul_nonneg hα.1 (show 0≤11/50-α by linarith [hα.2])
  have hsin := short_sine hα
  by_contra! hbad
  have haT := mul_le_mul_of_nonneg_right hbad (add_nonneg hsu hsv)
  have hDE := hp.DE
  have hEH := hp.EH
  dsimp [W,deValue,ehValue] at hDE hEH
  linarith [sq_nonneg P.2.2,hα.1,hα.2]

theorem strict_sorting {h d α q : ℝ} {P : State}
    (hq : q≤qCap) (hα : α∈Icc 0 (11/50 : ℝ))
    (hsum : h+d<1248/625-(359/500)*Real.sin α)
    (hp : Feasible h d α q P) : P.2.1<P.1 := by
  have ha := primary_lower hq hα hsum hp
  have hb := (corner_coordinates hq hp).2.2
  linarith

/-- For the larger span `α ≤ 27/100` allowed by the negative outer composites the primary
coordinate still exceeds `51/50`, which keeps every relaxed E point strictly off its diagonal and
off the core. -/
theorem primary_lower_wide {h d α q : ℝ} {P : State}
    (hq : q≤qCap) (hα : α∈Icc 0 (27/100 : ℝ))
    (hsum : h+d<1248/625-(359/500)*Real.sin α)
    (hp : Feasible h d α q P) : 51/50<P.1 := by
  have hb := (corner_coordinates hq hp).2.2
  have hu : P.2.2∈Icc 0 (7/10 : ℝ) :=
    ⟨hp.angle.1,by linarith [hp.angle.2,hα.2]⟩
  have hv : α-P.2.2∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith [hp.angle.2],by linarith [hp.angle.1,hα.2]⟩
  have hsu := (transport_trig hu).2.2.1
  have hsv := (transport_trig hv).2.2.1
  have hT : Real.sin P.2.2+Real.sin (α-P.2.2)≤α := by
    linarith [Real.sin_le hu.1,Real.sin_le hv.1]
  have hbu := mul_nonneg hp.b_nonneg
    (sub_nonneg.mpr (Real.cos_le_one P.2.2))
  have hbv := mul_nonneg (show 0≤9/10-P.2.1 by linarith)
    (sub_nonneg.mpr (Real.cos_le_one (α-P.2.2)))
  have hB : P.2.1*(Real.cos P.2.2-Real.cos (α-P.2.2))≤
      (9/10)*(1-Real.cos (α-P.2.2)) := by linarith
  have hcu := Real.one_sub_sq_div_two_le_cos (x := P.2.2)
  have hcv := Real.one_sub_sq_div_two_le_cos (x := α-P.2.2)
  have hcross := mul_nonneg hu.1 hv.1
  have hsquares : P.2.2^2+(α-P.2.2)^2≤α^2 := by linarith
  have hquadratic := mul_nonneg hα.1 (show 0≤27/100-α by linarith [hα.2])
  have hsin : (49/50)*α≤Real.sin α := by
    have hs := Real.sin_ge_sub_cube hα.1
    have hsquare := pow_le_pow_left₀ hα.1 hα.2 2
    have hcube := mul_le_mul_of_nonneg_right hsquare hα.1
    linarith [hα.1]
  by_contra! hbad
  have haT := mul_le_mul_of_nonneg_right hbad (add_nonneg hsu hsv)
  have hDE := hp.DE
  have hEH := hp.EH
  dsimp [W,deValue,ehValue] at hDE hEH
  linarith [sq_nonneg P.2.2,hα.1,hα.2]

theorem strict_sorting_wide {h d α q : ℝ} {P : State}
    (hq : q≤qCap) (hα : α∈Icc 0 (27/100 : ℝ))
    (hsum : h+d<1248/625-(359/500)*Real.sin α)
    (hp : Feasible h d α q P) : P.2.1<P.1 := by
  have ha := primary_lower_wide hq hα hsum hp
  have hb := (corner_coordinates hq hp).2.2
  linarith

theorem span_pos {h d α q : ℝ} {P : State}
    (hα : 0≤α) (hsum : h+d<1248/625-(359/500)*Real.sin α)
    (hp : Feasible h d α q P) : 0<α := by
  rcases lt_or_eq_of_le hα with hpos | heq
  · exact hpos
  · have ha0 : α=0 := heq.symm
    have hp0 : P.2.2=0 := by linarith [hp.angle.1,hp.angle.2]
    have hd := hp.DE
    have hh := hp.EH
    simp [W,deValue,ehValue,ha0,hp0] at hd hh
    simp [ha0] at hsum
    linarith

theorem feasibleSet_isClosed (h d α q : ℝ) : IsClosed (feasibleSet h d α q) := by
  have h1 : IsClosed {P : State | 0≤P.2.1} := isClosed_le continuous_const (by fun_prop)
  have h2 : IsClosed {P : State | P.2.1≤P.1} := isClosed_le (by fun_prop) (by fun_prop)
  have h3 : IsClosed {P : State | 0≤P.2.2} := isClosed_le continuous_const (by fun_prop)
  have h4 : IsClosed {P : State | P.2.2≤α} := isClosed_le (by fun_prop) continuous_const
  have h5 : IsClosed {P : State | corner P≤q} :=
    isClosed_le (by unfold corner; fun_prop) continuous_const
  have h6 : IsClosed {P : State | W P.2.2≤deValue d P} :=
    isClosed_le (by unfold W; fun_prop) (by unfold deValue; fun_prop)
  have h7 : IsClosed {P : State | W (α-P.2.2)≤ehValue h α P} :=
    isClosed_le (by unfold W; fun_prop) (by unfold ehValue; fun_prop)
  simpa only [feasibleSet,feasible_iff,ofPred_and] using
    h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter h7)))))

theorem feasibleSet_isCompact {h d α q : ℝ} (hq : q≤qCap) :
    IsCompact (feasibleSet h d α q) := by
  have hbox : IsCompact ((Icc (0:ℝ) 2) ×ˢ ((Icc (0:ℝ) 2) ×ˢ Icc 0 α)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  apply hbox.of_isClosed_subset (feasibleSet_isClosed h d α q)
  intro P hp
  have hb := corner_coordinates hq hp
  exact ⟨⟨hb.1,by linarith [hb.2.1]⟩,
    ⟨⟨hp.b_nonneg,by linarith [hb.2.2]⟩,hp.angle⟩⟩

theorem exists_minimum {h d α q : ℝ} (hq : q≤qCap)
    (hne : (feasibleSet h d α q).Nonempty) :
    ∃P, Feasible h d α q P ∧ IsMinOn corner (feasibleSet h d α q) P := by
  obtain ⟨P,hp,hmin⟩ := (feasibleSet_isCompact hq).exists_isMinOn hne
    (show ContinuousOn corner (feasibleSet h d α q) by unfold corner; fun_prop)
  exact ⟨P,hp,hmin⟩

/-- When DE has slack and the tangent is positive, decreasing the tangent gives a feasible point
with a strictly smaller corner circle; EH improves. -/
theorem lower_tangent {h d α q : ℝ} {P : State}
    (hα : α≤7/10) (hp : Feasible h d α q P)
    (hb : 0<P.2.1) (hde : 0<deSlack d P) :
    ∃Q, Feasible h d α q Q ∧ corner Q<corner P := by
  let e := min (P.2.1/2) (deSlack d P/2)
  have he : 0<e := lt_min (by linarith) (by linarith)
  have heb : e≤P.2.1/2 := min_le_left _ _
  have hed : e≤deSlack d P/2 := min_le_right _ _
  let Q : State := (P.1,P.2.1-e,P.2.2)
  have hu : P.2.2∈Icc 0 (7/10 : ℝ) := ⟨hp.angle.1,hp.angle.2.trans hα⟩
  have hv : α-P.2.2∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith [hp.angle.2],by linarith [hp.angle.1]⟩
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one P.2.2) he.le
  have hcv : 0≤Real.cos (α-P.2.2) := by linarith [(transport_trig hv).1]
  have hgain := mul_nonneg he.le hcv
  have hdec : corner Q<corner P := by
    have hpos := mul_pos he (show 0<2*P.2.1+1-e by linarith)
    dsimp [corner,Q]
    linarith
  refine ⟨Q,?_,hdec⟩
  refine {
    b_nonneg := by dsimp [Q]; linarith
    sorted := by dsimp [Q]; linarith [hp.sorted]
    angle := hp.angle
    circle := hdec.le.trans hp.circle
    DE := ?_
    EH := ?_ }
  · dsimp [Q,deValue]
    dsimp [deSlack,deValue] at hed hde
    linarith
  · have hh := hp.EH
    dsimp [Q,ehValue] at hh ⊢
    linarith

/-- When EH has slack and sorting is strict, a step along the tangent direction of DE, bounded by
the sorting margin, the EH slack and the radial descent, gives a feasible point with a strictly
smaller corner circle. -/
theorem slide_DE {h d α q : ℝ} {P : State}
    (hα : α≤7/10) (hp : Feasible h d α q P)
    (hsort : P.2.1<P.1) (heh : 0<ehSlack h α P) :
    ∃Q, Feasible h d α q Q ∧ corner Q<corner P := by
  have hu : P.2.2∈Icc 0 (7/10 : ℝ) := ⟨hp.angle.1,hp.angle.2.trans hα⟩
  have hv : α-P.2.2∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith [hp.angle.2],by linarith [hp.angle.1]⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hu
  let r := (P.1+1/2)*Real.cos P.2.2-(P.2.1+1/2)*Real.sin P.2.2
  have hr : 0<r := by
    have hfirst := mul_pos (sub_pos.mpr hsort) (show 0<Real.cos P.2.2 by linarith)
    have hsecond := mul_pos (show 0<P.2.1+1/2 by linarith [hp.b_nonneg])
      (sub_pos.mpr hsc)
    dsimp [r]
    nlinarith
  let e := min ((P.1-P.2.1)/4) (min (ehSlack h α P/2) r)
  have he : 0<e := lt_min (by linarith)
    (lt_min (by linarith) hr)
  have hes : e≤(P.1-P.2.1)/4 := min_le_left _ _
  have heh' : e≤ehSlack h α P/2 := (min_le_right _ _).trans (min_le_left _ _)
  have her : e≤r := (min_le_right _ _).trans (min_le_right _ _)
  let Q : State := (P.1-e*Real.cos P.2.2,P.2.1+e*Real.sin P.2.2,P.2.2)
  have hsinprod := mul_nonneg he.le hs0
  have hcosprod := mul_le_mul_of_nonneg_left hc1 he.le
  have hsinupper := mul_le_mul_of_nonneg_left (Real.sin_le_one P.2.2) he.le
  have hdec : corner Q<corner P := by
    have hprod := mul_pos he hr
    have hsquare := mul_le_mul_of_nonneg_left her he.le
    have hcircle := Real.sin_sq_add_cos_sq P.2.2
    have hid : corner Q=corner P-2*e*r+e^2 := by
      dsimp [corner,Q,r]
      linear_combination e^2*hcircle
    rw [hid]
    nlinarith
  refine ⟨Q,?_,hdec⟩
  refine {
    b_nonneg := by dsimp [Q]; linarith [hp.b_nonneg]
    sorted := by dsimp [Q]; linarith
    angle := hp.angle
    circle := hdec.le.trans hp.circle
    DE := ?_
    EH := ?_ }
  · have hid : deValue d Q=deValue d P := by dsimp [deValue,Q]; ring
    rw [hid]
    exact hp.DE
  · have hid : ehValue h α Q=ehValue h α P-e*Real.sin α := by
      have hsum : P.2.2+(α-P.2.2)=α := by ring
      have hsin := Real.sin_add P.2.2 (α-P.2.2)
      rw [hsum] at hsin
      dsimp [ehValue,Q]
      nlinarith
    have hrate := mul_le_mul_of_nonneg_left (Real.sin_le_one α) he.le
    change W (α-P.2.2)≤ehValue h α Q
    rw [hid]
    dsimp [ehSlack] at heh'
    linarith

end SquaresInCircles.Eight.EInteriorGeometry
