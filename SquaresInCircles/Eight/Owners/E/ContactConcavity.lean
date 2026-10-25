module

public import Mathlib.Topology.Instances.Real.Lemmas
public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: strict concavity of the E contact energy

The large cotangent terms of the second derivative cancel before any estimate
(`cotangent_cancellation`). One factorization controls the whole orientation interval up to the
total span `27/100` (`scaled_second_negative`), so the energy is strictly concave and every
subinterval has an endpoint of smaller energy than its interior points (`endpoint_improves`).
-/

section
/-!
## The relaxation of E and its active mixed contacts

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
end
end
end

section
/-!
## The two-contact curve of E

The curve `curve m n α z` solves the two mixed contacts DE and EH (`curve_contacts`), and it is
their only solution (`contact_unique`). Its energy is exactly the corner polynomial
(`corner_curve`), also at small variations with negative tangent. The derivative identities come
from differentiating the first and second harmonics (`energy_hasDerivAt`, `energyD_hasDerivAt`,
`scaled_second_identity`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EContactCurve
open EInteriorGeometry

def A (α : ℝ) : ℝ := Real.cos (α/2)/(2*Real.sin (α/2))
def B (α : ℝ) : ℝ := Real.sin (α/2)/(2*Real.cos (α/2))
def M (m α : ℝ) : ℝ := m/(2*Real.sin (α/2))
def N (n α : ℝ) : ℝ := n/(2*Real.cos (α/2))

def U (m α z : ℝ) : ℝ := A α*Real.cos z-M m α
def V (n α z : ℝ) : ℝ := B α*Real.sin z+N n α
def x (m n α z : ℝ) : ℝ := U m α z*Real.cos z-V n α z*Real.sin z
def b (m n α z : ℝ) : ℝ := U m α z*Real.sin z+V n α z*Real.cos z
def curve (m n α z : ℝ) : State := (x m n α z+1/2,b m n α z,α/2-z)

def K0 (m n α : ℝ) : ℝ :=
  (A α^2+2*A α+B α^2-2*B α)/2+M m α^2+N n α^2+5/4
def Kc (α : ℝ) : ℝ := (A α^2+2*A α-B α^2+2*B α)/2
def Ks (α : ℝ) : ℝ := (A α+B α)/2
def Lc (m n α : ℝ) : ℝ := -2*M m α*(A α+1)+N n α
def Ls (m n α : ℝ) : ℝ := 2*N n α*(B α-1)-M m α

def energy (m n α z : ℝ) : ℝ :=
  K0 m n α+Kc α*Real.cos (2*z)+Ks α*Real.sin (2*z)+
    Lc m n α*Real.cos z+Ls m n α*Real.sin z
def energyD (m n α z : ℝ) : ℝ :=
  -2*Kc α*Real.sin (2*z)+2*Ks α*Real.cos (2*z)-
    Lc m n α*Real.sin z+Ls m n α*Real.cos z
def energyDD (m n α z : ℝ) : ℝ :=
  -4*Kc α*Real.cos (2*z)-4*Ks α*Real.sin (2*z)-
    Lc m n α*Real.cos z-Ls m n α*Real.sin z

theorem rotated_components (m n α z : ℝ) :
    x m n α z*Real.cos z+b m n α z*Real.sin z=U m α z ∧
      -x m n α z*Real.sin z+b m n α z*Real.cos z=V n α z := by
  constructor
  · dsimp [x,b]
    linear_combination U m α z*(Real.sin_sq_add_cos_sq z)
  · dsimp [x,b]
    linear_combination V n α z*(Real.sin_sq_add_cos_sq z)

theorem corner_curve (m n α z : ℝ) :
    corner (curve m n α z)=energy m n α z := by
  dsimp [corner,curve,x,b,U,V,energy,K0,Kc,Ks,Lc,Ls]
  rw [Real.sin_two_mul,Real.cos_two_mul]
  linear_combination
    ((A α*Real.cos z-M m α)^2+(B α*Real.sin z+N n α)^2+B α^2-2*B α)*
      (Real.sin_sq_add_cos_sq z)

theorem energy_hasDerivAt (m n α z : ℝ) :
    HasDerivAt (energy m n α) (energyD m n α z) z := by
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2*t)) (-2*Real.sin (2*z)) z :=
    ((hasDerivAt_id' z).const_mul 2).cos.congr_deriv (by ring)
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2*t)) (2*Real.cos (2*z)) z :=
    ((hasDerivAt_id' z).const_mul 2).sin.congr_deriv (by ring)
  have hd := ((((hasDerivAt_const z (K0 m n α)).fun_add (hc.const_mul (Kc α))).fun_add
    (hs.const_mul (Ks α))).fun_add ((Real.hasDerivAt_cos z).const_mul (Lc m n α))).fun_add
    ((Real.hasDerivAt_sin z).const_mul (Ls m n α))
  exact hd.congr_deriv (by simp only [energyD]; ring)

theorem energyD_hasDerivAt (m n α z : ℝ) :
    HasDerivAt (energyD m n α) (energyDD m n α z) z := by
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2*t)) (-2*Real.sin (2*z)) z :=
    ((hasDerivAt_id' z).const_mul 2).cos.congr_deriv (by ring)
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2*t)) (2*Real.cos (2*z)) z :=
    ((hasDerivAt_id' z).const_mul 2).sin.congr_deriv (by ring)
  have hd := (((hs.const_mul (-2*Kc α)).fun_add (hc.const_mul (2*Ks α))).fun_sub
    ((Real.hasDerivAt_sin z).const_mul (Lc m n α))).fun_add
    ((Real.hasDerivAt_cos z).const_mul (Ls m n α))
  exact hd.congr_deriv (by simp only [energyDD]; ring)

theorem half_trig {α : ℝ} (hα : α∈Ioo 0 (27/100 : ℝ)) :
    0<Real.sin (α/2) ∧ 0<Real.cos (α/2) ∧ 0<Real.sin α := by
  refine ⟨?_,?_,?_⟩
  · exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hα.1])
      (by linarith [hα.2,Real.pi_gt_three])
  · apply transport_cos_pos
    rw [abs_of_pos (by linarith [hα.1] : (0:ℝ)<α/2)]
    linarith [hα.2]
  · exact Real.sin_pos_of_pos_of_lt_pi hα.1 (by linarith [hα.2,Real.pi_gt_three])

theorem U_equation {α : ℝ} (hs : Real.sin (α/2)≠0) (m z : ℝ) :
    2*Real.sin (α/2)*U m α z=Real.cos (α/2)*Real.cos z-m := by
  dsimp [U,A,M]
  field_simp [hs]

theorem V_equation {α : ℝ} (hc : Real.cos (α/2)≠0) (n z : ℝ) :
    2*Real.cos (α/2)*V n α z=Real.sin (α/2)*Real.sin z+n := by
  dsimp [V,B,N]
  field_simp [hc]

/-- Both primary contacts, DE and EH, hold with equality along the curve. -/
theorem curve_contacts {α : ℝ} (hα : α∈Ioo 0 (27/100 : ℝ)) (m n z : ℝ) :
    deValue ((m-n+1)/2) (curve m n α z)=W (α/2-z) ∧
      ehValue ((m+n+1)/2) α (curve m n α z)=W (α/2+z) := by
  have ht := half_trig hα
  have hu := U_equation ht.1.ne' m z
  have hv := V_equation ht.2.1.ne' n z
  have hr := rotated_components m n α z
  have hrs := congrArg (fun y : ℝ => Real.sin (α/2)*y) hr.1
  have hrc := congrArg (fun y : ℝ => Real.cos (α/2)*y) hr.2
  constructor
  · dsimp [deValue,curve,W]
    rw [Real.sin_sub,Real.cos_sub]
    nlinarith
  · have heq : α-(α/2-z)=α/2+z := by ring
    dsimp [ehValue,curve]
    rw [heq]
    dsimp [W]
    rw [Real.sin_add,Real.cos_add]
    nlinarith

theorem contact_unique {α m n a β z : ℝ}
    (hα : α∈Ioo 0 (27/100 : ℝ))
    (hDE : (m-n+1)/2+a*Real.sin (α/2-z)+β*Real.cos (α/2-z)=W (α/2-z))
    (hEH : (m+n+1)/2+a*Real.sin (α/2+z)-β*Real.cos (α/2+z)=W (α/2+z)) :
    a=x m n α z+1/2 ∧ β=b m n α z := by
  have ht := half_trig hα
  have hDE' := hDE
  have hEH' := hEH
  dsimp [W] at hDE' hEH'
  rw [Real.sin_sub,Real.cos_sub] at hDE'
  rw [Real.sin_add,Real.cos_add] at hEH'
  have hU : (a-1/2)*Real.cos z+β*Real.sin z=U m α z := by
    have hu := U_equation ht.1.ne' m z
    have heq : 2*Real.sin (α/2)*((a-1/2)*Real.cos z+β*Real.sin z)=
        2*Real.sin (α/2)*U m α z := by nlinarith
    exact (mul_left_cancel₀ (mul_ne_zero (by norm_num) ht.1.ne')) heq
  have hV : -(a-1/2)*Real.sin z+β*Real.cos z=V n α z := by
    have hv := V_equation ht.2.1.ne' n z
    have heq : 2*Real.cos (α/2)*(-(a-1/2)*Real.sin z+β*Real.cos z)=
        2*Real.cos (α/2)*V n α z := by nlinarith
    exact (mul_left_cancel₀ (mul_ne_zero (by norm_num) ht.2.1.ne')) heq
  constructor
  · have hu := congrArg (fun y : ℝ => Real.cos z*y) hU
    have hv := congrArg (fun y : ℝ => Real.sin z*y) hV
    have hn := congrArg (fun y : ℝ => (a-1/2)*y) (Real.sin_sq_add_cos_sq z)
    dsimp [x]
    nlinarith
  · have hu := congrArg (fun y : ℝ => Real.sin z*y) hU
    have hv := congrArg (fun y : ℝ => Real.cos z*y) hV
    have hn := congrArg (fun y : ℝ => β*y) (Real.sin_sq_add_cos_sq z)
    dsimp [b]
    nlinarith

def scaledSecond (m n α z : ℝ) : ℝ :=
  -2*(Real.cos α/Real.sin α+2)*Real.cos (2*z)-2*Real.sin (2*z)+
    m*Real.cos (α/2)*((Real.cos (α/2)/Real.sin (α/2)+2)*Real.cos z+Real.sin z)-
    n*Real.sin (α/2)*(Real.cos z+(Real.sin (α/2)/Real.cos (α/2)-2)*Real.sin z)

theorem coefficient_sum {α : ℝ} (hα : α∈Ioo 0 (27/100 : ℝ)) :
    A α+B α=1/Real.sin α ∧ A α-B α=Real.cos α/Real.sin α := by
  have ht := half_trig hα
  have hsin := Real.sin_two_mul (α/2)
  have hcos := Real.cos_two_mul (α/2)
  rw [show 2*(α/2)=α by ring] at hsin hcos
  constructor
  · rw [hsin]
    dsimp [A,B]
    field_simp [ht.1.ne',ht.2.1.ne']
    nlinarith [Real.sin_sq_add_cos_sq (α/2)]
  · rw [hsin,hcos]
    dsimp [A,B]
    field_simp [ht.1.ne',ht.2.1.ne']
    nlinarith [Real.sin_sq_add_cos_sq (α/2)]

/-- `sin α` times the second derivative of the energy is `scaledSecond`, with the large terms kept
together. -/
theorem scaled_second_identity {α : ℝ} (hα : α∈Ioo 0 (27/100 : ℝ)) (m n z : ℝ) :
    Real.sin α*energyDD m n α z=scaledSecond m n α z := by
  have ht := half_trig hα
  have hab := coefficient_sum hα
  have hsin := Real.sin_two_mul (α/2)
  rw [show 2*(α/2)=α by ring] at hsin
  have hM : Real.sin α*M m α=m*Real.cos (α/2) := by
    rw [hsin]
    dsimp [M]
    field_simp [ht.1.ne']
  have hN : Real.sin α*N n α=n*Real.sin (α/2) := by
    rw [hsin]
    dsimp [N]
    field_simp [ht.2.1.ne']
  have hAB : Real.sin α*(A α+B α)=1 := by
    rw [hab.1]
    field_simp [ht.2.2.ne']
  have hABdiff : Real.sin α*(A α+B α)*(A α-B α+2)=Real.cos α/Real.sin α+2 := by
    rw [hAB,one_mul,hab.2]
  have hK : Real.sin α*(4*Kc α)=2*(Real.cos α/Real.sin α+2) := by
    dsimp [Kc]
    linear_combination 2*hABdiff
  have hS : Real.sin α*(4*Ks α)=2 := by dsimp [Ks]; linear_combination 2*hAB
  have hLc : Real.sin α*(-Lc m n α)=
      m*Real.cos (α/2)*(Real.cos (α/2)/Real.sin (α/2)+2)-n*Real.sin (α/2) := by
    dsimp [Lc]
    rw [show Real.sin α*(-(-2*M m α*(A α+1)+N n α))=
      2*(Real.sin α*M m α)*(A α+1)-Real.sin α*N n α by ring,hM,hN]
    dsimp [A]
    ring
  have hLs : Real.sin α*(-Ls m n α)=
      m*Real.cos (α/2)-n*Real.sin (α/2)*(Real.sin (α/2)/Real.cos (α/2)-2) := by
    dsimp [Ls]
    rw [show Real.sin α*(-(2*N n α*(B α-1)-M m α))=
      Real.sin α*M m α-2*(Real.sin α*N n α)*(B α-1) by ring,hM,hN]
    dsimp [B]
    ring
  dsimp only [energyDD,scaledSecond]
  linear_combination (-Real.cos (2*z))*hK+(-Real.sin (2*z))*hS+Real.cos z*hLc+
    Real.sin z*hLs

end SquaresInCircles.Eight.EContactCurve
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EContactCurve

structure Window (α z : ℝ) : Prop where
  half_cos_lower : 99/100<Real.cos (α/2)
  half_sin_upper : Real.sin (α/2)<27/200
  full_cos_lower : 19271/20000<Real.cos α
  full_sin_upper : Real.sin α<27/100
  cos_lower : Real.cos (α/2)≤Real.cos z
  double_cos_lower : Real.cos α≤Real.cos (2*z)
  sin_bounds : -Real.sin (α/2)≤Real.sin z ∧ Real.sin z≤Real.sin (α/2)
  double_sin_bounds : -Real.sin α≤Real.sin (2*z) ∧ Real.sin (2*z)≤Real.sin α

theorem window {α z : ℝ} (hα : α∈Ioo 0 (27/100 : ℝ)) (hz : |z|≤α/2) :
    Window α z := by
  have hhalf : 0≤α/2 := by linarith [hα.1]
  have hhalfup : α/2≤27/200 := by linarith [hα.2]
  have hhalfSq := pow_le_pow_left₀ hhalf hhalfup 2
  have hfullSq := pow_lt_pow_left₀ hα.2 hα.1.le (by decide : (2:ℕ)≠0)
  have hcoshalf : 99/100<Real.cos (α/2) := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := α/2)]
  have hcosfull : 19271/20000<Real.cos α := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have hzi := abs_le.mp hz
  have hdouble : |2*z|≤α := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hdi := abs_le.mp hdouble
  have hcosz : Real.cos (α/2)≤Real.cos z := by
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg z)
      (by linarith [hα.2,Real.pi_gt_three]) hz
    simpa only [Real.cos_abs] using hh
  have hcosdouble : Real.cos α≤Real.cos (2*z) := by
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (2*z))
      (by linarith [hα.2,Real.pi_gt_three]) hdouble
    simpa only [Real.cos_abs] using hh
  have hsinzlo : -Real.sin (α/2)≤Real.sin z := by
    have hh := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hα.2,Real.pi_gt_three])
      (by linarith [hzi.2,hα.2,Real.pi_gt_three]) hzi.1
    simpa only [Real.sin_neg] using hh
  have hsinzhi : Real.sin z≤Real.sin (α/2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hzi.1,hα.2,Real.pi_gt_three])
      (by linarith [hα.2,Real.pi_gt_three]) hzi.2
  have hsindlo : -Real.sin α≤Real.sin (2*z) := by
    have hh := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hα.2,Real.pi_gt_three])
      (by linarith [hdi.2,hα.2,Real.pi_gt_three]) hdi.1
    simpa only [Real.sin_neg] using hh
  have hsindhi : Real.sin (2*z)≤Real.sin α :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hdi.1,hα.2,Real.pi_gt_three])
      (by linarith [hα.2,Real.pi_gt_three]) hdi.2
  exact ⟨hcoshalf,(Real.sin_le hhalf).trans_lt (by linarith [hα.2]),
    hcosfull,(Real.sin_le hα.1.le).trans_lt hα.2,hcosz,hcosdouble,
    ⟨hsinzlo,hsinzhi⟩,⟨hsindlo,hsindhi⟩⟩

/-- The cancellation of the cotangent terms on the whole orientation interval, controlled by the
factor `(c-1)*(1+4*c*(1-c²))` over a positive denominator. -/
theorem cotangent_cancellation {α z : ℝ}
    (hα : α∈Ioo 0 (27/100 : ℝ)) (hz : |z|≤α/2) :
    -2*(Real.cos α/Real.sin α)*Real.cos (2*z)+
      Real.cos (α/2)*(Real.cos (α/2)/Real.sin (α/2))*Real.cos z≤
        3*Real.sin (α/2) := by
  have ht := half_trig hα
  have hw := window hα hz
  have hcot : 0≤Real.cos α/Real.sin α :=
    div_nonneg (by linarith [hw.full_cos_lower]) ht.2.2.le
  have hfirst := mul_le_mul_of_nonpos_left hw.double_cos_lower
    (show -2*(Real.cos α/Real.sin α)≤0 by linarith)
  have hcoefficient : 0≤Real.cos (α/2)*(Real.cos (α/2)/Real.sin (α/2)) :=
    mul_nonneg ht.2.1.le (div_nonneg ht.2.1.le ht.1.le)
  have hsecond := mul_le_mul_of_nonneg_left (Real.cos_le_one z) hcoefficient
  have hsin := Real.sin_two_mul (α/2)
  have hcos := Real.cos_two_mul (α/2)
  rw [show 2*(α/2)=α by ring] at hsin hcos
  have hformula :
      -2*(Real.cos α/Real.sin α)*Real.cos α+
        Real.cos (α/2)*(Real.cos (α/2)/Real.sin (α/2))=
      (Real.cos (α/2)^3-(2*Real.cos (α/2)^2-1)^2)/
        (Real.cos (α/2)*Real.sin (α/2)) := by
    rw [hsin,hcos]
    field_simp [ht.1.ne',ht.2.1.ne']
    ring
  have hunit := Real.sin_sq_add_cos_sq (α/2)
  have hloss : 0≤1-Real.cos (α/2)^2 := by nlinarith [sq_nonneg (Real.sin (α/2))]
  have hfactor := mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (Real.cos_le_one (α/2)))
    (show 0≤1+4*Real.cos (α/2)*(1-Real.cos (α/2)^2) by
      have hp := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) ht.2.1.le) hloss
      linarith)
  have hunit3 := congrArg (fun r : ℝ => 3*Real.cos (α/2)*r) hunit
  have hmax :
      -2*(Real.cos α/Real.sin α)*Real.cos α+
        Real.cos (α/2)*(Real.cos (α/2)/Real.sin (α/2))≤3*Real.sin (α/2) := by
    rw [hformula]
    apply (div_le_iff₀ (mul_pos ht.2.1 ht.1)).2
    nlinarith
  linarith

theorem scaled_second_upper {m n α z : ℝ}
    (hα : α∈Ioo 0 (27/100 : ℝ)) (hz : |z|≤α/2)
    (hm : m∈Icc (0:ℝ) 1) (hn : |n|≤1) :
    scaledSecond m n α z≤
      5*Real.sin (α/2)+2*Real.sin (α/2)^2+2*Real.sin α+2-4*Real.cos α := by
  have ht := half_trig hα
  have hw := window hα hz
  have hcancel := cotangent_cancellation hα hz
  have hcz : 0≤Real.cos z := by linarith [hw.half_cos_lower,hw.cos_lower]
  have hcot : 0≤Real.cos (α/2)/Real.sin (α/2) := div_nonneg ht.2.1.le ht.1.le
  have hcotprod := mul_nonneg hcot hcz
  have hbracket : 0≤(Real.cos (α/2)/Real.sin (α/2)+2)*Real.cos z+Real.sin z := by
    linarith [hw.half_cos_lower,hw.cos_lower,hw.sin_bounds.1,hw.half_sin_upper]
  have hmterm := mul_le_mul_of_nonneg_right hm.2 (mul_nonneg ht.2.1.le hbracket)
  have htwo := mul_le_mul (Real.cos_le_one (α/2)) (Real.cos_le_one z) hcz
    (by norm_num : (0:ℝ)≤1)
  have hsinpart := mul_le_mul_of_nonneg_left hw.sin_bounds.2 ht.2.1.le
  have hsinpart' := mul_le_mul_of_nonneg_right (Real.cos_le_one (α/2)) ht.1.le
  have htan0 : 0≤Real.sin (α/2)/Real.cos (α/2) := div_nonneg ht.1.le ht.2.1.le
  have htan2 : Real.sin (α/2)/Real.cos (α/2)≤2 := by
    apply (div_le_iff₀ ht.2.1).2
    linarith [hw.half_sin_upper,hw.half_cos_lower]
  have hk : |Real.sin (α/2)/Real.cos (α/2)-2|≤2 := by
    rw [abs_of_nonpos (by linarith : Real.sin (α/2)/Real.cos (α/2)-2≤0)]
    linarith
  have hsz : |Real.sin z|≤Real.sin (α/2) := abs_le.mpr hw.sin_bounds
  have hkprod : |(Real.sin (α/2)/Real.cos (α/2)-2)*Real.sin z|≤2*Real.sin (α/2) := by
    rw [abs_mul]
    exact mul_le_mul hk hsz (abs_nonneg _) (by norm_num)
  have hB : |Real.cos z+(Real.sin (α/2)/Real.cos (α/2)-2)*Real.sin z|≤
      1+2*Real.sin (α/2) :=
    (abs_add_le _ _).trans (add_le_add (Real.abs_cos_le_one z) hkprod)
  have hnprod : |n*(Real.cos z+(Real.sin (α/2)/Real.cos (α/2)-2)*Real.sin z)|≤
      1+2*Real.sin (α/2) := by
    rw [abs_mul]
    simpa using mul_le_mul hn hB (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hnterm : -n*(Real.cos z+(Real.sin (α/2)/Real.cos (α/2)-2)*Real.sin z)≤
      1+2*Real.sin (α/2) := by
    have hh := (neg_le_abs (n*(Real.cos z+
      (Real.sin (α/2)/Real.cos (α/2)-2)*Real.sin z))).trans hnprod
    linarith
  have hnterm' := mul_le_mul_of_nonneg_left hnterm ht.1.le
  dsimp [scaledSecond]
  linarith [hw.double_cos_lower,hw.double_sin_bounds.1]

theorem scaled_second_negative {m n α z : ℝ}
    (hα : α∈Ioo 0 (27/100 : ℝ)) (hz : |z|≤α/2)
    (hm : m∈Icc (0:ℝ) 1) (hn : |n|≤1) :
    scaledSecond m n α z< -(2411/4000 : ℝ) := by
  have hu := scaled_second_upper hα hz hm hn
  have ht := half_trig hα
  have hw := window hα hz
  have hsquare := pow_lt_pow_left₀ hw.half_sin_upper ht.1.le
    (by decide : (2:ℕ)≠0)
  linarith [hw.half_sin_upper,hw.full_sin_upper,hw.full_cos_lower]

theorem energyDD_upper {m n α z : ℝ}
    (hα : α∈Ioo 0 (27/100 : ℝ)) (hz : |z|≤α/2)
    (hm : m∈Icc (0:ℝ) 1) (hn : |n|≤1) :
    energyDD m n α z≤ -(3/5 : ℝ) := by
  have ht := half_trig hα
  have hnumer := scaled_second_negative hα hz hm hn
  rw [←scaled_second_identity hα m n z] at hnumer
  by_contra! hbad
  have hprod := mul_le_mul_of_nonneg_left hbad.le ht.2.2.le
  have hsin := Real.sin_le_one α
  nlinarith

/-- On every subinterval of `[-α/2, α/2]` the energy at an interior point exceeds its value at one
of the endpoints. The reduction of E applies this inside the neighbourhood of strict sorting and
positive tangent. -/
theorem endpoint_improves {m n α l u z : ℝ}
    (hα : α∈Ioo 0 (27/100 : ℝ))
    (hm : m∈Icc (0:ℝ) 1) (hn : |n|≤1)
    (hl : -α/2≤l) (hu : u≤α/2) (hz : z∈Ioo l u) :
    energy m n α l<energy m n α z ∨ energy m n α u<energy m n α z := by
  apply strict_endpoint_of_second_derivative (k := (3/5 : ℝ))
    (df := energyD m n α) (ddf := energyDD m n α) (by norm_num) hz
  · intro r hr
    exact energy_hasDerivAt m n α r
  · intro r hr
    exact energyD_hasDerivAt m n α r
  · intro r hr
    exact energyDD_upper hα (abs_le.mpr ⟨by linarith [hr.1],by linarith [hr.2]⟩) hm hn

end SquaresInCircles.Eight.EContactCurve
end
end
end
