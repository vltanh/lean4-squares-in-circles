module

public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Words.Short.Outer.One.RoleFourScalars
public import SquaresInCircles.Eight.Words.Short.Outer.One.UnitScalars
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameCap

/-!
# Eight squares: both upper primary owners on opposite edge five

The literal multipliers .776 and .774 give the two written full-circle
supports. The unit-vector projection bounds the norm derivative on
the entire angle half; only the initial two radicals are evaluated.
-/

section
/-!
## The intrinsic support transition for role four

The diagonal/full-circle transition is the unique zero of the actual
coefficient difference. The full-circle branch is concave throughout
the interval from that transition to the final angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.RoleFour
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.SameZero.PJ.Reference (sinBox cosBox)

def transition (x : ℝ) : ℝ := weight*(Real.cos x+Real.sin x)-target
def transitionD (x : ℝ) : ℝ := weight*(Real.cos x-Real.sin x)
def IsEvent (e : ℝ) : Prop := e∈Ioo 0 (3/10) ∧ transition e=0

lemma transition_hasDerivAt (x : ℝ) : HasDerivAt transition (transitionD x) x := by
  convert (((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).const_mul weight).sub_const
    target using 1
  · funext y; simp only [transition,Pi.add_apply]
  · simp only [transitionD]; ring

lemma transition_strictMono : StrictMonoOn transition (Icc 0 (7/10)) := by
  apply strict_increase_of_reserve
    (fun y _ => (transition_hasDerivAt y).continuousAt.continuousWithinAt)
    (fun y _ => transition_hasDerivAt y) (show (0:ℝ)<2/25 by norm_num)
  intro y hy
  have ht := positive_trig (Ioo_subset_Icc_self hy)
  dsimp [transitionD,weight]
  linarith [ht.1,ht.2.2.2.1]

lemma transition_endpoints : transition 0<0 ∧ (26/1000:ℝ)<transition (3/10) := by
  constructor
  · norm_num [transition,weight,target]
  · let B := (((Interval.point weight).mul
      ((cosBox (3/10) (by norm_num)).add (sinBox (3/10) (by norm_num)))).sub
        (Interval.point target))
    have hb : (26/1000:ℝ)<B.lo := by
      norm_num [B,weight,target,SecondWord.SameZero.PJ.Reference.sinBox,
        SecondWord.SameZero.PJ.Reference.cosBox,Interval.of_bounds,Interval.point,
        Interval.add,Interval.sub,Interval.neg,Interval.mul,
        HighOrderTaylor.S17,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
        HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
        sin9,sin7,cos10,cos8]
    exact hb.trans_le B.mem.1

theorem exists_event : ∃e,IsEvent e := by
  have hc : Continuous transition := by
    have he : transition = fun y => weight*(Real.cos y+Real.sin y)-target := rfl
    rw [he]; fun_prop
  obtain ⟨e,he,heq⟩ := intermediate_value_Icc (show (0:ℝ)≤3/10 by norm_num)
    hc.continuousOn (show (0:ℝ)∈Icc (transition 0) (transition (3/10)) from
      ⟨transition_endpoints.1.le,by linarith [transition_endpoints.2]⟩)
  have hl : 0<e := lt_of_le_of_ne he.1 (by
    intro h
    rw [←h] at heq
    linarith [transition_endpoints.1])
  have hu : e<3/10 := lt_of_le_of_ne he.2 (by
    intro h
    rw [h] at heq
    linarith [transition_endpoints.2])
  exact ⟨e,⟨hl,hu⟩,heq⟩

lemma event_angle {e : ℝ} (he : IsEvent e) : e∈Icc 0 (7/10) :=
  ⟨he.1.1.le,by linarith [he.1.2]⟩

lemma event_identity {e : ℝ} (he : IsEvent e) :
    weight*(Real.cos e+Real.sin e)=target := by
  have hh := he.2
  dsimp [transition] at hh
  linarith

lemma before_event {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    weight*(Real.cos x+Real.sin x)≤target := by
  have hh := transition_strictMono.monotoneOn
    (show x∈Icc 0 (7/10) from ⟨hx.1,hx.2.trans (event_angle he).2⟩)
    (event_angle he) hx.2
  rw [he.2] at hh
  dsimp [transition] at hh
  linarith

abbrev radius : ℝ := Real.sqrt Q0
def normA : ℝ := weight^2+target^2
def normC : ℝ := -2*weight*target
def N (x : ℝ) : ℝ := CircularNorm.norm normA 0 normC x
def normValue (x : ℝ) : ℝ :=
  Real.pi/2-x+constant+(weight+target)/2+weight*Real.cos x-radius*N x
def normFirst (x : ℝ) : ℝ :=
  -1-weight*Real.sin x-radius*CircularNorm.d1 normA 0 normC x
def normSecond (x : ℝ) : ℝ :=
  -weight*Real.cos x-radius*CircularNorm.d2 normA 0 normC x

lemma radius_positive : 0<radius := Real.sqrt_pos.mpr (by norm_num [Q0])
lemma radius_sq : radius^2=Q0 := Real.sq_sqrt (by norm_num [Q0])
lemma radius_upper : radius<(1978788/1000000:ℝ) := by
  rw [radius,Real.sqrt_lt' (by norm_num)]
  norm_num [Q0]

lemma norm_energy_positive (x : ℝ) : 0<CircularNorm.energy normA 0 normC x := by
  have hs := Real.sin_le_one x
  norm_num [CircularNorm.energy,normA,normC,weight,target] at *
  linarith

lemma norm_positive (x : ℝ) : 0<N x := CircularNorm.norm_pos (norm_energy_positive x)
lemma norm_sq (x : ℝ) : (N x)^2=weight^2+target^2-2*weight*target*Real.sin x := by
  rw [N,CircularNorm.norm_sq (norm_energy_positive x).le]
  simp only [CircularNorm.energy,normA,normC]
  ring

lemma norm_antitone : AntitoneOn N (Icc 0 (7/10)) := by
  intro x hx y hy hxy
  have hs := sin_mono hx hy hxy
  have hNx := norm_sq x
  have hNy := norm_sq y
  norm_num [weight,target] at *
  nlinarith [norm_positive x,norm_positive y]

lemma event_norm_square {e : ℝ} (he : IsEvent e) :
    (N e)^2=2*weight^2*(Real.cos e)^2 := by
  have hn := norm_sq e
  have hc := Real.sin_sq_add_cos_sq e
  have heq := event_identity he
  linear_combination hn-weight^2*hc-
    (target+weight*Real.cos e-weight*Real.sin e)*heq

lemma norm_after_event {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    (N x)^2≤2*weight^2 := by
  have hh := norm_antitone (event_angle he) ⟨he.1.1.le.trans hx.1,hx.2⟩ hx.1
  have hs := event_norm_square he
  have hc := Real.sin_sq_add_cos_sq e
  have hstep : (N x)^2≤(N e)^2 := by nlinarith [norm_positive x,norm_positive e]
  have hcoef := mul_nonneg (show 0≤2*weight^2 by positivity) (sq_nonneg (Real.sin e))
  nlinarith

lemma radius_norm_after_event {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    radius*N x/4<(7/10:ℝ)*weight := by
  have hh := mul_le_mul_of_nonneg_left (norm_after_event he hx)
    (show 0≤Q0 by norm_num [Q0])
  have hsq : (radius*N x)^2≤2*Q0*weight^2 := by
    rw [mul_pow,radius_sq]
    nlinarith only [hh]
  norm_num [weight,Q0] at *
  nlinarith [mul_pos radius_positive (norm_positive x)]

lemma normValue_hasDerivAt (x : ℝ) : HasDerivAt normValue (normFirst x) x := by
  convert (((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+constant+(weight+target)/2)).add
      ((Real.hasDerivAt_cos x).const_mul weight)).sub
        ((CircularNorm.norm_hasDerivAt (norm_energy_positive x)).const_mul radius)) using 1
  · funext y; simp only [normValue,N,Pi.add_apply,Pi.sub_apply,Pi.neg_apply,id_eq]; ring
  · simp only [normFirst]; ring

lemma normFirst_hasDerivAt (x : ℝ) : HasDerivAt normFirst (normSecond x) x := by
  convert ((((Real.hasDerivAt_sin x).const_mul weight).neg).const_add (-1)).sub
    ((CircularNorm.d1_hasDerivAt (norm_energy_positive x)).const_mul radius) using 1
  · funext y; simp only [normFirst,Pi.sub_apply,Pi.neg_apply]; ring
  · simp only [normSecond]; ring

lemma normValue_concave {e : ℝ} (he : IsEvent e) :
    ConcaveOn ℝ (Icc e (7/10)) normValue := by
  apply concave_of_deriv2 (fun x _ => normValue_hasDerivAt x)
    (fun x _ => normFirst_hasDerivAt x)
  intro x hx
  have hc := CircularNorm.curvature_lower (norm_energy_positive x)
    (show (0:ℝ)^2+normC^2≤normA^2 by norm_num [normC,normA,weight,target])
  have hmul := mul_le_mul_of_nonneg_left hc radius_positive.le
  have hcap := radius_norm_after_event he hx
  have ht := positive_trig (show x∈Icc 0 (7/10) from ⟨he.1.1.le.trans hx.1,hx.2⟩)
  have hmul' : -radius*N x/4≤radius*CircularNorm.d2 normA 0 normC x := by
    simp only [N]; linarith
  have hwc : weight*(7/10)≤weight*Real.cos x :=
    mul_le_mul_of_nonneg_left (by linarith [ht.1]) (by norm_num [weight])
  simp only [normSecond]
  linarith

lemma normValue_at_event {e : ℝ} (he : IsEvent e) : normValue e=diagonal e := by
  have hN := event_norm_square he
  have hdiag := diagonal_circle
  have hprod : radius*N e=2*(outerDiagonal+1/2)*weight*Real.cos e := by
    have hsq : (radius*N e)^2=(2*(outerDiagonal+1/2)*weight*Real.cos e)^2 := by
      calc
        (radius*N e)^2=Q0*(N e)^2 := by rw [mul_pow,radius_sq]
        _=2*(outerDiagonal+1/2)^2*(2*weight^2*(Real.cos e)^2) := by rw [hN,←hdiag]
        _=(2*(outerDiagonal+1/2)*weight*Real.cos e)^2 := by ring
    have hright : 0≤2*(outerDiagonal+1/2)*weight*Real.cos e :=
      mul_nonneg (by dsimp [weight]; linarith [outer_endpoint_bounds.2.2.1])
        (by linarith [(positive_trig (event_angle he)).1])
    nlinarith [mul_pos radius_positive (norm_positive e)]
  have heq := event_identity he
  dsimp [normValue,diagonal]
  linear_combination -hprod-(outerDiagonal+1/2)*heq

lemma norm_final_upper : N (7/10)<(682546867/1000000000:ℝ) := by
  have hh := norm_sq (7/10)
  have hs := fine_cap_trig.1
  norm_num [weight,target] at hh
  nlinarith [norm_positive (7/10)]

lemma normValue_final : (89809/100000:ℝ)<normValue (7/10) := by
  have hprod : radius*N (7/10)<(1978788/1000000:ℝ)*(682546867/1000000000) :=
    (mul_le_mul_of_nonneg_right radius_upper.le (norm_positive (7/10)).le).trans_lt
      (mul_lt_mul_of_pos_left norm_final_upper (by norm_num))
  have hp := pi_hand_enclosure.1
  have hc := fine_cap_trig.2.2.1
  dsimp [normValue,weight,target,constant]
  linarith

lemma normValue_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    (89809/100000:ℝ)<normValue x := by
  apply concave_gt_of_endpoints (normValue_concave he) hx
  · rw [normValue_at_event he]
    linarith [diagonal_lower (event_angle he)]
  · exact normValue_final

end SquaresInCircles.Eight.ShortOuterOne.RoleFour
end
end
end

section
/-!
## The two literal opposite-sign edge-five tuples

The two tuples are related by exact reflection and reversal. The
half-angle identities retain the original angle, with the complete
range below 3/8; the sharper feasible range is derived later.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive
open CommonQuarter CorePairGeometry Arithmetic

def pQ : Bool→ℚ | false => -20967/100000 | true => -21826/100000
def qQ : Bool→ℚ | false => 83048/100000 | true => 83472/100000
def PQ : Bool→ℚ | false => 21826/100000 | true => 20967/100000
def tQ : Bool→ℚ | false => 83472/100000 | true => 83048/100000
def p (r : Bool) : ℝ := pQ r
def q (r : Bool) : ℝ := qQ r
def P (r : Bool) : ℝ := PQ r
def t (r : Bool) : ℝ := tQ r
def c : ℝ := 50283/100000
def threshold : ℝ := 42643/47500
def X0 : ℝ := Real.sqrt (Q0-1/4)
def T0 : ℝ := Real.sqrt (Q0-9/4)
def half (u : ℝ) : ℝ := Real.tan (u/2)
def halfCap : ℝ := 733/2500
def atanFive (x : ℝ) : ℝ := x-x^3/3+x^5/5-x^7/7+x^9/9
abbrev radius := RoleFour.radius

lemma coefficient_bounds (r : Bool) :
    -(21826/100000:ℝ)≤p r ∧ p r≤-(20967/100000:ℝ) ∧
    (83048/100000:ℝ)≤q r ∧ q r≤83472/100000 ∧
    (20967/100000:ℝ)≤P r ∧ P r≤21826/100000 ∧
    (83048/100000:ℝ)≤t r ∧ t r≤83472/100000 := by
  cases r <;> norm_num [p,q,P,t,pQ,qQ,PQ,tQ]

lemma X0_eq : X0=outerAxial+1/2 := by dsimp [X0,outerAxial]; ring
lemma X0_bounds : (1914575671/1000000000:ℝ)<X0 ∧ X0<1914575672/1000000000 := by
  rw [X0_eq]
  constructor <;> linarith [ShortOuterZero.fine_axial_bounds.1,ShortOuterZero.fine_axial_bounds.2]
lemma X0_sq : X0^2=Q0-1/4 := Real.sq_sqrt (by norm_num [Q0])
lemma T0_sq : T0^2=Q0-9/4 := Real.sq_sqrt (by norm_num [Q0])
lemma T0_bounds : (1290581264/1000000000:ℝ)<T0 ∧ T0<1290581265/1000000000 := by
  have hp : 0≤T0 := Real.sqrt_nonneg _
  have hs := T0_sq
  norm_num [Q0] at hs
  constructor <;> nlinarith

lemma half_cos_positive {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0<Real.cos (u/2) := by
  apply transport_cos_pos
  rw [abs_of_nonneg (by linarith [hu.1] : 0≤u/2)]
  linarith [hu.2]

lemma half_bounds {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0≤half u ∧ half u<(3/8:ℝ) := by
  have hhalf : u/2∈Icc 0 (7/20:ℝ) := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hc := Real.one_sub_sq_div_two_le_cos (x:=u/2)
  have hsq := pow_le_pow_left₀ hhalf.1 hhalf.2 2
  have hcos : (751/800:ℝ)≤Real.cos (u/2) := by nlinarith
  have hs := Real.sin_le (show 0≤u/2 from hhalf.1)
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hhalf.1 (by linarith [hhalf.2,Real.pi_gt_three])
  have hcp := half_cos_positive hu
  have hupper : half u≤(280/751:ℝ) := by
    rw [half,Real.tan_eq_sin_div_cos,div_le_iff₀ hcp]
    nlinarith
  exact ⟨by rw [half,Real.tan_eq_sin_div_cos]; exact div_nonneg hs0 hcp.le,by linarith⟩

lemma half_trig {u : ℝ} (hu : u∈Icc 0 (7/10)) :
    Real.cos u=(1-(half u)^2)/(1+(half u)^2) ∧
    Real.sin u=2*half u/(1+(half u)^2) := by
  have hc := half_cos_positive hu
  have hS : Real.sin (u/2)=half u*Real.cos (u/2) := by
    rw [half,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
  have hcircle : (Real.cos (u/2))^2*(1+(half u)^2)=1 := by
    have hh := Real.sin_sq_add_cos_sq (u/2)
    rw [hS] at hh
    nlinarith only [hh]
  have hcos := Real.cos_two_mul (u/2)
  have hsin := Real.sin_two_mul (u/2)
  rw [show 2*(u/2)=u by ring] at hcos hsin
  rw [hS] at hsin
  have hden : 1+(half u)^2≠0 := by positivity
  constructor
  · apply (eq_div_iff hden).2
    linear_combination (1+(half u)^2)*hcos+2*hcircle
  · apply (eq_div_iff hden).2
    linear_combination (1+(half u)^2)*hsin+2*half u*hcircle

lemma angle_arctan_half {u : ℝ} (hu : u∈Icc 0 (7/10)) : u=2*Real.arctan (half u) := by
  rw [half,Real.arctan_tan (by linarith [hu.1,Real.pi_gt_three])
    (by linarith [hu.2,Real.pi_gt_three])]
  ring

lemma arctan_le_five {x : ℝ} (hx : 0≤x) : Real.arctan x≤atanFive x := by
  have hD (y : ℝ) : HasDerivAt (fun y => atanFive y-Real.arctan y)
      ((1-y^2+y^4-y^6+y^8)-1/(1+y^2)) y := by
    have h5 : HasDerivAt atanFive (1-y^2+y^4-y^6+y^8) y := by
      have h := (((((hasDerivAt_id' y).fun_sub ((hasDerivAt_pow 3 y).div_const 3)).fun_add
        ((hasDerivAt_pow 5 y).div_const 5)).fun_sub ((hasDerivAt_pow 7 y).div_const 7)).fun_add
        ((hasDerivAt_pow 9 y).div_const 9))
      exact h.congr_deriv (by norm_num)
    exact h5.fun_sub (Real.hasDerivAt_arctan y)
  have hh := nonneg_of_deriv_nonneg (fun y => atanFive y-Real.arctan y)
    (fun y => (hD y).differentiableAt) (by norm_num [atanFive])
    (fun y _ => by
      have hd : (0:ℝ)<1+y^2 := by positivity
      have hid : (1-y^2+y^4-y^6+y^8)-1/(1+y^2)=y^10/(1+y^2) := by
        rw [eq_div_iff hd.ne']
        field_simp
        ring
      rw [(hD y).deriv,hid]
      positivity) hx
  linarith

lemma atanFive_le_self {x : ℝ} (hx : x∈Icc 0 halfCap) : atanFive x≤x := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have h1 : 0≤1/3-x^2/5 := by dsimp [halfCap] at hx2; nlinarith
  have h2 : 0≤1/7-x^2/9 := by dsimp [halfCap] at hx2; nlinarith
  have hfirst := mul_nonneg (pow_nonneg hx.1 3) h1
  have hsecond := mul_nonneg (pow_nonneg hx.1 7) h2
  dsimp [atanFive]
  nlinarith only [hfirst,hsecond]

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive
end
end
end

section
/-!
## The six exact opposite-sign secondary supports

Each row retains its own fixed multiplier and its literal adjacent
role coefficients. Source supports are the two concave endpoints,
except for the single negative-primary row whose source increases.
The concluding support inequality uses the original weak separator.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeSecondary
open CommonQuarter CorePairGeometry Arithmetic WrongWordCircleSupport
open SameContact (arc ratio)

abbrev Row := Fin 6
def c : Row→ℝ := ![6618/10000,6618/10000,-25931/100000,-25931/100000,-1866/10000,-1866/10000]
def p : Row→ℝ := ![9133/100000,-51554/100000,19335/100000,0,18602/100000,0]
def q : Row→ℝ := ![88074/100000,119909/100000,76744/100000,86884/100000,80996/100000,94766/100000]
def P : Row→ℝ := ![51554/100000,-9133/100000,0,-19335/100000,0,-18602/100000]
def t : Row→ℝ := ![119909/100000,88074/100000,86884/100000,76744/100000,94766/100000,80996/100000]
def weight : Row→ℝ := ![93308/100000,111499/100000,100982/100000,108532/100000,110143/100000,112741/100000]
def threshold (r : Row) : ℝ := if r.val<2 then 359/400 else 17953/20000
def source (r : Row) (b : ℝ) : ℝ := p r*arc b+(weight r-q r)*b
def sourceBound (r : Row) : ℝ := if r=1 then p r*outerAxial
  else min (p r*outerAxial) ((p r+weight r-q r)*outerDiagonal)
abbrev radius := RoleFour.radius
def radiusUpper : ℝ := 494697/250000
def normA (r : Row) : ℝ := (P r)^2+(t r)^2+(weight r)^2
def normB (r : Row) : ℝ := 2*weight r*P r
def normC (r : Row) (high : Bool) : ℝ := 2*weight r*Unit.direction high*t r
def N (r : Row) (high : Bool) (x : ℝ) : ℝ := CircularNorm.norm (normA r) (normB r) (normC r high) x
def value (r : Row) (high : Bool) (x : ℝ) : ℝ :=
  Real.pi/2+Unit.direction high*x+c r+sourceBound r+(weight r+P r+t r)/2+
    weight r*Real.cos x+(1+Unit.direction high)/2*weight r*Real.sin x-radius*N r high x
def first (r : Row) (high : Bool) (x : ℝ) : ℝ :=
  Unit.direction high-weight r*Real.sin x+(1+Unit.direction high)/2*weight r*Real.cos x-
    radius*CircularNorm.d1 (normA r) (normB r) (normC r high) x
def second (r : Row) (high : Bool) (x : ℝ) : ℝ :=
  -weight r*Real.cos x-(1+Unit.direction high)/2*weight r*Real.sin x-
    radius*CircularNorm.d2 (normA r) (normB r) (normC r high) x

lemma coefficient_bounds (r : Row) : 0<weight r ∧ 0<t r ∧ 0<weight r+min (P r) 0 ∧ 0<t r-P r := by
  fin_cases r <;> norm_num [weight,t,P]

lemma fine_ratio_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : (5223/20000:ℝ)<ratio b := by
  have hU := SecondWord.U_positive (SameContact.outer_domain hb)
  dsimp only [SecondWord.U] at hU
  have hA := (outer_bounds (SameContact.arc_state hb)).2.1
  have ha := ShortOuterZero.fine_axial_bounds.2
  change (5223/20000:ℝ)<(b+1/2)/(arc b+1/2)
  apply (lt_div_iff₀ hU).2
  linarith [hb.1]

lemma source_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (source r) (-p r*ratio b+weight r-q r) b := by
  have h := ((SameContact.arc_hasDerivAt (SameContact.outer_domain hb)).const_mul (p r)).fun_add
    ((hasDerivAt_id' b).const_mul (weight r-q r))
  exact h.congr_deriv (by ring)

lemma negative_source_monotone : MonotoneOn (source 1) (Icc 0 outerDiagonal) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun b hb => (source_hasDerivAt 1 hb).continuousAt.continuousWithinAt)
    (fun b hb => source_hasDerivAt 1 (Ioo_subset_Icc_self hb))
  intro b hb
  have hr := fine_ratio_lower (Ioo_subset_Icc_self hb)
  norm_num [p,weight,q]
  linarith

lemma source_support (r : Row) {a b : ℝ} (hs : OuterState a b) :
    sourceBound r≤p r*a+(weight r-q r)*b := by
  by_cases hrow : r=1
  · subst r
    have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
    have hh := negative_source_monotone
      (show (0:ℝ)∈Icc 0 outerDiagonal from ⟨le_rfl,by linarith [outer_endpoint_bounds.2.2.1]⟩)
      hb hb.1
    simpa [sourceBound,source,SameContact.arc_zero,(SameContact.actual_arc hs).1] using hh
  · have hp : 0≤p r := by
      fin_cases r <;> first | exact absurd rfl hrow | norm_num [p]
    dsimp only [sourceBound]
    simp only [hrow,↓reduceIte]
    exact outer_concave_lower hs hp (min_le_left _ _) (by
      have hh := min_le_right (p r*outerAxial) ((p r+weight r-q r)*outerDiagonal)
      nlinarith only [hh])

lemma norm_energy_identity (r : Row) (high : Bool) (x : ℝ) :
    CircularNorm.energy (normA r) (normB r) (normC r high) x=
      (P r+weight r*Real.cos x)^2+(t r+Unit.direction high*weight r*Real.sin x)^2 := by
  cases high <;> dsimp [CircularNorm.energy,normA,normB,normC,Unit.direction] <;>
    linear_combination -(weight r)^2*(Real.sin_sq_add_cos_sq x)

lemma negative_vertical (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (67/1000:ℝ)<t r-weight r*Real.sin x := by
  have ht := (positive_trig hx).2.2.2.1
  fin_cases r <;> norm_num [t,weight] <;> linarith

lemma norm_energy_positive (r : Row) (high : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<CircularNorm.energy (normA r) (normB r) (normC r high) x := by
  rw [norm_energy_identity]
  have hv : 0<t r+Unit.direction high*weight r*Real.sin x := by
    cases high
    · norm_num [Unit.direction]
      linarith [negative_vertical r hx]
    · have hs := mul_nonneg (coefficient_bounds r).1.le (positive_trig hx).2.2.1
      norm_num [Unit.direction]
      linarith [(coefficient_bounds r).2.1]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hv)

lemma norm_positive (r : Row) (high : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<N r high x :=
  CircularNorm.norm_pos (norm_energy_positive r high hx)

lemma norm_sq (r : Row) (high : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (N r high x)^2=(P r)^2+(t r)^2+(weight r)^2+
      2*weight r*(P r*Real.cos x+Unit.direction high*t r*Real.sin x) := by
  have hh := CircularNorm.norm_sq (norm_energy_positive r high hx).le
  convert hh using 1 <;> dsimp [N,CircularNorm.energy,normA,normB,normC]
  ring

lemma norm_initial (r : Row) (high : Bool) :
    (N r high 0)^2=(P r+weight r)^2+(t r)^2 := by
  have hh := norm_sq r high (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  norm_num at hh
  nlinarith only [hh]

lemma value_hasDerivAt (r : Row) (high : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (value r high) (first r high x) x := by
  have h := (((((hasDerivAt_id' x).const_mul (Unit.direction high)).const_add
    (Real.pi/2+c r+sourceBound r+(weight r+P r+t r)/2)).fun_add
      ((Real.hasDerivAt_cos x).const_mul (weight r))).fun_add
        ((Real.hasDerivAt_sin x).const_mul ((1+Unit.direction high)/2*weight r))).fun_sub
          ((CircularNorm.norm_hasDerivAt (norm_energy_positive r high hx)).const_mul radius)
  convert h using 1
  · funext y
    simp only [value,N]
    ring
  · simp only [first]
    ring

lemma first_hasDerivAt (r : Row) (high : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (first r high) (second r high x) x := by
  have h := (((((Real.hasDerivAt_sin x).const_mul (weight r)).neg).const_add
    (Unit.direction high)).fun_add
      ((Real.hasDerivAt_cos x).const_mul ((1+Unit.direction high)/2*weight r))).fun_sub
        ((CircularNorm.d1_hasDerivAt (norm_energy_positive r high hx)).const_mul radius)
  convert h using 1
  · funext y
    simp only [first,Pi.neg_apply]
    ring
  · simp only [second]
    ring

lemma norm_coefficients (r : Row) (high : Bool) (x : ℝ) :
    Real.sqrt ((-P r-weight r*Real.cos x)^2+
      (-t r-Unit.direction high*weight r*Real.sin x)^2)=N r high x := by
  unfold N CircularNorm.norm
  rw [norm_energy_identity]
  congr 1
  ring

theorem original_support (r : Row) (high : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hm : (1+Real.cos x+Real.sin x)/2≤ -b+A*Real.cos x+Unit.direction high*B*Real.sin x) :
    value r high x≤Real.pi/2+Unit.direction high*x+c r+p r*a-q r*b-P r*A-t r*B := by
  have hmargin := mul_le_mul_of_nonneg_left hm (coefficient_bounds r).1.le
  have hsource := source_support r hs
  have htarget := ShortOuterZero.Opposite.Positive.Cap.full_circle_lower
    (X:=-P r-weight r*Real.cos x) (Y:=-t r-Unit.direction high*weight r*Real.sin x) ht
  rw [norm_coefficients] at htarget
  dsimp [value]
  nlinarith only [hmargin,hsource,htarget]

end SquaresInCircles.Eight.ShortOuterOne.OppositeSecondary
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.UpperPrimary
open CommonQuarter CorePairGeometry Arithmetic

def weight : Bool→ℝ | false => 97/125 | true => 387/500
def sourceNorm (r : Bool) : ℝ := Real.sqrt ((weight r-p r)^2+(q r)^2)
def source (r : Bool) : ℝ := (weight r-p r+q r)/2-radius*sourceNorm r
def energy (r : Bool) (u : ℝ) : ℝ :=
  (P r)^2+(t r)^2+(weight r)^2+2*weight r*(P r*Real.sin u-t r*Real.cos u)
def norm (r : Bool) (u : ℝ) : ℝ := Real.sqrt (energy r u)
def projection (r : Bool) (u : ℝ) : ℝ := P r*Real.cos u+t r*Real.sin u
def value (r : Bool) (u : ℝ) : ℝ := Real.pi/2+u+c+source r+
  (weight r+P r+t r)/2+weight r*Real.sin u-radius*norm r u
def first (r : Bool) (u : ℝ) : ℝ :=
  1+weight r*Real.cos u-radius*weight r*projection r u/norm r u
def sourceUpper : Bool→ℝ | false => 322223/250000 | true => 162083/125000
def targetUpper : Bool→ℝ | false => 226021/1000000 | true => 27143/125000

lemma weight_bounds (r : Bool) : 0<weight r ∧ weight r≤97/125 := by
  cases r <;> norm_num [weight]

lemma energy_squares (r : Bool) (u : ℝ) : energy r u=
    (P r+weight r*Real.sin u)^2+(t r-weight r*Real.cos u)^2 := by
  dsimp [energy]
  linear_combination -(weight r)^2*(Real.sin_sq_add_cos_sq u)

lemma energy_positive (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0<energy r u := by
  have hfirst : 0<P r+weight r*Real.sin u := by
    have hh := mul_nonneg (weight_bounds r).1.le (positive_trig hu).2.2.1
    linarith [(coefficient_bounds r).2.2.2.2.1]
  rw [energy_squares]
  nlinarith [sq_nonneg (t r-weight r*Real.cos u)]
lemma norm_positive (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0<norm r u :=
  Real.sqrt_pos.2 (energy_positive r hu)
lemma norm_sq (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) : (norm r u)^2=energy r u :=
  Real.sq_sqrt (energy_positive r hu).le

lemma energy_hasDerivAt (r : Bool) (u : ℝ) :
    HasDerivAt (energy r) (2*weight r*projection r u) u := by
  have hh := ((((Real.hasDerivAt_sin u).const_mul (P r)).fun_sub
    ((Real.hasDerivAt_cos u).const_mul (t r))).const_mul (2*weight r)).const_add
      ((P r)^2+(t r)^2+(weight r)^2)
  exact hh.congr_deriv (by simp only [projection]; ring)

lemma norm_hasDerivAt (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) :
    HasDerivAt (norm r) (weight r*projection r u/norm r u) u := by
  have hh := (energy_hasDerivAt r u).sqrt (energy_positive r hu).ne'
  exact hh.congr_deriv (by rw [norm]; ring)

lemma value_hasDerivAt (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) :
    HasDerivAt (value r) (first r u) u := by
  have hh := ((((((hasDerivAt_id' u).const_add (Real.pi/2)).add_const c).add_const (source r)
    ).add_const ((weight r+P r+t r)/2)).fun_add ((Real.hasDerivAt_sin u).const_mul (weight r))).fun_sub
      ((norm_hasDerivAt r hu).const_mul radius)
  exact hh.congr_deriv (by simp only [first]; ring)

lemma projection_le_norm (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) :
    projection r u≤norm r u := by
  have he : (projection r u)^2+(P r*Real.sin u-t r*Real.cos u+weight r)^2=energy r u := by
    dsimp [projection,energy]
    linear_combination ((P r)^2+(t r)^2)*(Real.sin_sq_add_cos_sq u)
  nlinarith [sq_nonneg (P r*Real.sin u-t r*Real.cos u+weight r),norm_sq r hu,
    norm_positive r hu]

lemma first_positive (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0<first r u := by
  have hn := norm_positive r hu
  have hprojection := (div_le_one hn).2 (projection_le_norm r hu)
  have hprod := mul_le_mul_of_nonneg_left hprojection
    (mul_nonneg RoleFour.radius_positive.le (weight_bounds r).1.le)
  have hR := mul_lt_mul_of_pos_right RoleFour.radius_upper (weight_bounds r).1
  have hc := mul_lt_mul_of_pos_left (show (19/25:ℝ)<Real.cos u by linarith [(positive_trig hu).1])
    (weight_bounds r).1
  have hw := mul_le_mul_of_nonneg_right (weight_bounds r).2
    (by norm_num : (0:ℝ)≤1978788/1000000-19/25)
  have e : radius*weight r*projection r u/norm r u=
      RoleFour.radius*weight r*(projection r u/norm r u) := by ring
  dsimp only [first]
  rw [e]
  linarith only [hprod,hR,hc,hw]

lemma monotone (r : Bool) : MonotoneOn (value r) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hu => (value_hasDerivAt r hu).continuousAt.continuousWithinAt)
    (fun _ hu => value_hasDerivAt r (Ioo_subset_Icc_self hu))
    (fun _ hu => (first_positive r (Ioo_subset_Icc_self hu)).le)

lemma initial_radicals (r : Bool) : sourceNorm r<sourceUpper r ∧ norm r 0<targetUpper r := by
  have hsrc := Real.sq_sqrt (show 0≤(weight r-p r)^2+(q r)^2 by positivity)
  have hsrc0 := Real.sqrt_nonneg ((weight r-p r)^2+(q r)^2)
  have htgt := norm_sq r (by norm_num : (0:ℝ)∈Icc 0 (7/10))
  have htgt0 := norm_positive r (by norm_num : (0:ℝ)∈Icc 0 (7/10))
  cases r <;> norm_num [sourceNorm,sourceUpper,targetUpper,energy,weight,p,q,P,t,pQ,qQ,PQ,tQ] at hsrc hsrc0 htgt ⊢ <;>
    constructor <;> nlinarith

lemma initial (r : Bool) : (1123/1250:ℝ)<value r 0 := by
  have hpi : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  have hsrc := mul_lt_mul'' RoleFour.radius_upper (initial_radicals r).1
    RoleFour.radius_positive.le (Real.sqrt_nonneg _)
  have htgt := mul_lt_mul'' RoleFour.radius_upper (initial_radicals r).2
    RoleFour.radius_positive.le (norm_positive r (by norm_num : (0:ℝ)∈Icc 0 (7/10))).le
  cases r <;> norm_num [value,source,c,p,q,P,t,pQ,qQ,PQ,tQ,weight,sourceUpper,targetUpper] at hsrc htgt ⊢ <;>
    linarith

lemma original_lower (r : Bool) {a b A B u : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (_hu : u∈Icc 0 (7/10))
    (hm : (1+Real.cos u+Real.sin u)/2≤a+A*Real.sin u-B*Real.cos u) :
    value r u≤Real.pi/2+u+c+p r*a-q r*b-P r*A-t r*B := by
  have hsrc := ShortOuterZero.Opposite.Positive.Cap.full_circle_lower
    (X:=p r-weight r) (Y:=-(q r)) hs
  have htgt := ShortOuterZero.Opposite.Positive.Cap.full_circle_lower
    (X:=-(P r)-weight r*Real.sin u) (Y:=weight r*Real.cos u-t r) ht
  have hsep := mul_le_mul_of_nonneg_left hm (weight_bounds r).1.le
  have hsrad : (p r-weight r)^2+(-(q r))^2=(weight r-p r)^2+(q r)^2 := by ring
  have htrad : (-(P r)-weight r*Real.sin u)^2+(weight r*Real.cos u-t r)^2=energy r u := by
    rw [energy_squares]
    ring
  rw [hsrad] at hsrc
  rw [htrad] at htgt
  dsimp [value,source,sourceNorm,norm]
  nlinarith only [hsrc,htgt,hsep]

theorem original (r : Bool) {a b A B u : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hu : u∈Icc 0 (7/10))
    (hm : (1+Real.cos u+Real.sin u)/2≤a+A*Real.sin u-B*Real.cos u) :
    (1123/1250:ℝ)<Real.pi/2+u+c+p r*a-q r*b-P r*A-t r*B :=
  ((initial r).trans_le ((monotone r) (by norm_num) hu hu.1)).trans_le
    (original_lower r hs ht hu hm)

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.UpperPrimary
end
end
end
