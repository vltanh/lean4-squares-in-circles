module

public import SquaresInCircles.Eight.Words.Short.Outer.One.RoleFourNorm

/-!
# Eight squares: the two literal opposite-sign edge-five tuples

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
