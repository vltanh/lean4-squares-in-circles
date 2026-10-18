module

public import SquaresInCircles.Eight.Arithmetic.PreparedArc
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Exact arctangent endpoint enclosures

The argument is reduced by the algebraic half-angle formula.  Alternating
polynomials through degrees 49 and 51 provide upper and lower bounds.  The
derivative remainders below are exact identities with positive denominator.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Arithmetic

def atanLower (x : ℝ) : ℝ := x - x^3/3 + x^5/5 - x^7/7 + x^9/9 - x^11/11 + x^13/13 - x^15/15 + x^17/17 - x^19/19 + x^21/21 - x^23/23 + x^25/25 - x^27/27 + x^29/29 - x^31/31 + x^33/33 - x^35/35 + x^37/37 - x^39/39 + x^41/41 - x^43/43 + x^45/45 - x^47/47 + x^49/49 - x^51/51
def atanUpper (x : ℝ) : ℝ := x - x^3/3 + x^5/5 - x^7/7 + x^9/9 - x^11/11 + x^13/13 - x^15/15 + x^17/17 - x^19/19 + x^21/21 - x^23/23 + x^25/25 - x^27/27 + x^29/29 - x^31/31 + x^33/33 - x^35/35 + x^37/37 - x^39/39 + x^41/41 - x^43/43 + x^45/45 - x^47/47 + x^49/49

theorem atanLower_le {x : ℝ} (hx : 0≤x) : atanLower x≤Real.arctan x := by
  have hh := nonneg_of_deriv_nonneg (fun t => Real.arctan t-atanLower t)
    (by unfold atanLower; exact Real.differentiable_arctan.sub (by fun_prop))
    (by norm_num [atanLower])
    (fun x hx0 => by
      have hd : (0:ℝ)<1+x^2 := by positivity
      have hid : 1/(1+x^2)-(1 - x^2 + x^4 - x^6 + x^8 - x^10 + x^12 - x^14 + x^16 - x^18 + x^20 - x^22 + x^24 - x^26 + x^28 - x^30 + x^32 - x^34 + x^36 - x^38 + x^40 - x^42 + x^44 - x^46 + x^48 - x^50)=x^52/(1+x^2) := by
        field_simp [ne_of_gt hd]
        ring
      have hp : deriv (fun t => atanLower t) x = 1 - x^2 + x^4 - x^6 + x^8 - x^10 + x^12 - x^14 + x^16 - x^18 + x^20 - x^22 + x^24 - x^26 + x^28 - x^30 + x^32 - x^34 + x^36 - x^38 + x^40 - x^42 + x^44 - x^46 + x^48 - x^50 := by
        unfold atanLower
        simp (disch := fun_prop)
        ring
      rw [deriv_fun_sub (Real.differentiableAt_arctan x) (by unfold atanLower; fun_prop),
        Real.deriv_arctan,hp,hid]
      exact div_nonneg (pow_nonneg hx0 52) hd.le) hx
  linarith

theorem arctan_le_atanUpper {x : ℝ} (hx : 0≤x) : Real.arctan x≤atanUpper x := by
  have hh := nonneg_of_deriv_nonneg (fun t => atanUpper t-Real.arctan t)
    (by unfold atanUpper; exact Differentiable.sub (by fun_prop) Real.differentiable_arctan)
    (by norm_num [atanUpper])
    (fun x hx0 => by
      have hd : (0:ℝ)<1+x^2 := by positivity
      have hid : (1 - x^2 + x^4 - x^6 + x^8 - x^10 + x^12 - x^14 + x^16 - x^18 + x^20 - x^22 + x^24 - x^26 + x^28 - x^30 + x^32 - x^34 + x^36 - x^38 + x^40 - x^42 + x^44 - x^46 + x^48)-1/(1+x^2)=x^50/(1+x^2) := by
        field_simp [ne_of_gt hd]
        ring
      have hp : deriv (fun t => atanUpper t) x = 1 - x^2 + x^4 - x^6 + x^8 - x^10 + x^12 - x^14 + x^16 - x^18 + x^20 - x^22 + x^24 - x^26 + x^28 - x^30 + x^32 - x^34 + x^36 - x^38 + x^40 - x^42 + x^44 - x^46 + x^48 := by
        unfold atanUpper
        simp (disch := fun_prop)
        ring
      rw [deriv_fun_sub (by unfold atanUpper; fun_prop) (Real.differentiableAt_arctan x),
        Real.deriv_arctan,hp,hid]
      exact div_nonneg (pow_nonneg hx0 50) hd.le) hx
  linarith

def atanHalf (x : ℝ) : ℝ := x/(1+Real.sqrt (1+x^2))

theorem atanHalf_nonneg {x : ℝ} (hx : 0≤x) : 0≤atanHalf x := by
  unfold atanHalf
  positivity

theorem arctan_half_identity {x : ℝ} (hx : 0≤x ∧ x≤1) :
    Real.arctan x=2*Real.arctan (atanHalf x) := by
  have hs : 0<Real.sqrt (1+x^2) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0≤1+x^2 by positivity)
  have hd : 0<1+Real.sqrt (1+x^2) := by positivity
  have hy0 := atanHalf_nonneg hx.1
  have hy1 : atanHalf x<1 := by
    unfold atanHalf
    exact (div_lt_one hd).mpr (by linarith [hx.2])
  have hyden : 0<1-(atanHalf x)^2 := by nlinarith [hy0,hy1]
  have hne : (1+Real.sqrt (1+x^2))^2-x^2 ≠ 0 := ne_of_gt (by nlinarith [hsq,hs])
  have hid : 2*atanHalf x/(1-(atanHalf x)^2)=x := by
    unfold atanHalf
    field_simp [ne_of_gt hd,ne_of_gt hyden,hne]
    nlinarith [congrArg (fun z : ℝ => x*z) hsq]
  rw [Real.two_mul_arctan (by linarith [hy0]) hy1,hid]

def atanExpr {n : ℕ} : ℕ → ScalarExpr n → ScalarExpr n
  | 0,e => e
  | k+1,e => .add (atanExpr k e)
      (.mul (.const (((-1 : ℚ)^(k+1))/(2*(k+1)+1))) (.pow e (2*(k+1)+1)))

theorem atanExpr_valid {n k : ℕ} {boxes : Fin n→ QInterval} {e : ScalarExpr n}
    (he : e.Valid boxes) : (atanExpr k e).Valid boxes := by
  induction k with
  | zero => exact he
  | succ k hk => exact ⟨hk,⟨True.intro,he⟩⟩

theorem atanExpr_lower_value (e : ScalarExpr 0) :
    (atanExpr 25 e).value=atanLower e.value := by
  norm_num [atanExpr,ScalarExpr.value,ScalarExpr.eval,atanLower]
  ring
theorem atanExpr_upper_value (e : ScalarExpr 0) :
    (atanExpr 24 e).value=atanUpper e.value := by
  norm_num [atanExpr,ScalarExpr.value,ScalarExpr.eval,atanUpper]
  ring

structure ArctanEndpoint where
  input : ℚ
  root : QInterval
  output : QInterval
  deriving DecidableEq, Repr

namespace ArctanEndpoint
def halfExpr (a : ArctanEndpoint) : ScalarExpr 0 :=
  .div (.const a.input) (.add (.const 1) (.sqrt (.const (1+a.input^2)) a.root))
def lowerExpr (a : ArctanEndpoint) : ScalarExpr 0 :=
  .mul (.const 2) (atanExpr 25 a.halfExpr)
def upperExpr (a : ArctanEndpoint) : ScalarExpr 0 :=
  .mul (.const 2) (atanExpr 24 a.halfExpr)
def NumericValid (a : ArctanEndpoint) : Prop :=
  0≤a.input ∧ a.input≤1 ∧ a.halfExpr.Valid closedBoxes ∧
  a.output.lo≤(a.lowerExpr.range closedBoxes).lo ∧
  (a.upperExpr.range closedBoxes).hi≤a.output.hi
instance (a : ArctanEndpoint) : Decidable a.NumericValid := by unfold NumericValid; infer_instance

theorem halfExpr_value (a : ArctanEndpoint) : a.halfExpr.value=atanHalf a.input := by
  simp [halfExpr,ScalarExpr.value,ScalarExpr.eval,ScalarExpr.div,atanHalf,div_eq_mul_inv]

theorem sound {a : ArctanEndpoint} (ha : a.NumericValid) :
    a.output.Mem (Real.arctan a.input) := by
  have hx : (0:ℝ)≤a.input ∧ (a.input:ℝ)≤1 := by exact_mod_cast And.intro ha.1 ha.2.1
  have he := ha.2.2.1
  have hL := a.lowerExpr.closed_sound (show a.lowerExpr.Valid closedBoxes from
    ⟨True.intro,atanExpr_valid he⟩)
  have hU := a.upperExpr.closed_sound (show a.upperExpr.Valid closedBoxes from
    ⟨True.intro,atanExpr_valid he⟩)
  have hl := atanLower_le (atanHalf_nonneg hx.1)
  have hu := arctan_le_atanUpper (atanHalf_nonneg hx.1)
  have hid := arctan_half_identity hx
  have hlcast : (a.output.lo:ℝ)≤(a.lowerExpr.range closedBoxes).lo := by exact_mod_cast ha.2.2.2.1
  have hucast : ((a.upperExpr.range closedBoxes).hi:ℝ)≤a.output.hi := by exact_mod_cast ha.2.2.2.2
  have hlv : a.lowerExpr.value=2*atanLower (atanHalf a.input) := by
    change 2*(atanExpr 25 a.halfExpr).value=_
    rw [atanExpr_lower_value,halfExpr_value]
  have huv : a.upperExpr.value=2*atanUpper (atanHalf a.input) := by
    change 2*(atanExpr 24 a.halfExpr).value=_
    rw [atanExpr_upper_value,halfExpr_value]
  rw [hlv] at hL
  rw [huv] at hU
  exact ⟨by linarith [hL.1],by linarith [hU.2]⟩
end ArctanEndpoint

end SquaresInCircles.Eight.Arithmetic
