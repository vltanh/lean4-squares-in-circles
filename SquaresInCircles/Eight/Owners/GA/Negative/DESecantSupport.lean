module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.GA.Sorted.Support
public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcavity

/-!
# Eight squares: the small-A D support with a negative DE3 secant

The secant coefficient ranges over the complete interval [1,1.308].
Negative angles are diagonal. On positive angles the diagonal branch
increases and the full-circle branch is concave. The transition is an
actual equality of the force components, obtained by the intermediate
value theorem. Thus the only angle endpoint comparisons are zero and
the original variation cap. A rational affine upper bound for the cap
norm is proved on the entire coefficient interval by a single quadratic
comparison; it retains a 19/100 endpoint reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDESecant
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity Secondary

abbrev c : ℝ := 9/5
abbrev L : ℝ := 103/100

def forceF (u z : ℝ) : ℝ := u+c*Real.sin z
def forceG (z : ℝ) : ℝ := c*Real.cos z
def baseline (u : ℝ) : ℝ := (u+c)*(1-GlobalGA.Secondary.diagonal)

def stress (u z : ℝ) : ℝ :=
  c*edgeWidth z+u-clippedSupport (forceF u z) (forceG z)+L*z

def diagonalPositive (u z : ℝ) : ℝ :=
  c*(1+Real.cos z+Real.sin z)/2+u-
    GlobalGA.Secondary.diagonal*(u+c*Real.sin z+c*Real.cos z)+L*z

def fullPositive (u z : ℝ) : ℝ :=
  c*(1+Real.cos z+Real.sin z)/2+u-R*pairNorm u c z+
    (u+c*Real.sin z+c*Real.cos z)/2+L*z

def fullPositiveD (u z : ℝ) : ℝ :=
  c*(Real.cos z-Real.sin z)-R*normD1 u c z+L

def diagonalNegative (u w : ℝ) : ℝ :=
  c*(1+Real.cos w+Real.sin w)/2+u-
    GlobalGA.Secondary.diagonal*(u-c*Real.sin w+c*Real.cos w)-L*w

theorem coefficient_range {u : ℝ} (hu : u∈Icc 1 (327/250:ℝ)) :
    0<u ∧ u≤c ∧ c≤2*u := by
  dsimp [c]
  exact ⟨by linarith [hu.1],by linarith [hu.2],by linarith [hu.1]⟩

theorem phi_lower {z : ℝ} (hz : z∈Icc 0 frameCap) : 1≤PositiveAngularEnvelope.phi z := by
  have ht := transport_trig hz
  have hp := mul_nonneg (by linarith [ht.1] : 0≤Real.cos z) ht.2.2.1
  dsimp [PositiveAngularEnvelope.phi]
  nlinarith [Real.sin_sq_add_cos_sq z]

theorem force_positive {u z : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hz : |z|≤frameCap) : 0<forceF u z+forceG z ∧ 0<forceG z := by
  have ht := small_angle hz
  have hsin := (abs_le.mp ht.2).1
  dsimp [forceF,forceG,c,frameCap] at *
  constructor <;> linarith [hu.1,ht.1]

theorem force_norm (u z : ℝ) :
    Real.sqrt ((forceF u z)^2+(forceG z)^2)=pairNorm u c z := by
  have he : (forceF u z)^2+(forceG z)^2=u^2+c^2+2*u*c*Real.sin z := by
    dsimp [forceF,forceG]
    nlinarith only [congrArg (fun x : ℝ => c^2*x) (Real.sin_sq_add_cos_sq z)]
  rw [he]
  rfl

theorem diagonalPositive_eq {u z : ℝ} (hz : z∈Icc 0 frameCap) :
    diagonalPositive u z=c*edgeWidth z+u-
      diagonalSupport (forceF u z) (forceG z)+L*z := by
  rw [edgeWidth_positive_formula hz]
  dsimp [diagonalPositive,diagonalSupport,forceF,forceG]
  ring

theorem fullPositive_eq {u z : ℝ} (hz : z∈Icc 0 frameCap) :
    fullPositive u z=c*edgeWidth z+u-
      fullSupport (forceF u z) (forceG z)+L*z := by
  rw [edgeWidth_positive_formula hz]
  unfold fullSupport
  rw [force_norm]
  dsimp [fullPositive,forceF,forceG]
  ring

theorem positive_match {u z : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hz : z∈Icc 0 frameCap) (he : forceF u z-forceG z=0) :
    diagonalPositive u z=fullPositive u z := by
  have hforce := force_positive hu (by rw [abs_of_nonneg hz.1]; exact hz.2)
  rw [diagonalPositive_eq hz,fullPositive_eq hz,
    full_at_diagonal (by linarith) hforce.1.le]

theorem diagonalPositive_hasDerivAt (u z : ℝ) :
    HasDerivAt (diagonalPositive u)
      (c*(1/2-GlobalGA.Secondary.diagonal)*(Real.cos z-Real.sin z)+L) z := by
  have h := ((((((((Real.hasDerivAt_cos z).const_add 1).fun_add
    (Real.hasDerivAt_sin z)).const_mul c).div_const 2).add_const u).fun_sub
      (((((Real.hasDerivAt_sin z).const_mul c).const_add u).fun_add
        ((Real.hasDerivAt_cos z).const_mul c)).const_mul GlobalGA.Secondary.diagonal)).fun_add
          ((hasDerivAt_id' z).const_mul L))
  exact h.congr_deriv (by ring)

theorem diagonalPositive_monotone (u : ℝ) :
    MonotoneOn (diagonalPositive u) (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun z _ => (diagonalPositive_hasDerivAt u z).continuousAt.continuousWithinAt)
    (fun z _ => diagonalPositive_hasDerivAt u z)
  intro z hz
  have ht := transport_trig (Ioo_subset_Icc_self hz)
  have hm := mul_le_mul_of_nonneg_left
    (show Real.cos z-Real.sin z≤1 by linarith [ht.2.1,ht.2.2.1])
    (show 0≤c*(GlobalGA.Secondary.diagonal-1/2) by dsimp [c]; linarith [diagonal_bounds.1])
  dsimp [c,L] at *
  nlinarith [diagonal_bounds.2]

theorem diagonalPositive_lower {u z : ℝ} (hz : z∈Icc 0 frameCap) :
    baseline u≤diagonalPositive u z := by
  have hm := diagonalPositive_monotone u
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) hz hz.1
  have h0 : diagonalPositive u 0=baseline u := by
    simp [diagonalPositive,baseline]
    ring
  rwa [h0] at hm

theorem fullPositive_hasDerivAt {u z : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hz : z∈Icc 0 frameCap) :
    HasDerivAt (fullPositive u) (fullPositiveD u z) z := by
  have hr := coefficient_range hu
  have hn := pairNorm_hasDerivAt hr.1 (by norm_num [c] : 0<c)
    (by rw [abs_of_nonneg hz.1]; exact hz.2)
  have h := ((((((((Real.hasDerivAt_cos z).const_add 1).fun_add
    (Real.hasDerivAt_sin z)).const_mul c).div_const 2).add_const u).fun_sub
      (hn.const_mul R)).fun_add
    (((((Real.hasDerivAt_sin z).const_mul c).const_add u).fun_add
      ((Real.hasDerivAt_cos z).const_mul c)).div_const 2)).fun_add
        ((hasDerivAt_id' z).const_mul L)
  exact h.congr_deriv (by dsimp [fullPositiveD]; ring)

theorem fullPositiveD_hasDerivAt {u z : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hz : z∈Icc 0 frameCap) :
    HasDerivAt (fullPositiveD u) (curvature R u c z-c*PositiveAngularEnvelope.phi z) z := by
  have hr := coefficient_range hu
  have hn := normD1_hasDerivAt hr.1 (by norm_num [c] : 0<c)
    (by rw [abs_of_nonneg hz.1]; exact hz.2)
  have h := ((((Real.hasDerivAt_cos z).fun_sub (Real.hasDerivAt_sin z)).const_mul c).fun_sub
    (hn.const_mul R)).add_const L
  exact h.congr_deriv (by dsimp [curvature,PositiveAngularEnvelope.phi]; ring)

theorem fullPositive_concave {u : ℝ} (hu : u∈Icc 1 (327/250:ℝ)) :
    ConcaveOn ℝ (Icc 0 frameCap) (fullPositive u) := by
  have hr := coefficient_range hu
  apply concave_of_deriv2 (fun z hz => fullPositive_hasDerivAt hu hz)
    (fun z hz => fullPositiveD_hasDerivAt hu hz)
  intro z hz
  have hcurv := curvature_positive_upper (Real.sqrt_nonneg qCap) hr.1 hr.2.1 hr.2.2 hz
  have hslope := curvatureSlope_nonneg (Real.sqrt_nonneg qCap) hr.1
    (by norm_num [c] : 0<c)
  have hcap := mul_le_mul_of_nonneg_left hz.2 hslope
  have hconstants := curvature_constant_bounds (R := R) (Real.sqrt_nonneg qCap)
    (by rw [radius_sq]) hr.1 hr.2.1 hr.2.2
  have hphi := phi_lower hz
  dsimp [c] at *
  nlinarith [hconstants.2.2.2]

/-- The cap norm is enclosed on the whole secant-coefficient interval.
The squared majorant is concave after subtracting the force energy. -/
theorem cap_norm_upper {u : ℝ} (hu : u∈Icc 1 (327/250:ℝ)) :
    pairNorm u c frameCap<(171/100:ℝ)+(43/50)*u := by
  have hr := coefficient_range hu
  have hs := pairNorm_sq hr.1 (by norm_num [c] : 0<c)
    (t := frameCap) (by norm_num [frameCap])
  have ht := (transport_trig
    (by norm_num [frameCap] : frameCap∈Icc 0 frameCap)).2.2.2.1
  have hmul := mul_le_mul_of_nonneg_left ht.le hr.1.le
  have hinterval := mul_nonneg (sub_nonneg.mpr hu.1) (sub_nonneg.mpr hu.2)
  have hmajorant : u^2+c^2+2*u*c*Real.sin frameCap<
      ((171/100:ℝ)+(43/50)*u)^2 := by
    dsimp [c]
    nlinarith only [hmul,hinterval,hu.1,hu.2]
  dsimp [pairEnergy,pairProduct] at hs
  have hq : (pairNorm u c frameCap)^2<((171/100:ℝ)+(43/50)*u)^2 := by
    rw [hs]; linarith [hmajorant]
  exact lt_of_pow_lt_pow_left₀ 2 (by linarith [hu.1]) hq

theorem fullPositive_cap {u : ℝ} (hu : u∈Icc 1 (327/250:ℝ)) :
    baseline u+19/100<fullPositive u frameCap := by
  have hn := cap_norm_upper hu
  have hnp : 0<(171/100:ℝ)+(43/50)*u := by linarith [hu.1]
  have hnorm := radius_norm_upper hnp hn
  have hphi := phi_cap_lower
  have hdiag := mul_le_mul_of_nonneg_left diagonal_bounds.1.le
    (show 0≤u+c by dsimp [c]; linarith [hu.1])
  dsimp [fullPositive,baseline,PositiveAngularEnvelope.phi,c,L,frameCap] at *
  nlinarith [hu.2]

theorem positive_lower {u z : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hz : z∈Icc 0 frameCap) : baseline u≤ stress u z := by
  by_cases hdiag : forceF u z≤forceG z
  · have he : stress u z=diagonalPositive u z := by
      rw [diagonalPositive_eq hz]
      simp [stress,clippedSupport,hdiag]
    rw [he]
    exact diagonalPositive_lower hz
  · let e : ℝ→ℝ := fun t => forceF u t-forceG t
    have hec : Continuous e := by dsimp [e,forceF,forceG]; fun_prop
    have he0 : e 0≤0 := by
      dsimp [e,forceF,forceG,c]
      norm_num
      linarith [hu.2]
    have hez : 0≤e z := by dsimp [e]; linarith
    obtain ⟨t,ht,hte⟩ := intermediate_value_Icc hz.1 hec.continuousOn
      (show (0:ℝ)∈Icc (e 0) (e z) from ⟨he0,hez⟩)
    have hti : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hz.2⟩
    have hleft : baseline u≤fullPositive u t := by
      rw [← positive_match hu hti hte]
      exact diagonalPositive_lower hti
    have hright : baseline u≤fullPositive u frameCap := by
      linarith [fullPositive_cap hu]
    have hmin := (fullPositive_concave hu).min_le_of_mem_Icc hti
      (by norm_num [frameCap] : frameCap∈Icc 0 frameCap) ⟨ht.2,hz.2⟩
    have he : stress u z=fullPositive u z := by
      rw [fullPositive_eq hz]
      simp [stress,clippedSupport,hdiag]
    rw [he]
    exact (le_min hleft hright).trans hmin

theorem diagonalNegative_hasDerivAt (u w : ℝ) :
    HasDerivAt (diagonalNegative u)
      (c*((GlobalGA.Secondary.diagonal+1/2)*Real.cos w+(GlobalGA.Secondary.diagonal-1/2)*Real.sin w)-L) w := by
  have h := ((((((((Real.hasDerivAt_cos w).const_add 1).fun_add
    (Real.hasDerivAt_sin w)).const_mul c).div_const 2).add_const u).fun_sub
      (((((Real.hasDerivAt_sin w).const_mul c).const_sub u).fun_add
        ((Real.hasDerivAt_cos w).const_mul c)).const_mul GlobalGA.Secondary.diagonal)).fun_sub
          ((hasDerivAt_id' w).const_mul L))
  exact h.congr_deriv (by ring)

theorem diagonalNegative_monotone (u : ℝ) :
    MonotoneOn (diagonalNegative u) (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun w _ => (diagonalNegative_hasDerivAt u w).continuousAt.continuousWithinAt)
    (fun w _ => diagonalNegative_hasDerivAt u w)
  intro w hw
  have ht := transport_trig (Ioo_subset_Icc_self hw)
  have hm := mul_le_mul (show (1399/1000:ℝ)≤GlobalGA.Secondary.diagonal+1/2 by linarith [diagonal_bounds.1])
    ht.1.le (by norm_num : (0:ℝ)≤7648/10000) (by linarith [diagonal_bounds.1])
  have hp := mul_nonneg (show 0≤GlobalGA.Secondary.diagonal-1/2 by linarith [diagonal_bounds.1]) ht.2.2.1
  dsimp [c,L]
  nlinarith

theorem negative_lower {u w : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hw : w∈Icc 0 frameCap) : baseline u≤ stress u (-w) := by
  have hphi := phi_lower hw
  have hdiag : forceF u (-w)≤forceG (-w) := by
    dsimp [forceF,forceG,PositiveAngularEnvelope.phi,c] at *
    simp only [Real.cos_neg,Real.sin_neg]
    linarith [hu.2]
  have he : stress u (-w)=diagonalNegative u w := by
    simp only [stress,clippedSupport,ite_eq_left hdiag]
    rw [edgeWidth_negative_formula hw]
    dsimp [diagonalNegative,diagonalSupport,forceF,forceG]
    simp only [Real.cos_neg,Real.sin_neg]
    ring
  have hm := diagonalNegative_monotone u
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) hw hw.1
  have h0 : diagonalNegative u 0=baseline u := by
    simp [diagonalNegative,baseline]
    ring
  rw [he]
  rwa [h0] at hm

theorem stress_lower {u z : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hz : |z|≤frameCap) : baseline u≤ stress u z := by
  by_cases hpos : 0≤z
  · exact positive_lower hu ⟨hpos,by simpa [abs_of_nonneg hpos] using hz⟩
  · have hneg : -z∈Icc 0 frameCap :=
      ⟨by linarith,by simpa [abs_of_neg (lt_of_not_ge hpos)] using hz⟩
    simpa only [neg_neg] using negative_lower hu hneg

/-- This is the D inequality used by the actual source stress. -/
theorem actual_lower {q u z : ℝ} {D : SignedPoint}
    (hs : D.Sorted) (hy : 0≤D.y) (hc : D.Contained q) (hq : q≤qCap)
    (hu : u∈Icc 1 (327/250:ℝ)) (hz : |z|≤frameCap) :
    baseline u≤c*edgeWidth z+u-
      ((u+c*Real.sin z)*D.a+c*Real.cos z*D.y)+L*z := by
  have hsup := actual_clipped_support hs hy hc hq (force_positive hu hz).1.le
  have hlow := stress_lower hu hz
  dsimp [stress,forceF,forceG] at *
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDESecant
