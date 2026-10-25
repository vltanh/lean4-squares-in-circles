module

public import SquaresInCircles.Eight.Frames.Pair.TransportAssembly
public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.TrigonometricReserves
public import SquaresInCircles.Eight.Words.Outside.EEndpoint

/-!
# Eight squares: seven-cycle insertion of the two outside-E endpoints

The compact DE2 and DE3 constructions change only E. `CycleEndpoint.cycle` inserts their point at
its physical frame and keeps the original DE axis and every nonincident witness; the new cycle is
in physical order (`CycleEndpoint.ordered`), and both signed variation budgets decrease by an
exact amount (`CycleEndpoint.variations`). The output is again a boundary input at the same
working radius (`CycleEndpoint.boundaryInput`, `cycle_endpoint`).
-/

section
/-!
## The original D-circle term at a negative DE2 contact

The rotated D corner is recovered from its actual outer
q-circle. Its angular gain decreases over the complete allowed n interval,
so the endpoint n=7/10 provides the comparison required by the outside-E
transport. A separate rational reserve supplies the flat-core E case.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace OutsideDContact

def ell (Y n : ℝ) : ℝ := 1+Real.cos n-Y
def root (q Y n : ℝ) : ℝ := Real.sqrt (q-(ell Y n)^2)
def gain (q Y n : ℝ) : ℝ := root q Y n-Real.sin n
def gainDerivative (q Y n : ℝ) : ℝ :=
  ell Y n*Real.sin n/root q Y n-Real.cos n

theorem bounds {q Y n : ℝ} (hq : qLow≤q)
    (hY : Y∈Icc (1/2 : ℝ) (7/5)) (hn : n∈Icc 0 (7/10 : ℝ)) :
    0<ell Y n ∧ ell Y n≤3/2 ∧ 129/100<root q Y n ∧ 0<q-(ell Y n)^2 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hn
  have hl0 : 0<ell Y n := by dsimp [ell]; linarith [hY.2]
  have hlU : ell Y n≤3/2 := by dsimp [ell]; linarith [hY.1]
  have hrad : (129/100 : ℝ)^2<q-(ell Y n)^2 := by
    dsimp [qLow] at hq
    nlinarith
  have hrad0 : 0<q-(ell Y n)^2 := (sq_nonneg _).trans_lt hrad
  have hroot : 129/100<root q Y n := by
    have hs := Real.sq_sqrt hrad0.le
    have hs0 := Real.sqrt_nonneg (q-(ell Y n)^2)
    dsimp [root]
    nlinarith
  exact ⟨hl0,hlU,hroot,hrad0⟩

theorem gain_hasDerivAt {q Y n : ℝ} (hrad : 0<q-(ell Y n)^2) :
    HasDerivAt (gain q Y) (gainDerivative q Y n) n := by
  have hl : HasDerivAt (ell Y) (-Real.sin n) n :=
    ((Real.hasDerivAt_cos n).const_add 1).sub_const Y
  have hr0 : root q Y n≠0 := (Real.sqrt_pos.mpr hrad).ne'
  have hr := ((hasDerivAt_const n q).fun_sub (hl.fun_pow 2)).sqrt hrad.ne'
  have F : HasDerivAt (gain q Y) _ n := hr.fun_sub (Real.hasDerivAt_sin n)
  convert F using 1
  dsimp [gainDerivative,root]
  field_simp
  ring

theorem gain_derivative_negative {q Y n : ℝ} (hq : qLow≤q)
    (hY : Y∈Icc (1/2 : ℝ) (7/5)) (hn : n∈Icc 0 (7/10 : ℝ)) :
    gainDerivative q Y n<0 := by
  obtain ⟨hl0,hlU,hrL,hrad⟩ := bounds hq hY hn
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hn
  have hlow : (129/100 : ℝ)*(7648/10000)<root q Y n*Real.cos n :=
    (mul_lt_mul_of_pos_right hrL (by norm_num : (0:ℝ)<7648/10000)).trans_le
      (mul_le_mul_of_nonneg_left hc.le (by linarith : 0≤root q Y n))
  have hupp := mul_le_mul hlU hs.le hs0 (by norm_num : (0:ℝ)≤3/2)
  unfold gainDerivative
  apply sub_neg.mpr
  apply (div_lt_iff₀ (by linarith : 0<root q Y n)).2
  nlinarith

theorem gain_antitone {q Y : ℝ} (hq : qLow≤q)
    (hY : Y∈Icc (1/2 : ℝ) (7/5)) :
    AntitoneOn (gain q Y) (Icc 0 (7/10 : ℝ)) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro n hn
    exact (gain_hasDerivAt (bounds hq hY hn).2.2.2).continuousAt.continuousWithinAt
  · intro n hn
    exact gain_hasDerivAt (bounds hq hY (Ioo_subset_Icc_self hn)).2.2.2
  · intro n hn
    exact (gain_derivative_negative hq hY (Ioo_subset_Icc_self hn)).le

theorem gain_ge_cap {q Y n : ℝ} (hq : qLow≤q)
    (hY : Y∈Icc (1/2 : ℝ) (7/5)) (hn : n∈Icc 0 (7/10 : ℝ)) :
    gain q Y (7/10)≤gain q Y n :=
  gain_antitone hq hY hn ⟨by norm_num,le_rfl⟩ hn.2

theorem gain_mono_tangent {q Y₁ Y₂ n : ℝ} (hq : qLow≤q)
    (hY₁ : Y₁∈Icc (1/2 : ℝ) (7/5)) (hY₂ : Y₂∈Icc (1/2 : ℝ) (7/5))
    (hn : n∈Icc 0 (7/10 : ℝ)) (hY : Y₁≤Y₂) :
    gain q Y₁ n≤gain q Y₂ n := by
  have hb₁ := bounds hq hY₁ hn
  have hb₂ := bounds hq hY₂ hn
  have hL : ell Y₂ n≤ell Y₁ n := by dsimp [ell]; linarith
  have hsq := pow_le_pow_left₀ hb₂.1.le hL 2
  have hroot := Real.sqrt_le_sqrt (show q-(ell Y₁ n)^2≤q-(ell Y₂ n)^2 by linarith)
  exact sub_le_sub_right hroot (Real.sin n)

theorem gain_gt_core_speed {q Y n : ℝ} (hq : qLow≤q)
    (hY : Y∈Icc (1/2 : ℝ) (7/5)) (hn : n∈Icc 0 (7/10 : ℝ)) :
    87/100<gain q Y n := by
  have hcap := gain_ge_cap hq hY hn
  have hb := bounds hq hY (show (7/10 : ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)
  have hc := cos_upper_four (show (0:ℝ)≤7/10 by norm_num)
  have hs := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  have hcomb : Real.cos (7/10 : ℝ)+(87/50)*Real.sin (7/10 : ℝ)<19/10 := by
    norm_num at hc hs
    linarith
  have hcos0 : 0<Real.cos (7/10 : ℝ) := transport_cos_pos (by norm_num)
  have hsin0 : 0≤Real.sin (7/10 : ℝ) :=
    (transport_trig (show (7/10 : ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)).2.2.1
  have hell : ell Y (7/10)≤1/2+Real.cos (7/10 : ℝ) := by
    dsimp [ell]
    linarith [hY.1]
  have hellsq := pow_le_pow_left₀ hb.1.le hell 2
  have hrootSq := Real.sq_sqrt hb.2.2.2.le
  have hqL := hq
  dsimp [qLow] at hqL
  have hroot : Real.sin (7/10 : ℝ)+87/100<root q Y (7/10) := by
    dsimp [root] at hb hrootSq ⊢
    nlinarith [Real.sin_sq_add_cos_sq (7/10 : ℝ)]
  dsimp only [gain] at hcap ⊢
  linarith

/-- An actual DE2 equality identifies the positive rotated D coordinate
with the same-circle square root. Mere containment is not used here. -/
theorem actual_contact_gain {q b n : ℝ} {D : SignedPoint}
    (hDs : D.Sorted) (hDy : D.y≤0) (hDo : D.Outer q)
    (hn : n∈Icc 0 (7/10 : ℝ))
    (hcontact : (D.a-1/2)*Real.cos n+(D.y-1/2)*Real.sin n+b-1/2=0) :
    (D.a-1/2)*Real.sin n+(1/2-D.y)*Real.cos n=gain q (b+1/2) n := by
  let X := D.a+1/2
  let Y := 1/2-D.y
  let V := X*Real.sin n+Y*Real.cos n
  have ht := transport_trig hn
  have hc : 0<Real.cos n := by linarith [ht.1]
  have hs : 0≤Real.sin n := ht.2.2.1
  have hX : 0<X := by dsimp [X]; linarith [hDs.1]
  have hY : 0<Y := by dsimp [Y]; linarith
  have hV : 0<V := add_pos_of_nonneg_of_pos (mul_nonneg hX.le hs) (mul_pos hY hc)
  have heq : X*Real.cos n-Y*Real.sin n=ell (b+1/2) n := by
    dsimp [X,Y,ell]
    linarith
  have hnorm : X^2+Y^2=q := by
    simpa [X,Y,SignedPoint.Outer,SignedPoint.circle,abs_of_nonpos hDy,
      sub_eq_add_neg,add_comm] using hDo
  have hrotation : (X*Real.cos n-Y*Real.sin n)^2+V^2=q := by
    have hid : (X*Real.cos n-Y*Real.sin n)^2+V^2=
        (X^2+Y^2)*(Real.sin n^2+Real.cos n^2) := by dsimp [V]; ring
    rw [hid,Real.sin_sq_add_cos_sq,hnorm]
    ring
  have hrad : q-(ell (b+1/2) n)^2=V^2 := by rw [heq] at hrotation; linarith
  unfold gain root
  rw [hrad,Real.sqrt_sq_eq_abs,abs_of_pos hV]
  dsimp [V,X,Y]
  ring

theorem fixed_rate_positive {n : ℝ} {D : SignedPoint}
    (hDa : 1/2<D.a) (hDy : D.y≤0) (hn : n∈Icc 0 (7/10 : ℝ)) :
    0<(D.a-1/2)*Real.sin n+(1/2-D.y)*Real.cos n := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hn
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr hDa.le) hs0)
    (mul_pos (by linarith) (by linarith))

end OutsideDContact
end SquaresInCircles.Eight
end
end
end

section
/-!
## Strict derivative gap on the original-radius reference contact

This completes the whole-interval scalar comparison:
the actual reference gap increases, and its left endpoint has reserve
greater than 0.0048. Both the circle identity and the contact equation
are used at the endpoint. No anchor is moved to the reference solution.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OutsideDE2Reference
open Polynomial OutsideDE2Polynomial

theorem u_deriv (q p : ℝ) : HasDerivAt (u q) (-Real.cos p) p := by
  have h := (hasDerivAt_const p (leastPrimary q)).sub (Real.hasDerivAt_sin p)
  rw [zero_sub] at h
  exact h

theorem z_deriv {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    HasDerivAt (z q) (u q p*Real.cos p/z q p) p := by
  have hz0 : 0<z q p := lt_trans (by norm_num [Zlo]) (z_bounds hq hp).1
  have hd := ((hasDerivAt_const p q).sub ((u_deriv q p).pow 2)).sqrt
    (z_bounds hq hp).2.2.ne'
  convert hd using 1
  · rfl
  · dsimp [z]
    field_simp [show Real.sqrt (q-(u q p)^2)≠0 from hz0.ne']
    ring

theorem xy_deriv {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    HasDerivAt (x q) (-y q p*(1-Real.cos p/z q p)) p ∧
      HasDerivAt (y q) (beta q p) p := by
  have hz0 : 0<z q p := lt_trans (by norm_num [Zlo]) (z_bounds hq hp).1
  have hz := z_deriv hq hp
  have hu := u_deriv q p
  constructor
  · convert (hz.mul (Real.hasDerivAt_cos p)).sub (hu.mul (Real.hasDerivAt_sin p)) using 1
    · rfl
    · dsimp [y]
      field_simp [hz0.ne']
      ring
  · convert (hz.mul (Real.hasDerivAt_sin p)).add (hu.mul (Real.hasDerivAt_cos p)) using 1
    · rfl
    · dsimp [beta,x]
      field_simp [hz0.ne']
      ring

theorem gap_deriv {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    HasDerivAt (gap q) (gapDerivative q p) p := by
  have hb := bounds hq hp
  have hr := root_bounds hq hp
  have hx0 : 0<x q p := (factors_positive hp).2.2.1.trans_le hb.x_lower
  have hz0 : 0<z q p := lt_trans (by norm_num [Zlo]) hb.z_lower
  have hR0 : 0<radius q := lt_trans (by norm_num [Rlo]) hb.radius_lower
  have hd := xy_deriv hq hp
  have hL : HasDerivAt (ell q) (-beta q p) p := by
    have h := (hasDerivAt_const p (1+Real.cos (7/10 : ℝ))).sub hd.2
    rw [zero_sub] at h
    exact h
  have hrad : 0<q-(ell q p)^2 := Real.sqrt_pos.mp hr.2.2.1
  have hW : HasDerivAt (root q) (ell q p*beta q p/root q p) p := by
    convert ((hasDerivAt_const p q).sub (hL.pow 2)).sqrt hrad.ne' using 1
    · rfl
    · dsimp [root]
      field_simp [show Real.sqrt (q-(ell q p)^2)≠0 from hr.2.2.1.ne']
      ring
  have hfactor : HasDerivAt (fun t => 1-Real.cos t/radius q)
      (Real.sin p/radius q) p := by
    convert (hasDerivAt_const p (1:ℝ)).sub ((Real.hasDerivAt_cos p).div_const (radius q)) using 1
    ring
  convert (hW.sub_const (Real.sin (7/10 : ℝ))).sub (hd.1.mul hfactor) using 1
  · rfl
  · dsimp [gapDerivative,beta]
    field_simp [hx0.ne',hz0.ne',hR0.ne',hr.2.2.1.ne']
    ring

theorem endpoint_y_floor {q : ℝ} (hq : qLow≤q∧q≤qCap) :
    (379/625 : ℝ)<y q (11/50) := by
  have hp : (11/50 : ℝ)∈Icc (11/50 : ℝ) (7/10) := by constructor <;> norm_num
  have hb := bounds hq hp
  have he := contact_circle hq hp
  have hy0 := y_gt_half hq hp
  have hx0 : 0<x q (11/50) := (factors_positive hp).2.2.1.trans_le hb.x_lower
  have hc := taylor_bounds hp
  have hs7 := sin_lower_seven (show (0:ℝ)≤11/50 by norm_num)
  have hs7pos : 0<(11/50 : ℝ)-(11/50)^3/6+(11/50)^5/120-(11/50)^7/5040 := by norm_num
  by_contra! hybad
  have hx : (9417/5000 : ℝ)<x q (11/50) := by
    have hqlo := hq.1
    dsimp [qLow] at hqlo
    nlinarith [he.1]
  have hfirst := mul_le_mul hybad hc.2.2.2.2.2.1
    (by linarith [hc.2.2.2.1,hc.2.2.2.2.1] : 0≤Real.cos (11/50 : ℝ))
    (show (0:ℝ)≤379/625 by norm_num)
  have hsecond := mul_le_mul
    (show (4417/5000 : ℝ)≤x q (11/50)-1 by linarith)
    hs7 hs7pos.le (by linarith : 0≤x q (11/50)-1)
  rw [C4_eval] at hfirst
  norm_num at hfirst hsecond
  have hP := (constant_bounds hq).2.2.1
  dsimp [Plo] at hP
  nlinarith [he.2]

theorem endpoint_gap {q : ℝ} (hq : qLow≤q∧q≤qCap) :
    (3/625 : ℝ)<gap q (11/50) := by
  have hp : (11/50 : ℝ)∈Icc (11/50 : ℝ) (7/10) := by constructor <;> norm_num
  have hb := bounds hq hp
  have he := contact_circle hq hp
  have hy := endpoint_y_floor hq
  have hx : x q (11/50)<18837/10000 := by
    have hqu : q≤9789/2500 := hq.2
    have hy2 := pow_lt_pow_left₀ hy (by norm_num) (two_ne_zero)
    have hx2 : (x q (11/50))^2<(18837/10000)^2 := by linarith only [he.1,hy2,hqu]
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hx2
  have hr := root_bounds hq hp
  have hcH := cos_upper_four (show (0:ℝ)≤7/10 by norm_num)
  have hsH := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  have hL : ell q (11/50) <
      1+(1-(7/10 : ℝ)^2/2+(7/10)^4/24)-379/625 := by
    dsimp only [ell]
    linarith only [hcH,hy]
  have hroot_sq : (root q (11/50))^2=q-(ell q (11/50))^2 :=
    Real.sq_sqrt (Real.sqrt_pos.mp hr.2.2.1).le
  have hroot : (7/10 : ℝ)-(7/10)^3/6+(7/10)^5/120+4799/5000<root q (11/50) := by
    have hqlo : 19577/5000≤q := hq.1
    have hL2 := pow_lt_pow_left₀ hL hr.1.le (two_ne_zero)
    have h2 : ((7/10 : ℝ)-(7/10)^3/6+(7/10)^5/120+4799/5000)^2<(root q (11/50))^2 := by
      rw [hroot_sq]
      norm_num at hL2 ⊢
      linarith only [hL2,hqlo]
    exact lt_of_pow_lt_pow_left₀ 2 hr.2.2.1.le h2
  have hC : 4799/5000<root q (11/50)-Real.sin (7/10 : ℝ) := by linarith only [hroot,hsH]
  have hc0 := cos_lower_six (show (0:ℝ)≤11/50 by norm_num)
  have hR0 : 0<radius q := lt_trans (by norm_num [Rlo]) hb.radius_lower
  have hdiv := div_le_div₀ (le_trans (by norm_num) hc0) hc0 hR0 hb.radius_upper.le
  have hfactor : 1-Real.cos (11/50 : ℝ)/radius q≤
      1-(1-(11/50 : ℝ)^2/2+(11/50)^4/24-(11/50)^6/720)/(Rhi:ℝ) := by linarith only [hdiv]
  have hfactor0 : 0≤1-Real.cos (11/50 : ℝ)/radius q :=
    (factors_positive hp).2.2.2.2.1.le.trans hb.radius_factor
  have hprod := mul_le_mul hx.le hfactor hfactor0 (show (0:ℝ)≤18837/10000 by norm_num)
  have hB : x q (11/50)*(1-Real.cos (11/50 : ℝ)/radius q)<191/200 := by
    norm_num [Rhi] at hprod
    linarith only [hprod]
  dsimp only [gap]
  linarith only [hC,hB]

theorem gap_strictMono {q : ℝ} (hq : qLow≤q∧q≤qCap) :
    StrictMonoOn (gap q) (Icc (11/50 : ℝ) (7/10)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (11/50 : ℝ) (7/10))
  · exact fun p hp => (gap_deriv hq hp).continuousAt.continuousWithinAt
  · intro p hp
    rw [(gap_deriv hq (interior_subset hp)).deriv]
    exact derivative_pos hq (interior_subset hp)

theorem gap_positive {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) : 0<gap q p := by
  have hbase := endpoint_gap hq
  rcases hp.1.eq_or_lt with he | hlt
  · rw [← he]
    linarith
  · have hh := gap_strictMono hq (by constructor <;> norm_num) hp hlt
    linarith

/-- The actual outer reference contact has a strictly positive DE2
derivative gap on the entire long-EH interval, at the original q. -/
theorem reference_gap {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    beta q p<root q p-Real.sin (7/10 : ℝ) := by
  have hb := bounds hq hp
  have hz0 : 0<z q p := lt_trans (by norm_num [Zlo]) hb.z_lower
  have hx0 : 0≤x q p := (factors_positive hp).2.2.1.le.trans hb.x_lower
  have hc0 : 0≤Real.cos p := by
    have ht := taylor_bounds hp
    exact ht.2.2.2.1.le.trans ht.2.2.2.2.1
  have hd := div_le_div₀ hc0 le_rfl hz0 hb.z_upper
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_left hd 1) hx0
  have hg := gap_positive hq hp
  dsimp [beta,gap] at *
  linarith

end SquaresInCircles.Eight.OutsideDE2Reference
end
end
end

section
/-!
## From the reference gap to original DE2/EH1 contacts

The reference point only compares scalar contact rates. The H primary varies down to the least
sorted primary at the same q, with the required monotonicities (`y_primary_mono`,
`beta_primary_anti`), and D's original rotated corner is recovered at a DE2 contact
(`recover_contact`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace OutsideDE2Comparison

def u (p P : ℝ) : ℝ := P-Real.sin p
def z (q p P : ℝ) : ℝ := Real.sqrt (q-(u p P)^2)
def x (q p P : ℝ) : ℝ := z q p P*Real.cos p-u p P*Real.sin p
def y (q p P : ℝ) : ℝ := z q p P*Real.sin p+u p P*Real.cos p
def beta (q p P : ℝ) : ℝ := x q p P*(1-Real.cos p/z q p P)

theorem contact_circle {q p P : ℝ} (hz : 0≤q-(u p P)^2) :
    (x q p P)^2+(y q p P)^2=q := by
  have hr := Real.sq_sqrt hz
  have hid (Z U s c : ℝ) : (Z*c-U*s)^2+(Z*s+U*c)^2=(Z^2+U^2)*(s^2+c^2) := by ring
  rw [x,y,hid,Real.sin_sq_add_cos_sq,z,hr]
  ring

theorem contact_bounds {q p P : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10))
    (hP : P∈Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) :
    -(123/500 : ℝ)<u p P ∧ u p P<141/500 ∧
      979/500<z q p P ∧ z q p P≤OutsideDE2Reference.radius q ∧
      0<q-(u p P)^2 ∧ 0<x q p P ∧ 0<y q p P ∧ y q p P<7/5 := by
  obtain ⟨hRl,hRu,hPl,hPu⟩ := OutsideDE2Reference.constant_bounds hq
  have ht := trig_bracket (l := (11/50 : ℝ)) (u := (7/10 : ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hp
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig ⟨by linarith [hp.1],hp.2⟩
  have hsinlo : 109/500<Real.sin p := by norm_num at ht; linarith [ht.1]
  have hulo : -(123/500 : ℝ)<u p P := by
    dsimp [u,OutsideDE2Polynomial.Plo] at *
    linarith [hP.1]
  have huhi : u p P<141/500 := by dsimp [u]; linarith [hP.2]
  have hu2 : (u p P)^2<(141/500 : ℝ)^2 := by
    linarith [mul_pos (by linarith : 0<u p P+141/500)
      (by linarith : 0<141/500-u p P)]
  have hrad : (979/500 : ℝ)^2<q-(u p P)^2 := by
    have hqL := hq.1
    dsimp [qLow] at hqL
    linarith
  have hrad0 : 0<q-(u p P)^2 := (sq_nonneg _).trans_lt hrad
  have hzlo : (979/500 : ℝ)<z q p P := (Real.lt_sqrt (by norm_num)).2 hrad
  have hzup : z q p P≤OutsideDE2Reference.radius q :=
    Real.sqrt_le_sqrt (by linarith [sq_nonneg (u p P)])
  have hc0 : 0<Real.cos p := by linarith
  have hspos : 0<Real.sin p := by linarith
  have hxlo : 0<x q p P := by
    have h1 : (979/500 : ℝ)*(7648/10000)<z q p P*Real.cos p :=
      (mul_lt_mul_of_pos_right hzlo (by norm_num : (0:ℝ)<7648/10000)).trans_le
        (mul_le_mul_of_nonneg_left hc.le (by linarith : 0≤z q p P))
    have h2 := mul_le_mul huhi.le hs.le hs0 (by norm_num : (0:ℝ)≤141/500)
    dsimp [x]
    linarith
  have hylo : 0<y q p P := by
    have h1 : (979/500 : ℝ)*(109/500)<z q p P*Real.sin p :=
      (mul_lt_mul_of_pos_right hzlo (by norm_num : (0:ℝ)<109/500)).trans_le
        (mul_le_mul_of_nonneg_left hsinlo.le (by linarith : 0≤z q p P))
    have h2 : -(123/500 : ℝ)≤u p P*Real.cos p := by
      have hh := mul_le_mul_of_nonneg_right hulo.le hc0.le
      linarith
    dsimp [y]
    linarith
  have hyhi : y q p P<7/5 := by
    have hzR : z q p P<4947/2500 := by
      exact hzup.trans_lt (by simpa [OutsideDE2Polynomial.Rhi] using hRu)
    have h1 := mul_le_mul
      (show z q p P-Real.cos p≤607/500 by linarith)
      hs.le hs0 (by norm_num : (0:ℝ)≤607/500)
    have hP0 : 0≤P := by
      dsimp [OutsideDE2Polynomial.Plo] at hPl
      linarith [hP.1]
    have h2 := mul_le_mul hP.2 hc1 hc0.le (by norm_num : (0:ℝ)≤1/2)
    dsimp [y,u]
    linarith
  exact ⟨hulo,huhi,hzlo,hzup,hrad0,hxlo,hylo,hyhi⟩

theorem primary_derivatives {q p P : ℝ}
    (hrad : 0<q-(u p P)^2) :
    HasDerivAt (x q p) (-y q p P/z q p P) P ∧
      HasDerivAt (y q p) (x q p P/z q p P) P := by
  have hu : HasDerivAt (u p) 1 P := (hasDerivAt_id' P).sub_const (Real.sin p)
  have hz0 : z q p P≠0 := (Real.sqrt_pos.mpr hrad).ne'
  have hz : HasDerivAt (z q p) (-(u p P)/z q p P) P := by
    convert ((hasDerivAt_const P q).fun_sub (hu.fun_pow 2)).sqrt hrad.ne' using 1
    · rfl
    · rw [show Real.sqrt (q-u p P^2)=z q p P from rfl]
      field_simp
      push_cast
      ring
  constructor
  · convert (hz.mul_const (Real.cos p)).fun_sub (hu.mul_const (Real.sin p)) using 1
    · rfl
    · unfold y
      field_simp
      ring
  · convert (hz.mul_const (Real.sin p)).fun_add (hu.mul_const (Real.cos p)) using 1
    · rfl
    · unfold x
      field_simp
      ring

def betaPrimaryDerivative (q p P : ℝ) : ℝ :=
  -(y q p P*z q p P*(z q p P-Real.cos p)+
    x q p P*u p P*Real.cos p)/(z q p P)^3

theorem beta_primary_derivative {q p P : ℝ}
    (hrad : 0<q-(u p P)^2) :
    HasDerivAt (beta q p) (betaPrimaryDerivative q p P) P := by
  have hu : HasDerivAt (u p) 1 P := (hasDerivAt_id' P).sub_const (Real.sin p)
  have hz0 : z q p P≠0 := (Real.sqrt_pos.mpr hrad).ne'
  have hz : HasDerivAt (z q p) (-(u p P)/z q p P) P := by
    convert ((hasDerivAt_const P q).fun_sub (hu.fun_pow 2)).sqrt hrad.ne' using 1
    · rfl
    · rw [show Real.sqrt (q-u p P^2)=z q p P from rfl]
      field_simp
      push_cast
      ring
  convert (primary_derivatives hrad).1.fun_mul
    ((((hasDerivAt_const P (Real.cos p)).fun_div hz hz0).const_sub 1)) using 1
  · rfl
  · unfold betaPrimaryDerivative
    field_simp
    ring

theorem y_primary_mono {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    MonotoneOn (y q p) (Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro P hP
    exact (primary_derivatives (contact_bounds hq hp hP).2.2.2.2.1).2.continuousAt.continuousWithinAt
  · intro P hP
    exact (primary_derivatives (contact_bounds hq hp (Ioo_subset_Icc_self hP)).2.2.2.2.1).2
  · intro P hP
    have hb := contact_bounds hq hp (Ioo_subset_Icc_self hP)
    exact div_nonneg hb.2.2.2.2.2.1.le (by linarith [hb.2.2.1])

theorem y_gt_half {q p P : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10))
    (hP : P∈Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) :
    1/2<y q p P := by
  have hmono := y_primary_mono hq hp
  have hleft : OutsideDE2Reference.leastPrimary q∈
      Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ) := ⟨le_rfl,hP.1.trans hP.2⟩
  have hh := hmono hleft hP hP.1
  have heq : y q p (OutsideDE2Reference.leastPrimary q)=OutsideDE2Reference.y q p := rfl
  rw [heq] at hh
  exact (OutsideDE2Reference.y_gt_half hq hp).trans_le hh

theorem beta_primary_negative {q p P : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10))
    (hP : P∈Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) :
    betaPrimaryDerivative q p P<0 := by
  obtain ⟨huL,huU,hzL,hzU,hrad,hx,hy,hyU⟩ := contact_bounds hq hp hP
  have hyhalf := y_gt_half hq hp hP
  have hnorm := contact_circle hrad.le
  have hxU : x q p P<383/200 := by
    have hqU := hq.2
    dsimp [qCap] at hqU
    nlinarith
  have hc : 0<Real.cos p := transport_cos_pos (by
    rw [abs_of_nonneg (by linarith [hp.1] : 0≤p)]
    exact hp.2)
  have hzc : 479/500<z q p P-Real.cos p := by linarith [Real.cos_le_one p]
  have hyz : (979/1000 : ℝ)<y q p P*z q p P := by
    nlinarith [mul_pos (sub_pos.mpr hyhalf) (by linarith [hzL] : 0<z q p P)]
  have hmain : (9/10 : ℝ)<y q p P*z q p P*(z q p P-Real.cos p) := by
    have hm : (979/1000 : ℝ)*(479/500)<
        y q p P*z q p P*(z q p P-Real.cos p) :=
      (mul_lt_mul_of_pos_right hyz (by norm_num : (0:ℝ)<479/500)).trans_le
        (mul_le_mul_of_nonneg_left hzc.le (by positivity : 0≤y q p P*z q p P))
    norm_num at hm
    linarith
  have hpositive : 0<y q p P*z q p P*(z q p P-Real.cos p)+
      x q p P*u p P*Real.cos p := by
    by_cases hu0 : 0≤u p P
    · exact add_pos_of_pos_of_nonneg (by linarith)
        (mul_nonneg (mul_nonneg hx.le hu0) hc.le)
    · have huneg : 0< -u p P := by linarith
      have hprod : x q p P*(-u p P)<(383/200 : ℝ)*(123/500) := by
        exact (mul_lt_mul_of_pos_right hxU huneg).trans
          (mul_lt_mul_of_pos_left (by linarith : -u p P<123/500)
            (by norm_num : (0:ℝ)<383/200))
      have hcprod := mul_le_mul_of_nonneg_left (Real.cos_le_one p)
        (mul_nonneg hx.le huneg.le)
      nlinarith
  unfold betaPrimaryDerivative
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hpositive) (pow_pos (by linarith) 3)

theorem beta_primary_anti {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    AntitoneOn (beta q p) (Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) := by
  have hc : ContinuousOn (beta q p)
      (Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) := fun P hP =>
    (beta_primary_derivative (contact_bounds hq hp hP).2.2.2.2.1).continuousAt.continuousWithinAt
  have hm : MonotoneOn (fun P => -beta q p P)
      (Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg hc.neg
    · intro P hP
      exact (beta_primary_derivative (contact_bounds hq hp
        (Ioo_subset_Icc_self hP)).2.2.2.2.1).neg
    · intro P hP
      exact (neg_pos.mpr (beta_primary_negative hq hp (Ioo_subset_Icc_self hP))).le
  intro P₁ hP₁ P₂ hP₂ hle
  have hh := hm hP₁ hP₂ hle
  simp only at hh
  linarith

theorem comparison_to_reference {q p P : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10))
    (hP : P∈Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) :
    OutsideDE2Reference.y q p≤y q p P ∧
      beta q p P≤OutsideDE2Reference.beta q p := by
  have hl : OutsideDE2Reference.leastPrimary q∈
      Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ) := ⟨le_rfl,hP.1.trans hP.2⟩
  exact ⟨y_primary_mono hq hp hl hP hP.1,beta_primary_anti hq hp hl hP hP.1⟩

/-- The scalar contact formula recovers the original shifted E corner. -/
theorem recover_contact {q p P X Y : ℝ}
    (hp : p∈Icc 0 (7/10 : ℝ)) (hX : 0<X) (hY : 0<Y)
    (hcircle : X^2+Y^2=q) (hcontact : Y*Real.cos p-(X-1)*Real.sin p=P) :
    x q p P=X ∧ y q p P=Y ∧
      OutsideE.contactSpeed (X-1/2) (Y-1/2) (Y/X) p=beta q p P := by
  let Z := X*Real.cos p+Y*Real.sin p
  have ht := transport_trig hp
  have hc : 0<Real.cos p := by linarith [ht.1]
  have hs : 0≤Real.sin p := ht.2.2.1
  have hZ : 0<Z := add_pos_of_pos_of_nonneg (mul_pos hX hc) (mul_nonneg hY.le hs)
  have hU : u p P=Y*Real.cos p-X*Real.sin p := by dsimp [u]; linarith
  have hnorm : Z^2+(u p P)^2=q := by
    rw [hU]
    have hid : Z^2+(Y*Real.cos p-X*Real.sin p)^2=
        (X^2+Y^2)*(Real.sin p^2+Real.cos p^2) := by dsimp [Z]; ring
    rw [hid,Real.sin_sq_add_cos_sq,hcircle]
    ring
  have hroot : z q p P=Z := by
    unfold z
    rw [show q-(u p P)^2=Z^2 by linarith,Real.sqrt_sq_eq_abs,abs_of_pos hZ]
  have hx : x q p P=X := by
    rw [x,hroot,hU]
    calc
      _=X*(Real.sin p^2+Real.cos p^2) := by dsimp [Z]; ring
      _=X := by rw [Real.sin_sq_add_cos_sq]; ring
  have hy : y q p P=Y := by
    rw [y,hroot,hU]
    calc
      _=Y*(Real.sin p^2+Real.cos p^2) := by dsimp [Z]; ring
      _=Y := by rw [Real.sin_sq_add_cos_sq]; ring
  have hden : 0<Real.cos p+(Y/X)*Real.sin p :=
    add_pos_of_pos_of_nonneg hc (mul_nonneg (div_nonneg hY.le hX.le) hs)
  refine ⟨hx,hy,?_⟩
  unfold beta OutsideE.contactSpeed
  rw [hx,hroot]
  dsimp [Z] at hZ ⊢
  field_simp [hX.ne',hZ.ne',hden.ne']
  ring

theorem outer_contact_speed_lt {q p n a b : ℝ} {D H : SignedPoint}
    (hq : qLow≤q∧q≤qCap)
    (hHs : H.Sorted) (hHo : H.Outer q) (hHa : H.a<1)
    (hDs : D.Sorted) (hDy : D.y≤0) (hDo : D.Outer q)
    (ha : 0<a) (hb : 0≤b) (_hsort : b≤a)
    (hcircle : (a+1/2)^2+(b+1/2)^2=q)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) (hn : n∈Icc 0 (7/10 : ℝ))
    (hEH : H.a-1/2+(a-1/2)*Real.sin p-(b+1/2)*Real.cos p=0)
    (hDE : (D.a-1/2)*Real.cos n+(D.y-1/2)*Real.sin n+b-1/2=0) :
    OutsideE.contactSpeed a b ((b+1/2)/(a+1/2)) p<
      (D.a-1/2)*Real.sin n+(1/2-D.y)*Real.cos n := by
  let P := H.a-1/2
  have hP : P∈Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ) := by
    have hdiag := (SignedPoint.outer_bounds hHs hHo).1
    dsimp [OutsideDE2Reference.leastPrimary,diagonalCoordinate,P] at *
    constructor <;> linarith
  have hrecover := recover_contact ⟨by linarith [hp.1],hp.2⟩
    (show 0<a+1/2 by linarith) (show 0<b+1/2 by linarith) hcircle
    (show (b+1/2)*Real.cos p-((a+1/2)-1)*Real.sin p=P by dsimp [P]; linarith)
  have hcompare := comparison_to_reference hq hp hP
  have hactual := contact_bounds hq hp hP
  have href := contact_bounds hq hp
    (show OutsideDE2Reference.leastPrimary q∈
      Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ) from ⟨le_rfl,hP.1.trans hP.2⟩)
  have hYref : OutsideDE2Reference.y q p∈Icc (1/2 : ℝ) (7/5) :=
    ⟨(OutsideDE2Reference.y_gt_half hq hp).le,href.2.2.2.2.2.2.2.le⟩
  have hYactual : b+1/2∈Icc (1/2 : ℝ) (7/5) := by
    rw [← hrecover.2.1]
    exact ⟨(y_gt_half hq hp hP).le,hactual.2.2.2.2.2.2.2.le⟩
  have hmono := OutsideDContact.gain_mono_tangent hq.1 hYref hYactual
    (show (7/10 : ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)
    (by simpa only [hrecover.2.1] using hcompare.1)
  have hreference : OutsideDE2Reference.beta q p<
      OutsideDContact.gain q (OutsideDE2Reference.y q p) (7/10) := by
    simpa [OutsideDContact.gain,OutsideDContact.root,OutsideDContact.ell,
      OutsideDE2Reference.root,OutsideDE2Reference.ell] using
      OutsideDE2Reference.reference_gap hq hp
  have hDcap := OutsideDContact.gain_ge_cap hq.1 hYactual hn
  have hDactual := OutsideDContact.actual_contact_gain hDs hDy hDo hn hDE
  have hspeed : OutsideE.contactSpeed a b ((b+1/2)/(a+1/2)) p=beta q p P := by
    simpa using hrecover.2.2
  rw [hspeed,hDactual]
  exact hcompare.2.trans_lt (hreference.trans_le (hmono.trans hDcap))

theorem flat_contact_speed_lt {q p n b : ℝ} {D : SignedPoint}
    (hq : qLow≤q) (hDs : D.Sorted) (hDy : D.y≤0) (hDo : D.Outer q)
    (hb : b∈Ico 0 (9/40 : ℝ))
    (hp : p∈Icc 0 (7/10 : ℝ)) (hn : n∈Icc 0 (7/10 : ℝ))
    (hDE : (D.a-1/2)*Real.cos n+(D.y-1/2)*Real.sin n+b-1/2=0) :
    OutsideE.contactSpeed (7/12) b 0 p<
      (D.a-1/2)*Real.sin n+(1/2-D.y)*Real.cos n := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hp
  have hc0 : 0<Real.cos p := by linarith
  have hratio : Real.sin p/Real.cos p<843/1000 := by
    apply (div_lt_iff₀ hc0).2
    nlinarith
  have hratio0 := div_nonneg hs0 hc0.le
  have hspeed : OutsideE.contactSpeed (7/12) b 0 p<139/200 := by
    have hid : OutsideE.contactSpeed (7/12) b 0 p=
        1/12+(b+1/2)*(Real.sin p/Real.cos p) := by
      dsimp [OutsideE.contactSpeed]
      field_simp [hc0.ne']
      ring
    rw [hid]
    have hm := mul_le_mul (show b+1/2≤29/40 by linarith [hb.2]) hratio.le
      hratio0 (by norm_num : (0:ℝ)≤29/40)
    nlinarith
  have hgain := OutsideDContact.gain_gt_core_speed hq
    (show b+1/2∈Icc (1/2 : ℝ) (7/5) by constructor <;> linarith [hb.1,hb.2]) hn
  rw [OutsideDContact.actual_contact_gain hDs hDy hDo hn hDE]
  linarith

end OutsideDE2Comparison

namespace OutsideE

theorem ArcSource.de2_contact_speed_lt {q b p n : ℝ} {E D H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind) (hq : qLow≤q∧q≤qCap)
    (hHs : H.Sorted) (hHo : H.Outer q) (hHa : H.a<1)
    (hDs : D.Sorted) (hDy : D.y≤0) (hDo : D.Outer q)
    (hb : b∈Icc 0 (-E.y))
    (hp : p∈Icc (11/50 : ℝ) (7/10)) (hn : n∈Icc 0 (7/10 : ℝ))
    (hEH : ehSlack kind q H p b=0)
    (hDE : (D.a-1/2)*Real.cos n+(D.y-1/2)*Real.sin n+b-1/2=0) :
    contactSpeed (kind.primary q b) b (kind.slope q b) p<
      (D.a-1/2)*Real.sin n+(1/2-D.y)*Real.cos n := by
  cases kind with
  | flatCore =>
    exact OutsideDE2Comparison.flat_contact_speed_lt hq.1 hDs hDy hDo
      ⟨hb.1,hb.2.trans_lt (I.flat rfl).2⟩
      ⟨by linarith [hp.1],hp.2⟩ hn hDE
  | outerCircle =>
    have hg := I.geometry hq.1 hb
    have hroot : 0<Real.sqrt (q-(b+1/2)^2) := by
      have hh := hg.2.2.2.2.2.1
      dsimp [ArcKind.primary] at hh
      linarith
    have hrad := Real.sqrt_pos.mp hroot
    have hcircle : (ArcKind.outerCircle.primary q b+1/2)^2+(b+1/2)^2=q := by
      dsimp [ArcKind.primary]
      nlinarith [Real.sq_sqrt hrad.le]
    have hslope : ArcKind.outerCircle.slope q b=
        (b+1/2)/(ArcKind.outerCircle.primary q b+1/2) := by
      simp [ArcKind.slope,ArcKind.primary]
    rw [hslope]
    exact OutsideDE2Comparison.outer_contact_speed_lt hq hHs hHo hHa hDs hDy hDo
      (by linarith [hg.2.2.2.2.2.1]) hb.1 hg.2.2.2.2.2.2 hcircle hp hn hEH hDE

end OutsideE
end SquaresInCircles.Eight
end
end
end

section
/-!
## Compact same-q outside endpoint with the original DE2 witness

The two contact derivatives, including the outer E comparison proved from the whole-interval
polynomial, rule out an interior compact minimum (`de2_endpoint`). The endpoint keeps the
original DE2 axis, not DE3. H and D are on the original q-circle, as those comparisons
require.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace OutsideE

structure DE2Endpoint (q : ℝ) (D E H : SignedPoint) (n p : ℝ) where
  point : SignedPoint
  movement : ℝ
  movement_nonneg : 0≤ movement
  movement_le_n : movement≤n
  error_positive : 0<p-movement
  sorted : point.Sorted
  contained : point.Contained q
  core : point.AvoidsCore
  radial : point.Boundary q
  nonpos : point.y≤0
  tangent_nonincrease : |point.y|≤|E.y|
  circle_nonincrease : point.circle≤E.circle
  DE2 : quarterFeasible D point (-(n-movement)) 2
  EH1 : quarterFeasible point H (p-movement) 1
  terminal : quarterFeasible point H (p-movement) 0 ∨
    p-movement≤11/50 ∨ (n-movement=0 ∧ 11/50<p-movement)

theorem de2_endpoint {q n p : ℝ} {D E H : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHy : 211/250<H.y) (hHa : H.a<1) (hHo : H.Outer q)
    (hDs : D.Sorted) (hDy : D.y≤0) (hDo : D.Outer q)
    (hEs : E.Sorted) (hEy : E.y≤0) (hEr : E.Boundary q)
    (hn : n∈Ioc 0 (7/10 : ℝ)) (hp : p∈Ioc (11/50 : ℝ) (7/10 : ℝ))
    (hDE : quarterFeasible D E (-n) 2) (hEH : quarterFeasible E H p 1) :
    Nonempty (DE2Endpoint q D E H n p) := by
  obtain ⟨kind,I⟩ := arcSource_of_boundary hEs hEy hEr hHa
    ⟨by linarith [hp.1],hp.2⟩ hEH
  let α := p-n
  let l := max (11/50 : ℝ) α
  let f := ehSlack kind q H
  let g := de2Slack D α
  have hDa : 1/2<D.a := by
    have hd := (SignedPoint.outer_bounds hDs hDo).1
    have hlow := (uniform_circle_reserves hqL hqU).1
    linarith
  have hlp : l<p := max_lt_iff.mpr ⟨hp.1,by dsimp [α]; linarith [hn.1]⟩
  have hlshort : 11/50≤l := le_max_left _ _
  have hlα : α≤l := le_max_right _ _
  have hparams {x : ℝ} (hx : x∈Icc l p) :
      x∈Icc (11/50 : ℝ) (7/10 : ℝ) ∧ x-α∈Icc 0 (7/10 : ℝ) := by
    constructor
    · exact ⟨hlshort.trans hx.1,hx.2.trans hp.2⟩
    · constructor
      · linarith [hx.1]
      · dsimp [α]; linarith [hx.2,hn.2]
  have hprim := kind.continuous_primary q
  have hcf : Continuous (fun z : ℝ×ℝ => f z.1 z.2) := by
    dsimp [f,ehSlack]
    fun_prop
  have hcg : Continuous (fun z : ℝ×ℝ => g z.1 z.2) := by
    dsimp [g,de2Slack]
    fun_prop
  let S : Set (ℝ×ℝ) :=
    ((Icc l p ×ˢ Icc 0 (-E.y)) ∩ {z | 0≤f z.1 z.2}) ∩ {z | 0≤g z.1 z.2}
  have hcompact : IsCompact S :=
    ((isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const hcf)).inter_right
      (isClosed_le continuous_const hcg)
  have hstart : (p,-E.y)∈S := by
    refine ⟨⟨⟨⟨hlp.le,le_rfl⟩,⟨neg_nonneg.mpr hEy,le_rfl⟩⟩,?_⟩,?_⟩
    · dsimp [f]
      rw [ehSlack_actual kind q H (-E.y) ⟨by linarith [hp.1],hp.2⟩,I.initial]
      exact sub_nonneg.mpr hEH
    · dsimp [g]
      rw [de2Slack_actual kind q α D (-E.y)
        (by dsimp [α]; simpa using ⟨hn.1.le,hn.2⟩),I.initial]
      simpa [α] using sub_nonneg.mpr hDE
  obtain ⟨z,hz,hmin⟩ := hcompact.exists_isMinOn ⟨(p,-E.y),hstart⟩
    continuous_fst.continuousOn
  let m := z.1
  let b := z.2
  have hm : m∈Icc l p := hz.1.1.1
  have hb : b∈Icc 0 (-E.y) := hz.1.1.2
  have hf : 0≤f m b := hz.1.2
  have hg : 0≤g m b := hz.2
  have hangles := hparams hm
  have hpm : m∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hangles.1.1],hangles.1.2⟩
  have hstop : quarterFeasible (kind.point q b) H m 0 ∨ m=l := by
    by_cases hEH0 : quarterFeasible (kind.point q b) H m 0
    · exact Or.inl hEH0
    right
    apply le_antisymm _ hm.1
    by_contra! hlm
    have hnear : ∃ z' : ℝ×ℝ, z'.1∈Icc l p ∧ z'.2∈Icc 0 (-E.y) ∧
        0≤f z'.1 z'.2 ∧ 0≤g z'.1 z'.2 ∧ z'.1<m := by
      by_cases hfpos : 0<f m b
      · have hDpos := OutsideDContact.fixed_rate_positive hDa hDy hangles.2
        exact feasible_shift_left ⟨hlm,hm.2⟩ hb (le_rfl : (0:ℝ)≤0) (Or.inl rfl)
          (I.eh_direction_derivative (H := H) (p := m) (β := 0) hqL hb)
          (de2_direction_derivative D α b m 0)
          hf hg (Or.inl hfpos) (Or.inr (by simpa using hDpos))
      · have hfzero : f m b=0 := le_antisymm (le_of_not_gt hfpos) hf
        have hbpos : 0<b := by
          apply lt_of_le_of_ne hb.1
          intro hbzero
          have hcontact : ehSlack kind q H m 0=0 := by simpa [f,← hbzero] using hfzero
          exact hEH0 (by simpa [← hbzero] using
            I.zero_contact_eh0 hqL hqU hHs hHy hHo hangles.1 hcontact)
        let a := kind.primary q b
        let v := kind.slope q b
        let β₀ := contactSpeed a b v m
        let den := Real.cos m+v*Real.sin m
        let U := (a-1/2)*Real.cos m+(b+1/2)*Real.sin m
        let V := (D.a-1/2)*Real.sin (m-α)+(1/2-D.y)*Real.cos (m-α)
        have hgeom := I.geometry hqL hb
        have hder := I.derivative hqL hb
        have hβ := contactSpeed_positive hgeom.2.2.2.2.2.1 hb.1 hder.2.1 hpm
        have hidentity : β₀*den=U := by
          dsimp only [β₀,contactSpeed,den,U]
          exact div_mul_cancel₀ _ hβ.1.ne'
        by_cases hgpos : 0<g m b
        · have hEpos : 0<(β₀+1)*den-U := by nlinarith
          exact feasible_shift_left ⟨hlm,hm.2⟩ hb (by linarith [hβ.2]) (Or.inr hbpos)
            (I.eh_direction_derivative (H := H) (p := m) (β := β₀+1) hqL hb)
            (de2_direction_derivative D α b m (β₀+1))
            hf hg (Or.inr hEpos) (Or.inl hgpos)
        · have hgzero : g m b=0 := le_antisymm (le_of_not_gt hgpos) hg
          have hgap : β₀<V := I.de2_contact_speed_lt ⟨hqL,hqU⟩ hHs hHo hHa
            hDs hDy hDo hb hangles.1 hangles.2 hfzero hgzero
          let β := (β₀+V)/2
          have hβpos : 0<β := by dsimp [β]; linarith [hβ.2]
          have hβlower : β₀<β := by dsimp [β]; linarith
          have hEpos : 0<β*den-U := by
            have hh := mul_pos (sub_pos.mpr hβlower) hβ.1
            nlinarith
          have hDpos : 0<V-β := by dsimp [β]; linarith
          exact feasible_shift_left ⟨hlm,hm.2⟩ hb hβpos.le (Or.inr hbpos)
            (I.eh_direction_derivative (H := H) (p := m) (β := β) hqL hb)
            (de2_direction_derivative D α b m β)
            hf hg (Or.inr hEpos) (Or.inr hDpos)
    obtain ⟨z',hz'p,hz'b,hz'f,hz'g,hz'lt⟩ := hnear
    have hz'S : z'∈S := ⟨⟨⟨hz'p,hz'b⟩,hz'f⟩,hz'g⟩
    have hh : m≤z'.1 := hmin hz'S
    linarith
  have hgeometry := I.geometry hqL hb
  have hEHfinal : quarterFeasible (kind.point q b) H m 1 := by
    have hh := hf
    dsimp [f] at hh
    rw [ehSlack_actual kind q H b hpm] at hh
    exact sub_nonneg.mp hh
  have hDEfinal : quarterFeasible D (kind.point q b) (-(n-(p-m))) 2 := by
    have hh := hg
    dsimp [g] at hh
    rw [de2Slack_actual kind q α D b hangles.2] at hh
    have heq : m-α=n-(p-m) := by dsimp [α]; ring
    have hh2 := sub_nonneg.mp hh
    rw [heq] at hh2
    unfold quarterFeasible
    exact hh2
  have hterminal : quarterFeasible (kind.point q b) H m 0 ∨
      m≤11/50 ∨ (n-(p-m)=0 ∧ 11/50<m) := by
    rcases hstop with hstop | hstop
    · exact Or.inl hstop
    · by_cases hmshort : m≤11/50
      · exact Or.inr (Or.inl hmshort)
      · have hmα : m=α := by
          have hlEq : l=α := by
            apply max_eq_right
            by_contra! hα
            have hlEq : l=11/50 := max_eq_left hα.le
            linarith
          exact hstop.trans hlEq
        exact Or.inr (Or.inr ⟨by dsimp [α] at hmα; linarith,lt_of_not_ge hmshort⟩)
  exact ⟨{
    point := kind.point q b
    movement := p-m
    movement_nonneg := sub_nonneg.mpr hm.2
    movement_le_n := by dsimp [α] at hlα; linarith [hm.1]
    error_positive := by linarith [hangles.1.1]
    sorted := hgeometry.1
    contained := hgeometry.2.1
    core := hgeometry.2.2.1
    radial := hgeometry.2.2.2.1
    nonpos := by dsimp [ArcKind.point]; linarith [hb.1]
    tangent_nonincrease := by
      simp only [ArcKind.point,abs_neg,abs_of_nonneg hb.1,abs_of_nonpos hEy]
      exact hb.2
    circle_nonincrease := hgeometry.2.2.2.2.1
    DE2 := hDEfinal
    EH1 := by simpa using hEHfinal
    terminal := by simpa using hterminal }⟩

end OutsideE
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace OutsideE

/-- Common geometric output of the two compact constructions. The parameter `j` is the original
DE owner. -/
structure CycleEndpoint (q : ℝ) (C : SignedCycle) (j : Fin 4) where
  point : SignedPoint
  movement : ℝ
  movement_nonneg : 0≤ movement
  movement_le_n : movement≤C.theta D-C.theta E
  error_positive : 0<C.theta H-C.theta E-movement
  sorted : point.Sorted
  contained : point.Contained q
  core : point.AvoidsCore
  radial : point.Boundary q
  nonpos : point.y≤0
  tangent_nonincrease : |point.y|≤|(C.point E).y|
  circle_nonincrease : point.circle≤(C.point E).circle
  DE : quarterFeasible (C.point D) point (-(C.theta D-C.theta E-movement)) j
  EH1 : quarterFeasible point (C.point H) (C.theta H-C.theta E-movement) 1
  terminal : quarterFeasible point (C.point H) (C.theta H-C.theta E-movement) 0 ∨
    C.theta H-C.theta E-movement≤11/50 ∨
      (C.theta D-C.theta E-movement=0 ∧ 11/50<C.theta H-C.theta E-movement)

def DE2Endpoint.toCycle {q : ℝ} {C : SignedCycle}
    (O : DE2Endpoint q (C.point D) (C.point E) (C.point H)
      (C.theta D-C.theta E) (C.theta H-C.theta E)) : CycleEndpoint q C 2 where
  point := O.point
  movement := O.movement
  movement_nonneg := O.movement_nonneg
  movement_le_n := O.movement_le_n
  error_positive := O.error_positive
  sorted := O.sorted
  contained := O.contained
  core := O.core
  radial := O.radial
  nonpos := O.nonpos
  tangent_nonincrease := O.tangent_nonincrease
  circle_nonincrease := O.circle_nonincrease
  DE := O.DE2
  EH1 := O.EH1
  terminal := O.terminal

def DE3Endpoint.toCycle {q : ℝ} {C : SignedCycle}
    (O : DE3Endpoint q (C.point D) (C.point E) (C.point H)
      (C.theta D-C.theta E) (C.theta H-C.theta E)) : CycleEndpoint q C 3 where
  point := O.point
  movement := O.movement
  movement_nonneg := O.movement_nonneg
  movement_le_n := O.movement_le_n
  error_positive := O.error_positive
  sorted := O.sorted
  contained := O.contained
  core := O.core
  radial := O.radial
  nonpos := O.nonpos
  tangent_nonincrease := O.tangent_nonincrease
  circle_nonincrease := O.circle_nonincrease
  DE := O.DE3
  EH1 := O.EH1
  terminal := O.terminal

namespace CycleEndpoint

variable {q : ℝ} {C : SignedCycle} {j : Fin 4}

def cycle (O : CycleEndpoint q C j) : SignedCycle :=
  replacePoint C E O.point (C.theta E+O.movement)

theorem unchanged (O : CycleEndpoint q C j) (i : Vertex) (hi : i≠E) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i := by
  simp [cycle,replacePoint,hi]

theorem DE_actual (O : CycleEndpoint q C j) : O.cycle.Feasible D j := by
  have heq : C.theta E+O.movement-C.theta D=
      -(C.theta D-C.theta E-O.movement) := by ring
  have h := O.DE
  rw [← heq] at h
  simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,D,E,quarterFeasible,sub_nonneg] using h


theorem EH_actual (O : CycleEndpoint q C j) (k : Fin 4) :
    O.cycle.Feasible E k ↔
      quarterFeasible O.point (C.point H) (C.theta H-C.theta E-O.movement) k := by
  have heq : C.theta H-(C.theta E+O.movement)=
      C.theta H-C.theta E-O.movement := by ring
  rw [← heq]
  simp [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,H,E,quarterFeasible,sub_nonneg]


theorem other_feasible (O : CycleEndpoint q C j) (i : Vertex)
    (hiD : i≠D) (hiE : i≠E) (k : Fin 4) :
    O.cycle.Feasible i k ↔ C.Feasible i k := by
  have hn : next i≠E := by revert hiD; fin_cases i <;> decide
  exact SignedCycle.replacePoint_other_feasible hiE hn


theorem frame_range (O : CycleEndpoint q C j) :
    C.theta E+O.movement∈Icc (min (C.theta E) (C.theta D))
      (max (C.theta E) (C.theta D)) := by
  have hED : C.theta E≤C.theta D := by
    linarith [O.movement_nonneg,O.movement_le_n]
  rw [min_eq_left hED,max_eq_right hED]
  constructor <;> linarith [O.movement_nonneg,O.movement_le_n]

theorem necessary (O : CycleEndpoint q C j) (hn : C.Necessary q) :
    O.cycle.Necessary q :=
  SignedCycle.necessary_replace_clamped (v := E) (a := E) (b := D)
    hn O.sorted O.contained O.core (Or.inr O.frame_range)

theorem normal (O : CycleEndpoint q C j) (ha : C.NormalAnchors) :
    O.cycle.NormalAnchors := by
  constructor
  · rw [(O.unchanged H (by decide)).1]; exact ha.H_nonneg
  · rw [(O.unchanged A (by decide)).1]; exact ha.A_nonneg
  · rw [(O.unchanged B (by decide)).1]; exact ha.B_nonpos
  · rw [(O.unchanged D (by decide)).1]; exact ha.D_nonpos

def witnesses (w : C.Witnesses) (O : CycleEndpoint q C (w.owner D)) :
    O.cycle.Witnesses where
  owner := Function.update w.owner E 1
  feasible i := by
    by_cases hiE : i=E
    · subst i
      simpa using (O.EH_actual 1).2 O.EH1
    · by_cases hiD : i=D
      · subst i
        simpa [E,D] using O.DE_actual
      · simpa [Function.update_of_ne hiE] using
          (O.other_feasible i hiD hiE (w.owner i)).2 (w.feasible i)
  allowed i := by
    by_cases hiE : i=E
    · subst i
      norm_num [SignedCycle.normalOwners,E]
    · simpa [Function.update_of_ne hiE] using w.allowed i

theorem zero_signs (w : C.Witnesses) (O : CycleEndpoint q C (w.owner D))
    (hz : C.ZeroSignImplications w) : O.cycle.ZeroSignImplications (O.witnesses w) := by
  constructor
  · intro hj
    have hj' : w.owner H=2 := by simpa [witnesses,H,E] using hj
    rw [(O.unchanged G (by decide)).1]
    exact hz.HG_canceling hj'
  · intro hj
    have hj' : w.owner T=0 := by simpa [witnesses,T,E] using hj
    rw [(O.unchanged T (by decide)).1]
    exact hz.TD_canceling hj'

theorem ordered (w : C.Witnesses) (O : CycleEndpoint q C (w.owner D))
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (hz : C.ZeroSignImplications w) : O.cycle.Ordered :=
  SignedCycle.normal_necessary_ordered (O.necessary hn) hq (O.normal ha)
    (O.witnesses w) (O.zero_signs w hz)

theorem strict_spread (O : CycleEndpoint q C j) (hs : C.StrictSpread) :
    O.cycle.StrictSpread :=
  SignedCycle.strictSpread_replace_clamped (v := E) (a := E) (b := D)
    (p := O.point) hs (Or.inr O.frame_range)

theorem variations (O : CycleEndpoint q C j) :
    positiveVariation C.theta-positiveVariation O.cycle.theta=O.movement ∧
      negativeVariation C.theta-negativeVariation O.cycle.theta=O.movement := by
  have hDEold : positivePart (C.theta E-C.theta D)=0 :=
    max_eq_right (by linarith [O.movement_nonneg,O.movement_le_n])
  have hDEnew : positivePart (C.theta E+O.movement-C.theta D)=0 :=
    max_eq_right (by linarith [O.movement_le_n])
  have hEHold : positivePart (C.theta H-C.theta E)=C.theta H-C.theta E :=
    max_eq_left (by linarith [O.error_positive,O.movement_nonneg])
  have hEHnew : positivePart (C.theta H-(C.theta E+O.movement))=
      C.theta H-(C.theta E+O.movement) :=
    max_eq_left (by linarith [O.error_positive])
  have hle : O.movement≤C.theta 5-C.theta 6 := O.movement_le_n
  have hpos : 0<C.theta 0-C.theta 6-O.movement := O.error_positive
  have hm0 := O.movement_nonneg
  have e1 : positivePart (C.theta 6-C.theta 5)=0 := max_eq_right (by linarith)
  have e2 : positivePart (C.theta 6+O.movement-C.theta 5)=0 := max_eq_right (by linarith)
  have e3 : positivePart (C.theta 0-C.theta 6)=C.theta 0-C.theta 6 :=
    max_eq_left (by linarith)
  have e4 : positivePart (C.theta 0-(C.theta 6+O.movement))=C.theta 0-(C.theta 6+O.movement) :=
    max_eq_left (by linarith)
  have hp : positiveVariation C.theta-positiveVariation O.cycle.theta=O.movement := by
    simp [positiveVariation,Fin.sum_univ_succ,delta,next,cycle,replacePoint,
      E,Function.update_apply]
    linarith [e1,e2,e3,e4]
  exact ⟨hp,by
    simpa only [← variations_equal C.theta,← variations_equal O.cycle.theta] using hp⟩


theorem anchor_nonincrease (O : CycleEndpoint q C j) :
    AnchorNonincrease C O.cycle := by
  intro i hi
  by_cases hiE : i=E
  · subst i
    simpa [cycle,replacePoint] using O.circle_nonincrease
  · rw [(O.unchanged i hiE).1]

theorem radial_all (O : CycleEndpoint q C j) (hr : ∀ i, (C.point i).Boundary q) :
    ∀ i, (O.cycle.point i).Boundary q := by
  intro i
  by_cases hiE : i=E
  · subst i
    simpa [cycle,replacePoint] using O.radial
  · rw [(O.unchanged i hiE).1]
    exact hr i

theorem terminal_actual (O : CycleEndpoint q C j) :
    O.cycle.Feasible E 0 ∨
      |O.cycle.theta H-O.cycle.theta E|≤11/50 ∨
      (O.cycle.theta E=O.cycle.theta D ∧ 11/50<C.theta H-C.theta D) := by
  rcases O.terminal with hh | hh | ⟨hn,hp⟩
  · exact Or.inl ((O.EH_actual 0).2 hh)
  · right; left
    have heq : O.cycle.theta H-O.cycle.theta E=
        C.theta H-C.theta E-O.movement := by
      simp [cycle,replacePoint,H,E]
      ring
    rw [heq,abs_of_pos O.error_positive]
    exact hh
  · right; right
    constructor
    · have hn' : C.theta 5-C.theta 6-O.movement=0 := hn
      simp [cycle,replacePoint,D,E]
      linarith
    · linarith


/-- All original outer anchors are kept; the new E point is on its original radial arc, and the
signed budgets are lower (`variations`). -/
def boundaryInput (I : SignedCycle.NormalizedBoundaryInput q) (hq : q≤qCap)
    (O : CycleEndpoint q I.cycle (I.witnesses.owner D)) :
    SignedCycle.NormalizedBoundaryInput q where
  cycle := O.cycle
  necessary := O.necessary I.necessary
  ordered := O.ordered I.witnesses I.necessary hq I.anchors_normal I.zero_signs
  strict_spread := O.strict_spread I.strict_spread
  positive_variation := by
    have hvar := O.variations.1
    linarith [I.positive_variation,O.movement_nonneg]
  negative_variation := by
    have hvar := O.variations.2
    linarith [I.negative_variation,O.movement_nonneg]
  radial := O.radial_all I.radial
  anchors_outer := by
    intro i hi
    have hiE : i≠E := by rintro rfl; exact absurd hi (by decide)
    rw [(O.unchanged i hiE).1]
    exact I.anchors_outer i hi
  anchors_normal := O.normal I.anchors_normal
  witnesses := O.witnesses I.witnesses
  zero_signs := O.zero_signs I.witnesses I.zero_signs
  E_nonpos := by simpa [cycle,replacePoint] using O.nonpos

end CycleEndpoint

/-- The original owner matrix has exactly its two compact leaves. -/
theorem cycle_endpoint {q : ℝ} (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHy : 211/250<(I.cycle.point H).y) (hHa : (I.cycle.point H).a<1)
    (hn : I.cycle.theta E<I.cycle.theta D)
    (hp : 11/50<I.cycle.theta H-I.cycle.theta E)
    (hEH : I.cycle.Feasible E 1) :
    Nonempty (CycleEndpoint q I.cycle (I.witnesses.owner D)) := by
  have hnrange : I.cycle.theta D-I.cycle.theta E∈Ioc 0 (7/10 : ℝ) :=
    ⟨sub_pos.mpr hn,(le_abs_self _).trans (I.necessary.spread D E)⟩
  have hprange : I.cycle.theta H-I.cycle.theta E∈Ioc (11/50 : ℝ) (7/10 : ℝ) :=
    ⟨hp,(le_abs_self _).trans (I.necessary.spread H E)⟩
  have hHouter := I.anchors_outer H (by simp)
  have hDouter := I.anchors_outer D (by simp)
  have hEH' : quarterFeasible (I.cycle.point E) (I.cycle.point H)
      (I.cycle.theta H-I.cycle.theta E) 1 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  have hDE' : quarterFeasible (I.cycle.point D) (I.cycle.point E)
      (-(I.cycle.theta D-I.cycle.theta E)) (I.witnesses.owner D) := by
    have heq : -(I.cycle.theta D-I.cycle.theta E)=
        I.cycle.theta E-I.cycle.theta D := by ring
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,D,E,quarterFeasible,sub_nonneg,heq] using I.witnesses.feasible D
  have hj : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
    simpa [SignedCycle.normalOwners,D] using I.witnesses.allowed D
  rcases hj with hj | hj
  · rw [hj]
    obtain ⟨O⟩ := de2_endpoint hqL hqU (I.necessary.sorted H) hHy hHa hHouter
      (I.necessary.sorted D) I.anchors_normal.D_nonpos hDouter
      (I.necessary.sorted E) I.E_nonpos (I.radial E) hnrange hprange
      (by simpa [hj] using hDE') hEH'
    exact ⟨O.toCycle⟩
  · rw [hj]
    obtain ⟨O⟩ := de3_endpoint hqL hqU (I.necessary.sorted H) hHy hHa hHouter
      (I.necessary.sorted E) I.E_nonpos (I.radial E) hnrange hprange
      (by simpa [hj] using hDE') hEH'
    exact ⟨O.toCycle⟩

end OutsideE
end SquaresInCircles.Eight
end
end
end
