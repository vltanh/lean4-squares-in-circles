module

public import SquaresInCircles.Eight.Owners.BT.CoreDE3Support
public import SquaresInCircles.Eight.Owners.BT.ErrorComparisons

/-!
# Eight squares: the complete effective-error cap for original AB0 and negative BT1

When 0 <= v <= z, the effective error is r=z-v.  The two actual
projections cancel the original signed B coordinate exactly.  Their
remaining trigonometric line increases on the entire segment from
zero to v and begins at the high-primary prefix value.
-/

section
/-!
## The exact high-primary cap supplied by a negative BT1 prefix

The domain is the original corner disk with primary at least the
explicit cap.  The cap increases, every feasible error is below one
third, and its radical remains positive on the entire preceding
interval.  These facts are derived from the necessary prefix bound;
no optimizer or transition point is assumed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.HighPrimary

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def L : ℝ := 3/2-c0
def K : ℝ := 13/12
def «prefix» (z : ℝ) : ℝ := 3/2+(1/2)/Real.cos z+K*Real.sin z/Real.cos z
def X (z : ℝ) : ℝ := 1+L*Real.cos z+K*Real.sin z
def Xd (z : ℝ) : ℝ := K*Real.cos z-L*Real.sin z
def Z (z : ℝ) : ℝ := Real.sqrt (Q0-(X z)^2)
def OnCap (z : ℝ) : Prop := z∈Icc 0 frameCap ∧ (X z)^2+1/4≤Q0

theorem L_bounds : (3/5:ℝ)<L ∧ L<601/1000 := by
  dsimp [L]
  constructor <;> linarith [c0_bounds.1,c0_bounds.2]

theorem X_deriv (z : ℝ) : HasDerivAt X (Xd z) z := by
  have hc : HasDerivAt (fun y => L*Real.cos y) (L*(-Real.sin z)) z :=
    (Real.hasDerivAt_cos z).const_mul L
  have hs : HasDerivAt (fun y => K*Real.sin y) (K*Real.cos z) z :=
    (Real.hasDerivAt_sin z).const_mul K
  have h := ((hasDerivAt_const z (1:ℝ)).fun_add hc).fun_add hs
  unfold X Xd
  exact h.congr_deriv (by ring)

theorem Xd_deriv (z : ℝ) : HasDerivAt Xd (1-X z) z := by
  have hc : HasDerivAt (fun y => K*Real.cos y) (K*(-Real.sin z)) z :=
    (Real.hasDerivAt_cos z).const_mul K
  have hs : HasDerivAt (fun y => L*Real.sin y) (L*Real.cos z) z :=
    (Real.hasDerivAt_sin z).const_mul L
  have h := hc.fun_sub hs
  unfold X Xd
  exact h.congr_deriv (by ring)

theorem Xd_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<Xd z := by
  have tr := transport_trig hz
  have hprod := mul_le_mul L_bounds.2.le
    (show Real.sin z≤13/20 by linarith [tr.2.2.2.1]) tr.2.2.1
    (by norm_num : (0:ℝ)≤601/1000)
  dsimp [Xd,K]
  nlinarith only [tr.1,hprod]

theorem X_monotone : MonotoneOn X (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun z _ => (X_deriv z).continuousAt.continuousWithinAt
  · exact fun z _ => X_deriv z
  · exact fun z hz => (Xd_positive (Ioo_subset_Icc_self hz)).le

theorem X_lower {z : ℝ} (hz : z∈Icc 0 frameCap) : (8/5:ℝ)<X z := by
  have hm := X_monotone (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz hz.1
  simp only [X,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero] at hm ⊢
  linarith [L_bounds.1]

theorem cap_X_upper {z : ℝ} (hz : OnCap z) : X z<383/200 := by
  have hl := X_lower hz.1
  have hc := hz.2
  norm_num [Q0] at hc
  nlinarith

theorem X_third_lower : (383/200:ℝ)<X (1/3) := by
  have ht : (1/3:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1/3:ℝ))
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤1/3 by norm_num)
  have hmul := mul_lt_mul_of_pos_right L_bounds.1
    (show 0<Real.cos (1/3:ℝ) by linarith [(transport_trig ht).1])
  norm_num at hc hs
  dsimp [X,K]
  nlinarith only [hc,hs,hmul]

theorem cap_error_lt {z : ℝ} (hz : OnCap z) : z<1/3 := by
  by_contra! hn
  have hm := X_monotone (show (1/3:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz.1 hn
  linarith [X_third_lower,cap_X_upper hz]

theorem cap_down {z w : ℝ} (hz : OnCap z) (hw : w∈Icc 0 z) : OnCap w := by
  have hw' : w∈Icc 0 frameCap := ⟨hw.1,hw.2.trans hz.1.2⟩
  have hm := X_monotone hw' hz.1 hw.2
  have hp : 0≤X w := by linarith [X_lower hw']
  have hsq := pow_le_pow_left₀ hp hm 2
  exact ⟨hw',by linarith [hz.2]⟩

theorem cap_radicand {z : ℝ} (hz : OnCap z) : (1/4:ℝ)≤Q0-(X z)^2 := by
  linarith [hz.2]

theorem Z_pos {z : ℝ} (hz : OnCap z) : 0<Z z :=
  Real.sqrt_pos.mpr (by linarith [cap_radicand hz])

theorem Z_sq {z : ℝ} (hz : OnCap z) : (Z z)^2=Q0-(X z)^2 :=
  Real.sq_sqrt (by linarith [cap_radicand hz])

theorem Z_bounds {z : ℝ} (hz : OnCap z) : (1/2:ℝ)≤Z z ∧ Z z<233/200 := by
  have hsq := Z_sq hz
  have hl := X_lower hz.1
  have hn := Z_pos hz
  have hrad := cap_radicand hz
  norm_num [Q0] at hsq hrad
  constructor <;> nlinarith

theorem cap_trig {z : ℝ} (hz : OnCap z) :
    (17/18:ℝ)≤Real.cos z ∧ Real.sin z≤1/3 := by
  have hsmall := cap_error_lt hz
  have hsin := Real.sin_le hz.1.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := z)
  have hsquare := pow_le_pow_left₀ hz.1.1 hsmall.le 2
  constructor <;> nlinarith

theorem cap_Xd_lower {z : ℝ} (hz : OnCap z) : (41/50:ℝ)<Xd z := by
  have htr := cap_trig hz
  have hsin := (transport_trig hz.1).2.2.1
  have hp := mul_le_mul L_bounds.2.le htr.2 hsin
    (by norm_num : (0:ℝ)≤601/1000)
  dsimp [Xd,K]
  nlinarith only [htr.1,hp]

theorem X_eighth_lower : (173/100:ℝ)<X (1/8) := by
  have ht : (1/8:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1/8:ℝ))
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤1/8 by norm_num)
  have hmul := mul_lt_mul_of_pos_right L_bounds.1
    (show 0<Real.cos (1/8:ℝ) by linarith [(transport_trig ht).1])
  norm_num at hc hs
  dsimp [X,K]
  nlinarith only [hc,hs,hmul]

theorem Xd_eighth_lower : (99/100:ℝ)<Xd (1/8) := by
  have ht : (1/8:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1/8:ℝ))
  have hs := Real.sin_le (show (0:ℝ)≤1/8 by norm_num)
  have hp := mul_le_mul L_bounds.2.le hs (transport_trig ht).2.2.1
    (by norm_num : (0:ℝ)≤601/1000)
  norm_num at hc
  dsimp [Xd,K]
  nlinarith only [hc,hp]

theorem cap_large_bounds {z : ℝ} (hz : OnCap z) (hlarge : (1/8:ℝ)≤z) :
    (173/100:ℝ)<X z ∧ Z z<97/100 := by
  have hm := X_monotone (show (1/8:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz.1 hlarge
  have hx : (173/100:ℝ)<X z := X_eighth_lower.trans_le hm
  have hsq := Z_sq hz
  have hpos := Z_pos hz
  norm_num [Q0] at hsq
  exact ⟨hx,by nlinarith⟩

/-- The explicit prefix restricts the unchanged T circle. -/
theorem cap_of_prefix (a t : State) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hpref : «prefix» z≤a.b+t.a/Real.cos z) :
    X z≤t.a+1/2 ∧ OnCap z := by
  have hcos : 0<Real.cos z := by linarith [(transport_trig hz).1]
  have hab : a.b≤c0 := by
    have hh := state_sum_sharp a
    linarith [a.canonical]
  have hm := mul_le_mul_of_nonneg_right hpref hcos.le
  have hid : «prefix» z*Real.cos z=(3/2)*Real.cos z+1/2+K*Real.sin z := by
    dsimp [«prefix»]
    field_simp
  rw [hid] at hm
  have hdiv : (a.b+t.a/Real.cos z)*Real.cos z=a.b*Real.cos z+t.a := by
    field_simp
  rw [hdiv] at hm
  have hprod := mul_le_mul_of_nonneg_right hab hcos.le
  have hx : X z≤t.a+1/2 := by dsimp [X,L] at *; nlinarith only [hm,hprod]
  have hc := state_circle t
  have hs := pow_le_pow_left₀ (show 0≤X z by linarith [X_lower hz]) hx 2
  have hb := t.b_nonneg
  exact ⟨hx,⟨hz,by nlinarith only [hc,hs,hb,sq_nonneg t.b]⟩⟩

end SquaresInCircles.Eight.GlobalBT.HighPrimary
end
end
end

section
/-!
## The two AB owners at nonpositive error

The signed AB dual comparison gives a necessary cap together with its charge reserve. A negative
B with a weak BT1 witness has `b.b < 1/2` (`negative_B_small`), which puts B on the small side of
its radial chart, `7/12 ≤ b.a` (`small_B_primary`), and gives the cap `BT1_secondary_cap`. Both
conclusions are necessary inequalities on the states A, B, T (`nonpositive_prefix`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.OneNegative

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem negative_B_small (b t : State) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hy : transverse b≤0) (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) : b.b<1/2 := by
  have hby : transverse b= -b.b := transverse_nonpos_eq b hy
  have hsum := sine_cosine_monotone
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz hz.1
  simp only [Real.sin_zero,Real.cos_zero,zero_add] at hsum
  have tr := transport_trig hz
  rw [width_negative hz] at hBT
  dsimp [projection] at hBT
  rw [hby] at hBT
  simp only [Real.sin_neg,Real.cos_neg] at hBT
  by_contra! hn
  have hA := mul_le_mul_of_nonneg_right (hn.trans b.canonical) tr.2.2.1
  have hB := mul_le_mul_of_nonneg_right hn (show 0≤Real.cos z by linarith [tr.1])
  have hT := (ZeroPrimary.coordinates t).2.1
  nlinarith only [hBT,hA,hB,hT,hsum]

theorem small_B_primary (b : State) (hb : b.b<1/2) : (7/12:ℝ)≤b.a := by
  by_cases hcore : b.branch.type=0
  · have hh := (CommonQuarter.core_small_side (FrameCoreArc.state_core_chart b hcore) hb).1
    linarith
  · have houter := state_outer_chart b hcore
    have hA := (A_bounds houter.2).1
    rw [← houter.1] at hA
    linarith [c0_bounds.1]

theorem BT1_secondary_cap (b t : State) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hB : (7/12:ℝ)≤b.a) (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) :
    HighPrimary.«prefix» z≤1+transverse b+t.a/Real.cos z := by
  have tr := transport_trig hz
  have hcos : 0<Real.cos z := by linarith [tr.1]
  have hprod := mul_le_mul_of_nonneg_right hB tr.2.2.1
  rw [width_negative hz] at hBT
  dsimp [projection] at hBT
  simp only [Real.sin_neg,Real.cos_neg] at hBT
  have hleft : HighPrimary.«prefix» z*Real.cos z=
      (3/2)*Real.cos z+1/2+(13/12)*Real.sin z := by
    dsimp [HighPrimary.«prefix»,HighPrimary.K]
    field_simp
  have hright : (1+transverse b+t.a/Real.cos z)*Real.cos z=
      (1+transverse b)*Real.cos z+t.a := by
    field_simp
  apply le_of_mul_le_mul_right _ hcos
  rw [hleft,hright]
  nlinarith only [hBT,hprod]

/-- At nonpositive AB and BT errors, with owner `1` on BT, the prefix cap
`prefix z ≤ a.b + t.a / cos z` holds and the prefix charge keeps the negative-AB reserve
`(9/2000) w`. -/
theorem nonpositive_prefix (a b t : State) (ab : Bool) {w z : ℝ}
    (ha : 0≤transverse a) (hw : w∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hAB : GlobalOuterAnchor.width (-w)≤projection false a b (-w) (leftOwner ab))
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) :
    HighPrimary.«prefix» z≤a.b+t.a/Real.cos z ∧
      -z+kappa*(HighPrimary.«prefix» z-t.a/Real.cos z)+(9/2000)*w≤
        -w-z+kappa*a.b := by
  have hcos : 0<Real.cos w := by linarith [(transport_trig hw).1]
  have hl : 0≤kappa/Real.cos w := div_nonneg (by norm_num [kappa]) hcos.le
  have hab := (negative_zero_delete a b ab hw).trans (zeroDual_le_error a b ab hl hAB)
  rw [transverse_of_nonneg a ha] at hab
  have hbase : 1+transverse b≤a.b := by
    have hh := hab
    norm_num [kappa] at hh
    linarith [hw.1]
  have hby : transverse b<0 := by
    linarith [(ZeroPrimary.coordinates a).2.2.2.2]
  have hbsmall := negative_B_small b t hz hby.le hBT
  have hcap := BT1_secondary_cap b t hz (small_B_primary b hbsmall) hBT
  have hprod := mul_le_mul_of_nonneg_left
    (show HighPrimary.«prefix» z-t.a/Real.cos z≤1+transverse b by linarith)
    (show 0≤kappa by norm_num [kappa])
  refine ⟨by linarith,?_⟩
  nlinarith only [hab,hprod]

end SquaresInCircles.Eight.GlobalBT.OneNegative
end
end
end

section
/-!
## The original B chart for the effective AB0--BT1 cap

For 0 <= AB <= -BT, both signed B cases have transverse magnitude
below one half.  The positive case is excluded by exact whole-range
projection bounds on either side of 41/100.  The true B radial chart
then gives its primary bound, including the core side endpoint.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.OneNegative

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem sin_monotone : MonotoneOn Real.sin (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · fun_prop
  · exact fun x _ => Real.hasDerivAt_sin x
  · intro x hx
    linarith [(transport_trig (Ioo_subset_Icc_self hx)).1]

theorem cos_antitone : AntitoneOn Real.cos (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
  · fun_prop
  · exact fun x _ => Real.hasDerivAt_cos x
  · intro x hx
    have hh := (transport_trig (Ioo_subset_Icc_self hx)).2.2.1
    linarith

theorem half_secondary_primary_upper (b : State) (hb : (1/2:ℝ)≤b.b) : b.a<151/125 := by
  have hc := state_circle b
  have ha := b.a_pos
  have hsq := pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num)
    (show 1≤b.b+1/2 by linarith) 2
  norm_num [Q0] at hc
  nlinarith

theorem width_cut_lower : (463/200:ℝ)<1+Real.cos (41/100)+Real.sin (41/100) := by
  have hc := cos_lower_six (show (0:ℝ)≤41/100 by norm_num)
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤41/100 by norm_num)
  norm_num at hc hs
  linarith

theorem AB0_intermediate_B_small (a b t : State) {v z : ℝ}
    (ha : 0≤transverse a) (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hvz : v≤z) (hAB : GlobalOuterAnchor.width v≤projection false a b v 0)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) : b.b<1/2 := by
  by_cases hy : transverse b≤0
  · exact negative_B_small b t hz hy hBT
  · have hby := transverse_of_nonneg b (le_of_not_ge hy)
    have hay := transverse_of_nonneg a ha
    have hvtr := transport_trig hv
    have hztr := transport_trig hz
    have hAB' := hAB
    have hBT' := hBT
    rw [width_positive hv] at hAB'
    rw [width_negative hz] at hBT'
    dsimp [projection] at hAB' hBT'
    rw [hay,hby] at hAB'
    rw [hby] at hBT'
    simp only [Real.sin_neg,Real.cos_neg] at hBT'
    by_contra! hb
    have haB := half_secondary_primary_upper b hb
    have hav := (ZeroPrimary.coordinates a).2.2.2.2
    have hat := (ZeroPrimary.coordinates t).2.1
    have hwidth : (1:ℝ)≤(1+Real.cos v+Real.sin v)/2 := by
      have hh := sine_cosine_monotone
        (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hv hv.1
      simp only [Real.sin_zero,Real.cos_zero,zero_add] at hh
      linarith
    by_cases hcut : v≤41/100
    · have hs : Real.sin v≤41/100 := (Real.sin_le hv.1).trans hcut
      have hc := Real.one_sub_sq_div_two_le_cos (x := v)
      have hsq := pow_le_pow_left₀ hv.1 hcut 2
      have hcos : (18319/20000:ℝ)≤Real.cos v := by nlinarith only [hc,hsq]
      have hp1 := mul_le_mul haB.le hs hvtr.2.2.1
        (by norm_num : (0:ℝ)≤151/125)
      have hp2 := mul_le_mul hb hcos (by norm_num : (0:ℝ)≤18319/20000) b.b_nonneg
      nlinarith only [hAB',hav,hwidth,hp1,hp2]
    · have hsin := sin_monotone hv hz hvz
      have hcos := cos_antitone hv hz hvz
      have hp1 := mul_nonneg b.a_pos.le (sub_nonneg.mpr hsin)
      have hp2 := mul_nonneg b.b_nonneg (sub_nonneg.mpr hcos)
      have hwidthOrder := sine_cosine_monotone hv hz hvz
      have hcutOrder := sine_cosine_monotone
        (show (41/100:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hv (by linarith)
      have hlarge : (463/200:ℝ)<1+Real.cos v+Real.sin v := by
        linarith [width_cut_lower]
      nlinarith only [hAB',hBT',hp1,hp2,hwidthOrder,hlarge,hav,hat]

end SquaresInCircles.Eight.GlobalBT.OneNegative
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.OneNegative

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def capLine (r v : ℝ) : ℝ :=
  (1+Real.cos v+Real.sin v)/2+
  (1+Real.cos (v+r)+Real.sin (v+r))/(2*Real.cos r)+
  (Real.sin r/Real.cos r)*((7/12)*Real.cos v-(1/2)*Real.sin v)
def capLineD (r v : ℝ) : ℝ :=
  (Real.cos (v+r)-Real.sin (v+r)-(1/12)*Real.sin r*Real.sin v)/Real.cos r

theorem capLine_deriv {r : ℝ} (hr : r∈Icc 0 frameCap) (v : ℝ) :
    HasDerivAt (capLine r) (capLineD r v) v := by
  have hcos : Real.cos r≠0 := ne_of_gt (by linarith [(transport_trig hr).1])
  have hfirst := (((Real.hasDerivAt_cos v).add (Real.hasDerivAt_sin v)).const_add 1).div_const 2
  have hcosSum := (Real.hasDerivAt_cos (v+r)).comp v ((hasDerivAt_id v).add_const r)
  have hsinSum := (Real.hasDerivAt_sin (v+r)).comp v ((hasDerivAt_id v).add_const r)
  have hsecond := ((hcosSum.add hsinSum).const_add 1).div_const (2*Real.cos r)
  have hthird := (((Real.hasDerivAt_cos v).const_mul (7/12)).sub
    ((Real.hasDerivAt_sin v).const_mul (1/2))).const_mul (Real.sin r/Real.cos r)
  convert (hfirst.add hsecond).add hthird using 1
  · funext x
    dsimp [capLine]
    ring
  · dsimp [capLineD]
    rw [Real.cos_add,Real.sin_add]
    field_simp [hcos]
    ring

theorem capLineD_positive {r v : ℝ} (hr : r∈Icc 0 frameCap)
    (hv : v∈Icc 0 frameCap) (hsum : v+r≤frameCap) : 0<capLineD r v := by
  have hsumdom : v+r∈Icc 0 frameCap := ⟨add_nonneg hv.1 hr.1,hsum⟩
  have tr := transport_trig hsumdom
  have hprod := mul_le_mul (Real.sin_le_one r) (Real.sin_le_one v)
    (transport_trig hv).2.2.1 (by norm_num : (0:ℝ)≤1)
  have hnum : 0<Real.cos (v+r)-Real.sin (v+r)-(1/12)*Real.sin r*Real.sin v := by
    nlinarith only [tr.1,tr.2.2.2.1,hprod]
  exact div_pos hnum (by linarith [(transport_trig hr).1])

theorem capLine_zero {r : ℝ} (hr : r∈Icc 0 frameCap) :
    capLine r 0=HighPrimary.«prefix» r := by
  have hcos : Real.cos r≠0 := ne_of_gt (by linarith [(transport_trig hr).1])
  simp only [capLine,Real.cos_zero,Real.sin_zero,zero_add,mul_one,mul_zero,sub_zero]
  dsimp [HighPrimary.«prefix»,HighPrimary.K]
  field_simp [hcos]
  ring

theorem capLine_lower {r v : ℝ} (hr : r∈Icc 0 frameCap) (hv : 0≤v)
    (hsum : v+r≤frameCap) : HighPrimary.«prefix» r≤capLine r v := by
  have hm : MonotoneOn (capLine r) (Icc 0 v) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x _ => (capLine_deriv hr x).continuousAt.continuousWithinAt
    · exact fun x _ => capLine_deriv hr x
    · intro x hx
      exact (capLineD_positive hr
        ⟨hx.1.le,by linarith [hx.2,hr.1,hsum]⟩ (by linarith [hx.2,hsum])).le
  have hh := hm ⟨le_rfl,hv⟩ ⟨hv,le_rfl⟩ hv
  rwa [capLine_zero hr] at hh

theorem AB0_effective_cap (a b t : State) {v z : ℝ}
    (ha : 0≤transverse a) (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hvz : v≤z) (hAB : GlobalOuterAnchor.width v≤projection false a b v 0)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) :
    HighPrimary.«prefix» (z-v)≤a.b+t.a/Real.cos (z-v) ∧
      -(z-v)+kappa*(HighPrimary.«prefix» (z-v)-t.a/Real.cos (z-v))≤v-z+kappa*a.b := by
  let r := z-v
  have hr : r∈Icc 0 frameCap := ⟨by dsimp [r]; linarith,by dsimp [r]; linarith [hz.2,hv.1]⟩
  have hsum : v+r=z := by dsimp [r]; ring
  have hcos : 0<Real.cos r := by linarith [(transport_trig hr).1]
  have hBsmall := AB0_intermediate_B_small a b t ha hv hz hvz hAB hBT
  have hBprimary := small_B_primary b hBsmall
  have hBy : -(1/2:ℝ)≤transverse b := by linarith [(transverse_bounds b).1]
  have hp1 := mul_le_mul_of_nonneg_right hBprimary
    (show 0≤Real.cos v by linarith [(transport_trig hv).1])
  have hp2 := mul_le_mul_of_nonneg_right hBy (transport_trig hv).2.2.1
  have hforce := mul_le_mul_of_nonneg_left
    (show (7/12)*Real.cos v-(1/2)*Real.sin v≤b.a*Real.cos v+transverse b*Real.sin v by
      linarith only [hp1,hp2]) (transport_trig hr).2.2.1
  have hAB' := hAB
  have hBT' := hBT
  rw [width_positive hv] at hAB'
  rw [width_negative hz] at hBT'
  dsimp [projection] at hAB' hBT'
  rw [transverse_of_nonneg a ha] at hAB'
  simp only [Real.sin_neg,Real.cos_neg] at hBT'
  have hABscaled := mul_le_mul_of_nonneg_right hAB' hcos.le
  have hsin : Real.sin z=Real.sin v*Real.cos r+Real.cos v*Real.sin r := by
    rw [← hsum,Real.sin_add]
  have hcosz : Real.cos z=Real.cos v*Real.cos r-Real.sin v*Real.sin r := by
    rw [← hsum,Real.cos_add]
  have hline : capLine r v≤a.b+t.a/Real.cos r := by
    have hleft : capLine r v*Real.cos r=
        ((1+Real.cos v+Real.sin v)/2)*Real.cos r+
        (1+Real.cos z+Real.sin z)/2+
        Real.sin r*((7/12)*Real.cos v-(1/2)*Real.sin v) := by
      dsimp [capLine]
      rw [hsum]
      field_simp [hcos.ne']
    have hright : (a.b+t.a/Real.cos r)*Real.cos r=a.b*Real.cos r+t.a := by
      field_simp [hcos.ne']
    apply le_of_mul_le_mul_right _ hcos
    rw [hleft,hright]
    rw [hsin,hcosz] at hBT'
    rw [hsin,hcosz]
    nlinarith only [hABscaled,hBT',hforce]
  have hcap := (capLine_lower hr hv.1 (by rw [hsum]; exact hz.2)).trans hline
  refine ⟨hcap,?_⟩
  have hp := mul_le_mul_of_nonneg_left hcap (show 0≤kappa by norm_num [kappa])
  change -(z-v)+kappa*(HighPrimary.«prefix» r-t.a/Real.cos r)≤v-z+kappa*a.b
  nlinarith only [hp]

end SquaresInCircles.Eight.GlobalBT.OneNegative
end
end
end
