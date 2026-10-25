module

public import SquaresInCircles.Eight.TableFree.GlobalQuarterNegativePrimary
public import SquaresInCircles.Eight.TableFree.GlobalZeroLowScalar

/-!
# Actual domains in the zero--low-quarter sign contradiction

The source of the zero is provisionally nonpositive.  Its retained owner
2 forces a positive error and a definite transverse coordinate at the
common vertex.  Both original quarter owners are retained, including
their weak ties. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalZeroLow

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign GlobalOuterAnchor
open GlobalQuarterNegativePrimary

theorem zero_margin (s c : State) {v : ℝ} (hv : |v|≤frameCap)
    (hs : transverse s≤0) (hc : transverse c≤0) :
    s.Feasible c 2 v ↔ GlobalOuterAnchor.width v≤ s.a*Real.sin v-s.b*Real.cos v+c.b := by
  have hsy := transverse_nonpos_eq s hs
  have hcy := transverse_nonpos_eq c hc
  simp only [State.Feasible,forwardMargin,Matrix.cons_val,
    CommonQuarter.signed_width (by simpa only [frameCap] using hv),GlobalOuterAnchor.width]
  rw [hsy,hcy]
  constructor <;> intro hh <;> linarith

theorem zero_positive (s c : State) {v : ℝ} (hv : |v|≤frameCap)
    (hs : transverse s≤0) (hc : transverse c≤0)
    (hm : s.Feasible c 2 v) : 0<v := by
  have hh := (zero_margin s c hv hs hc).1 hm
  have hw := width_ge_one hv
  by_contra! hn
  have hsin := sine_nonpos hv hn
  have hcos : 0≤Real.cos v := by linarith [(signed_trig hv).1]
  have hp := mul_nonpos_of_nonneg_of_nonpos s.a_pos.le hsin
  have hb := mul_nonneg s.b_nonneg hcos
  linarith [(coordinates c).2.2.2.2]

theorem zero_domain (s c : State) {v : ℝ} (hv : |v|≤frameCap)
    (hs : transverse s≤0) (hc : transverse c≤0)
    (hm : s.Feasible c 2 v) :
    v∈Ioc 0 frameCap ∧ 29/100<c.b ∧ unsigned s≤lam*s.b := by
  have hpos := zero_positive s c hv hs hc hm
  have hv' : v∈Icc 0 frameCap := ⟨hpos.le,(le_abs_self v).trans hv⟩
  have tr := transport_trig hv'
  have hh := (zero_margin s c hv hs hc).1 hm
  have hw : GlobalOuterAnchor.width v=(1+Real.cos v+Real.sin v)/2 := by
    simp only [GlobalOuterAnchor.width,abs_of_nonneg tr.2.2.1]
  rw [hw] at hh
  have hsource := (coordinates s).2.1
  have hprod := mul_le_mul_of_nonneg_right hsource.le tr.2.2.1
  have hbprod := mul_nonneg s.b_nonneg (show 0≤Real.cos v by linarith [tr.1])
  have hcsmall : 29/100<c.b := by
    have hsinupper := mul_le_mul_of_nonneg_left
      (show Real.sin v≤129/200 by linarith [tr.2.2.2.1])
      (by norm_num : (0:ℝ)≤183/200)
    linarith [tr.1]
  have hmarker : unsigned s≤lam*s.b := by
    by_cases hcore : s.branch.type=0
    · have ha := (core_bounds s hcore).1
      have hb : s.b<1/2 := by
        by_contra! hn
        have h1 := mul_le_mul ha
          (show Real.sin v≤13/20 by linarith [tr.2.2.2.1]) tr.2.2.1
          (by norm_num : (0:ℝ)≤7/12)
        have h2 := mul_le_mul hn
          (show (3/4:ℝ)≤Real.cos v by linarith [tr.1])
          (by norm_num : (0:ℝ)≤3/4) s.b_nonneg
        have hwidth := width_ge_one hv
        rw [hw] at hwidth
        linarith [(coordinates c).2.2.2.2]
      exact marker_small_upper s hb
    · exact marker_outer_upper s hcore
  exact ⟨⟨hpos,hv'.2⟩,hcsmall,hmarker⟩

theorem secondary_target_outer (c t : State) {x : ℝ} (hx : |x|≤frameCap)
    (hc : transverse c≤0) (ht : 0≤transverse t)
    (hm : c.Feasible t 0 (Real.pi/2+x)) : t.branch.type≠0 := by
  intro hcore
  have hproj := FrameCoreArc.projection_lt (a:=t.b) (b:=t.a)
    (by norm_num : (0:ℝ)<1) (by nlinarith [(core_bounds t hcore).2.2]) x
  have hh := (low_zero_margin c t hx hc ht).1 hm
  have hw := width_ge_one hx
  linarith [c.b_nonneg]

theorem primary_target_outer (s c t : State) {v x : ℝ}
    (hv : |v|≤frameCap) (hx : x∈Icc 0 frameCap) (hspan : v+x≤frameCap)
    (hs : transverse s≤0) (hc : transverse c≤0)
    (hz : s.Feasible c 2 v)
    (hp : c.Feasible t 1 (Real.pi/2+x)) : t.branch.type≠0 := by
  have hvpos := zero_positive s c hv hs hc hz
  have hv' : v∈Icc 0 frameCap := ⟨hvpos.le,(le_abs_self v).trans hv⟩
  have hxabs : |x|≤frameCap := by rw [abs_of_nonneg hx.1]; exact hx.2
  have tv := transport_trig hv'
  have tx := transport_trig hx
  have hsum := transport_trig (show v+x∈Icc 0 frameCap from ⟨by linarith [hx.1],hspan⟩)
  have hzero := (zero_margin s c hv hs hc).1 hz
  have hquarter := (low_one_margin c t hxabs hc).1 hp
  have hcos : 0≤Real.cos x := by linarith [tx.1]
  have hweighted := mul_le_mul_of_nonneg_right hzero hcos
  have hwv := mul_le_mul_of_nonneg_right (width_ge_one hv) hcos
  have hwx := width_ge_one hxabs
  have hsinprod := mul_nonneg tv.2.2.1 hcos
  have hsource := mul_le_mul_of_nonneg_right (coordinates s).2.1.le hsinprod
  have hcommon := mul_le_mul_of_nonneg_right (coordinates c).2.1.le tx.2.2.1
  have hnegative := mul_nonneg (mul_nonneg s.b_nonneg
    (show 0≤Real.cos v by linarith [tv.1])) hcos
  have hextra := mul_le_mul
    (show Real.sin x≤13/20 by linarith [tx.2.2.2.1])
    (show 1-Real.cos v≤1/4 by linarith [tv.1])
    (sub_nonneg.mpr tv.2.1) (by norm_num : (0:ℝ)≤13/20)
  have hsumid : Real.sin x+Real.sin v*Real.cos x=
      Real.sin (v+x)+Real.sin x*(1-Real.cos v) := by
    rw [Real.sin_add]
    ring
  have hangle : Real.sin x+Real.sin v*Real.cos x≤13/16 := by
    rw [hsumid]
    linarith [hsum.2.2.2.1]
  intro hcore
  have htcore := (core_bounds t hcore).1
  linarith [tx.1]

theorem secondary_negative_cut (s c t : State) {v z : ℝ}
    (hv : |v|≤frameCap) (hz : z∈Icc 0 frameCap)
    (hs : transverse s≤0) (hc : transverse c≤0) (ht : 0≤transverse t)
    (hzero : s.Feasible c 2 v)
    (hquarter : c.Feasible t 0 (Real.pi/2-z)) : z<23/100 := by
  have hb := (zero_domain s c hv hs hc hzero).2.1
  have hd : |-z|≤frameCap := by rw [abs_neg,abs_of_nonneg hz.1]; exact hz.2
  have hh := (low_zero_margin c t hd hc ht).1
    (by simpa only [sub_eq_add_neg] using hquarter)
  have tr := transport_trig hz
  have hw : GlobalOuterAnchor.width (-z)=(1+Real.cos z+Real.sin z)/2 := by
    simp [GlobalOuterAnchor.width,abs_of_nonneg tr.2.2.1]
  rw [hw,Real.cos_neg,Real.sin_neg] at hh
  have hprimary := mul_le_mul_of_nonneg_right (coordinates t).2.1.le
    (show 0≤Real.cos z by linarith [tr.1])
  have htrans := mul_nonneg t.b_nonneg tr.2.2.1
  have hnecessary : 79/100<(183/200)*Real.cos z-(1/2)*Real.sin z := by nlinarith
  have hmono : AntitoneOn (fun u : ℝ => (183/200)*Real.cos u-(1/2)*Real.sin u)
      (Icc 0 frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
    · fun_prop
    · intro u _
      convert ((Real.hasDerivAt_cos u).const_mul (183/200)).sub
        ((Real.hasDerivAt_sin u).const_mul (1/2)) using 1 <;> ring
    · intro u hu
      have hh := transport_trig (Ioo_subset_Icc_self hu)
      linarith [hh.1,hh.2.2.1]
  by_contra! hlarge
  have hupper := hmono (show (23/100:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz hlarge
  have hcos := cos_upper_four (show (0:ℝ)≤23/100 by norm_num)
  have hsin := Real.sin_ge_sub_cube (show (0:ℝ)≤23/100 by norm_num)
  norm_num at hcos hsin
  linarith

end SquaresInCircles.Eight.TableFree.GlobalZeroLow
