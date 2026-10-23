module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperReferences

/-!
# The complete axial part of the six upper primary contacts

Uncompiled transcription of the axial monotonicity and curvature
arguments. The exceptional row 1 is reduced to its axial boundary and
to the interval beginning at .09; its earlier interior contacts are
retained for the exact angular-stationarity argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

theorem axial_tangent (r : Row) {e x y κ : ℝ} (he : IsEvent e)
    (hx : x∈Icc 0 e) (hy : y∈Icc 0 e) (hκ : ∀u∈Icc 0 e,κ≤F2 r u) :
    F r y+F1 r y*(x-y)+κ/2*(x-y)^2≤F r x :=
  curvature_tangent hx hy (fun u hu => F_hasDerivAt r he hu)
    (fun u hu => F1_hasDerivAt r he hu) hκ

theorem F_zero_linear {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (44913/50000:ℝ)+(49/250)*x<F 0 x := by
  have ht := axial_tangent 0 he hx ⟨le_rfl,by linarith [(event_bounds he).1]⟩
    (fun u hu => (axial_curvature_zero he hu).le)
  have hF := Reference.initial_value 0
  norm_num [Reference.initialLower] at hF
  have hp := mul_le_mul_of_nonneg_right Reference.initial_first_zero.le hx.1
  nlinarith [sq_nonneg x]

theorem F_zero_increasing {e : ℝ} (he : IsEvent e) : MonotoneOn (F 0) (Icc 0 e) := by
  have hm : MonotoneOn (F1 0) (Icc 0 e) :=
    monoOn_of_hasDeriv_nonneg
      (fun x hx => (F1_hasDerivAt 0 he hx).continuousAt.continuousWithinAt)
      (fun x hx => F1_hasDerivAt 0 he (Ioo_subset_Icc_self hx))
      (fun x hx => by linarith [axial_curvature_zero he (Ioo_subset_Icc_self hx)])
  apply monoOn_of_hasDeriv_nonneg
    (fun x hx => (F_hasDerivAt 0 he hx).continuousAt.continuousWithinAt)
    (fun x hx => F_hasDerivAt 0 he (Ioo_subset_Icc_self hx))
  intro x hx
  have hh := hm ⟨le_rfl,by linarith [(event_bounds he).1]⟩ (Ioo_subset_Icc_self hx) hx.1.le
  linarith [Reference.initial_first_zero]

theorem axial_ratioD_upper {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    ratioD (contact 0 x)≤Q0/(129/100:ℝ)^3 := by
  have hv := (axial_bounds he hx).2.2.1
  have hp : 0<v x := by linarith
  have hc := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤129/100) hv.le 3
  change Q0/(v x)^3≤Q0/(129/100:ℝ)^3
  apply (div_le_iff₀ (pow_pos hp 3)).2
  norm_num [Q0] at *
  nlinarith

theorem H_zero_derivative {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    -(52/25:ℝ)<H1 0 x := by
  have hb := axial_bounds he hx
  have hg := projection_early he hx
  have hD := axial_ratioD_upper he hx
  have hL := sourceD_lower 0 (before_domain he hx).2.2
  norm_num [p,q] at hL
  have hd0 := (SameContact.ratioD_pos (Same.primary_domain (before_domain he hx).2.2)).le
  have hh0 : 0≤h x := by linarith [hb.2.2.2.2.1]
  have h1 := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hD (show 0≤q 0 by norm_num [q]))
      hb.2.2.2.2.2.1.le hh0 (by positivity)) hg.2.1.le
      (by linarith [hg.1] : 0≤projection x) (by positivity)
  have h2 := mul_le_mul hL hg.2.2.1.le (by norm_num)
    (by linarith : 0≤sourceD 0 (contact 0 x))
  dsimp [H1,sourceDD]
  norm_num [q,Q0] at h1
  nlinarith

theorem H_zero_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    -(27/1000:ℝ)-(52/25)*x<H 0 x := by
  have hh := derivative_reserve
    (fun y hy => (H_hasDerivAt 0 he hy).continuousAt.continuousWithinAt)
    (fun y hy => H_hasDerivAt 0 he (Ioo_subset_Icc_self hy))
    (fun y hy => (H_zero_derivative he (Ioo_subset_Icc_self hy)).le)
    (show (0:ℝ)∈Icc 0 e from ⟨le_rfl,by linarith [(event_bounds he).1]⟩) hx hx.1
  linarith [Reference.initial_H_zero]

theorem H_one_decreasing {e : ℝ} (he : IsEvent e) : AntitoneOn (H 1) (Icc 0 e) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x hx => (H_hasDerivAt 1 he hx).continuousAt.continuousWithinAt)
    (fun x hx => H_hasDerivAt 1 he (Ioo_subset_Icc_self hx))
  intro x hx
  have hx' := Ioo_subset_Icc_self hx
  have hb := axial_bounds he hx'
  have hg := projection_early he hx'
  have hD := source_ratioD_lower (before_domain he hx').2.2
  have hL := axial_sourceD_upper 1 he hx'
  have hL0 : 0≤sourceD 1 (contact 0 x) := by
    have hh := sourceD_lower 1 (before_domain he hx').2.2
    norm_num [p,q] at hh
    linarith
  have h1 := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hD (show 0≤q 1 by norm_num [q]))
      (show (227/250:ℝ)≤h x by linarith [hb.2.2.2.2.1]) (by norm_num) (by positivity))
      hg.1 (by norm_num) (by positivity)
  have h2 := mul_le_mul hL.le hg.2.2.2.le
    (by linarith [hg.2.2.1] : 0≤projectionD x) (by norm_num [p,q])
  dsimp [H1,sourceDD]
  norm_num [p,q,Q0] at h1 h2
  nlinarith

theorem event_trig {e : ℝ} (he : IsEvent e) :
    (10679/100000:ℝ)<Real.sin e ∧ Real.sin e<(21419/200000:ℝ) ∧
      (124281/125000:ℝ)<Real.cos e ∧ Real.cos e<(49713/50000:ℝ) := by
  have hsl : (10679/100000:ℝ)<(ShortOuterZero.Same.Event.eventSin he).lo := by
    dsimp [ShortOuterZero.Same.Event.eventSin]
    event_reference_arithmetic
  have hsu : (ShortOuterZero.Same.Event.eventSin he).hi<(21419/200000:ℝ) := by
    dsimp [ShortOuterZero.Same.Event.eventSin]
    event_reference_arithmetic
  have hcl : (124281/125000:ℝ)<(ShortOuterZero.Same.Event.eventCos he).lo := by
    dsimp [ShortOuterZero.Same.Event.eventCos]
    event_reference_arithmetic
  have hcu : (ShortOuterZero.Same.Event.eventCos he).hi<(49713/50000:ℝ) := by
    dsimp [ShortOuterZero.Same.Event.eventCos]
    event_reference_arithmetic
  exact ⟨hsl.trans_le (ShortOuterZero.Same.Event.eventSin he).mem.1,
    (ShortOuterZero.Same.Event.eventSin he).mem.2.trans_lt hsu,
    hcl.trans_le (ShortOuterZero.Same.Event.eventCos he).mem.1,
    (ShortOuterZero.Same.Event.eventCos he).mem.2.trans_lt hcu⟩

theorem H_one_at_event {e : ℝ} (he : IsEvent e) : -(71/1000:ℝ)<H 1 e := by
  have ht := event_trig he
  have hsin := mul_le_mul rho_bounds.1.le ht.1.le (by norm_num)
    (by linarith [rho_bounds.1] : 0≤rho)
  have hid : H 1 e=(p 1+q 1)*projection e+P 1*rho-t 1 := by
    dsimp [H,first,sourceD,stateSpeed,SecondWord.SameZero.k]
    rw [he.2,ratio_zero,ratio_diagonal]
    dsimp [projection]
    ring
  rw [hid]
  norm_num [p,q,P,t,projection]
  nlinarith [rho_bounds.1,ht.2.2.1]

theorem H_one_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    -(71/1000:ℝ)<H 1 x :=
  (H_one_at_event he).trans_le ((H_one_decreasing he) hx
    ⟨by linarith [(event_bounds he).1],le_rfl⟩ hx.2)

theorem F_pair_lower (r : Row) (hr : r=3∨r=4) {e x : ℝ}
    (he : IsEvent e) (hx : x∈Icc 0 e) : (4489/5000:ℝ)<F r x := by
  have ht := axial_tangent r he hx ⟨le_rfl,by linarith [(event_bounds he).1]⟩
    (fun u hu => (axial_curvature_pair r hr he hu).le)
  have hF := Reference.initial_value r
  have hD := Reference.initial_first_pair r hr
  have hp := mul_le_mul_of_nonneg_right hD.le hx.1
  have hs := sq_nonneg (x/4-1/125)
  rcases hr with rfl | rfl <;> norm_num [Reference.initialLower] at hF <;> nlinarith

theorem F_one_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (4489/5000:ℝ)<F 1 x := by
  have ht := axial_tangent 1 he hx ⟨le_rfl,by linarith [(event_bounds he).1]⟩
    (fun u hu => (axial_curvature_one he hu).le)
  have hF := Reference.initial_value 1
  norm_num [Reference.initialLower] at hF
  have hp := mul_le_mul_of_nonneg_right Reference.initial_first_one.le hx.1
  nlinarith [sq_nonneg ((47/100)*x-1/50)]

theorem F_one_after_nine {e x : ℝ} (he : IsEvent e) (hx : x∈Icc (9/100) e) :
    (8997/10000:ℝ)<F 1 x := by
  have ht := axial_tangent 1 he ⟨by linarith [hx.1],hx.2⟩
    ⟨by norm_num,by linarith [(event_bounds he).1]⟩
    (fun u hu => (axial_curvature_one he hu).le)
  have hp := mul_nonneg Reference.first_at_nine.le (sub_nonneg.mpr hx.1)
  nlinarith [Reference.value_at_nine,sq_nonneg (x-9/100)]

theorem simple_axial_first (r : Row) (hr : r=2∨r=5) {e x : ℝ}
    (he : IsEvent e) (hx : x∈Icc 0 e) :
    (if r=2 then (1/50:ℝ) else -(1/10))<F1 r x := by
  have hb := axial_bounds he hx
  have hL := axial_sourceD_upper r he hx
  have hL0 : 0≤sourceD r (contact 0 x) := by
    linarith [sourceD_lower r (before_domain he hx).2.2,(coefficients r).2.2.1]
  have hp := mul_le_mul hL.le hb.2.2.2.2.2.1.le
    (by linarith [hb.2.2.2.2.1] : 0≤h x) (by linarith)
  dsimp [F1,angleFirst,h]
  rcases hr with rfl | rfl <;> norm_num [p,q] at hp ⊢ <;> nlinarith

theorem F_simple_lower (r : Row) (hr : r=2∨r=5) {e x : ℝ}
    (he : IsEvent e) (hx : x∈Icc 0 e) : (449/500:ℝ)<F r x := by
  have hh := derivative_reserve
    (fun u hu => (F_hasDerivAt r he hu).continuousAt.continuousWithinAt)
    (fun u hu => F_hasDerivAt r he (Ioo_subset_Icc_self hu))
    (fun u hu => (simple_axial_first r hr he (Ioo_subset_Icc_self hu)).le)
    (show (0:ℝ)∈Icc 0 e from ⟨le_rfl,by linarith [(event_bounds he).1]⟩) hx hx.1
  have hF := Reference.initial_value r
  have hcap : x<(27/250:ℝ) := by linarith [hx.2,(event_bounds he).2.1]
  rcases hr with rfl | rfl <;> norm_num [Reference.initialLower] at hh hF <;> linarith

theorem H_simple_positive (r : Row) (hr : r=2∨r=3∨r=4∨r=5) {e x : ℝ}
    (he : IsEvent e) (hx : x∈Icc 0 e) : 0<H r x := by
  have hL := sourceD_lower r (before_domain he hx).2.2
  have hg := projection_early he hx
  have hmul := mul_le_mul hL hg.1 (by norm_num)
    (by linarith [hL,(coefficients r).2.2.1] : 0≤sourceD r (contact 0 x))
  have hid : H r x=sourceD r (contact 0 x)*projection x+P r*rho-t r := by
    dsimp [H,first,stateSpeed,SecondWord.SameZero.k,projection]
    rw [ratio_zero]
    ring
  rw [hid]
  rcases hr with rfl | rfl | rfl | rfl <;>
    norm_num [p,q,P,t] at hmul ⊢ <;> nlinarith [rho_bounds.2]

def zeroAxialLower (x : ℝ) : ℝ :=
  44913/50000+(49/250)*x-(27/1000+(52/25)*x)^2/(78/25)

theorem zeroAxialLower_bound {x : ℝ} (hx : x∈Icc 0 (27/250)) : (449/500:ℝ)<zeroAxialLower x := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (27/250)) zeroAxialLower := by
    apply concave_of_deriv2
      (f':=fun y => 49/250-2*(52/25)*(27/1000+(52/25)*y)/(78/25))
      (f'':=fun _ => -2*(52/25)^2/(78/25))
    · intro y _
      dsimp [zeroAxialLower]
      convert (((hasDerivAt_id y).const_mul (49/250)).const_add (44913/50000)).sub
        (((((hasDerivAt_id y).const_mul (52/25)).const_add (27/1000)).pow 2).div_const (78/25)) using 1 <;> ring
    · intro y _
      convert ((((hasDerivAt_id y).const_mul (52/25)).const_add (27/1000)).
        const_mul (2*(52/25)/(78/25))).const_sub (49/250) using 1 <;> ring
    · intro y _
      norm_num
  exact concave_gt_of_endpoints hc hx (by norm_num [zeroAxialLower]) (by norm_num [zeroAxialLower])

theorem before_zero {B e x : ℝ} (he : IsEvent e) (hd : Domain B x) (hx : x≤e) :
    (449/500:ℝ)<value 0 B x := by
  have hx' : x∈Icc 0 e := ⟨hd.2.1.1,hx⟩
  have hh := contact_remainder 0 (before_domain he hx') hd hd.1.1
    (by norm_num : (0:ℝ)<39/25)
    (show 0≤(27/1000:ℝ)+(52/25)*x by positivity)
    (by linarith [H_zero_lower he hx'] : -(27/1000+(52/25)*x)≤first 0 0 x)
    (fun E hE => (early_curvature_zero he (between_domain (before_domain he hx') hd hE) hx).le)
  have hF := F_zero_linear he hx'
  have hbound := zeroAxialLower_bound
    (show x∈Icc 0 (27/250) from ⟨hd.2.1.1,by linarith [hx,(event_bounds he).2.1]⟩)
  dsimp [zeroAxialLower,F] at *
  linarith

theorem before_simple (r : Row) (hr : r=2∨r=3∨r=4∨r=5)
    {B e x : ℝ} (he : IsEvent e) (hd : Domain B x) (hx : x≤e) :
    (4489/5000:ℝ)<value r B x := by
  have hx' : x∈Icc 0 e := ⟨hd.2.1.1,hx⟩
  have hm := endpoint_minimum r (before_domain he hx') hd hd.1.1
    (H_simple_positive r hr he hx').le
  by_cases hpair : r=3∨r=4
  · exact (F_pair_lower r hpair he hx').trans_le hm
  · have hs : r=2∨r=5 := by rcases hr with h | h | h | h <;> tauto
    have hh := F_simple_lower r hs he hx'
    dsimp [F] at hh
    linarith

theorem before_one_after_nine {B e x : ℝ} (he : IsEvent e) (hd : Domain B x)
    (hx : x∈Icc (9/100) e) : (4489/5000:ℝ)<value 1 B x := by
  have hx' : x∈Icc 0 e := ⟨hd.2.1.1,hx.2⟩
  have hh := contact_remainder 1 (before_domain he hx') hd hd.1.1
    (by norm_num : (0:ℝ)<38/25) (by norm_num : (0:ℝ)≤71/1000)
    (H_one_lower he hx').le
    (fun E hE => (early_curvature_one he (between_domain (before_domain he hx') hd hE) hx.2).le)
  have hF := F_one_after_nine he hx
  dsimp [F] at hF
  norm_num at hh
  linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
