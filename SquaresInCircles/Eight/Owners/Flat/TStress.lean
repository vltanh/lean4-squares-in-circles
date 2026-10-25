module

public import SquaresInCircles.Eight.Boundary.ActualOrdinaryBlocks
public import SquaresInCircles.Eight.Frames.Ordinary.NegativeSlope
public import SquaresInCircles.Eight.Owners.CancelingSupport
public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Owners.GA.Secant.Gain
public import SquaresInCircles.Eight.Owners.Negative.PrimaryEntry
public import SquaresInCircles.Eight.Owners.Primary.Cap

/-!
# Eight squares: exact flat-T stress and its secant gain

The T work is its original physical work, with
the actual flat radial coordinate `7/12`. In particular, the negative
radial force is not bounded by the full circle support. All other forces
and both E rotations are the same original seven-edge stress.
-/

section
/-!
## A negative GA1 with a noncanceling HG0 moved along the flat core

The endpoint is built on the core at the circle ceiling of the input
(`flat_core_negative_ga1_hg0_transport`). The two intervals are separated by HG alignment, and the
only other endpoint, the contact of the primary at zero tangent, is infeasible
(`zero_tangent_endpoint_infeasible`, `endpoint`). The statement concerns the neighbouring
constraints only.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace PrimaryCap

def plusDemand (P Θ x : ℝ) : ℝ :=
  1/2+(1-value P x)*Real.cos (x-Θ)+(1-K)*Real.sin (x-Θ)

def plusDerivative (P Θ x : ℝ) : ℝ :=
  (1-value P x*Real.tan x)*Real.cos (x-Θ)+
    (value P x-1)*Real.sin (x-Θ)

def minusDemand (P Θ x : ℝ) : ℝ :=
  1/2+(1-value P x)*Real.cos (Θ-x)+K*Real.sin (Θ-x)

def minusDerivative (P Θ x : ℝ) : ℝ :=
  Real.sin (Θ-x)-value P x*Real.sin Θ/Real.cos x

def minusSecond (P Θ x : ℝ) : ℝ :=
  -Real.cos (Θ-x)+(Real.sin Θ/Real.cos x)*(K-2*value P x*Real.tan x)

def demand (P Θ x : ℝ) : ℝ :=
  edgeWidth (x-Θ)-(7/12)*Real.sin (x-Θ)-
    (value P x-1/2)*Real.cos (x-Θ)

theorem demand_eq_plus {P Θ x : ℝ}
    (hx : x-Θ ∈ Icc 0 (7/10 : ℝ)) :
    demand P Θ x=plusDemand P Θ x := by
  rw [demand,edgeWidth_positive_formula hx]
  unfold plusDemand K
  ring

theorem demand_eq_minus {P Θ x : ℝ}
    (hx : Θ-x ∈ Icc 0 (7/10 : ℝ)) :
    demand P Θ x=minusDemand P Θ x := by
  have he : x-Θ= -(Θ-x) := by ring
  rw [demand,he,edgeWidth_negative_formula hx,Real.sin_neg,Real.cos_neg]
  unfold minusDemand K
  ring

theorem demand_iff_actual {P Θ x : ℝ} (H : SignedPoint) :
    demand P Θ x ≤ H.y ↔ zeroFeasible H (point P x) (x-Θ) 0 := by
  simp [demand,zeroFeasible,zeroProjection,point]
  constructor <;> intro h <;> linarith

theorem demand_strict_iff_actual {P Θ x : ℝ} (H : SignedPoint) :
    demand P Θ x < H.y ↔
      edgeWidth (x-Θ) < zeroProjection H (point P x) (x-Θ) 0 := by
  simp [demand,zeroProjection,point]
  constructor <;> intro h <;> linarith

theorem plusDemand_hasDerivAt (P Θ x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt (plusDemand P Θ) (plusDerivative P Θ x) x := by
  have hd := value_hasDerivAt P x hc
  have hcos : HasDerivAt (fun y => Real.cos (y-Θ)) (-Real.sin (x-Θ)) x := by
    convert ((hasDerivAt_id' x).sub_const Θ).cos using 1
    ring
  have hsin : HasDerivAt (fun y => Real.sin (y-Θ)) (Real.cos (x-Θ)) x := by
    convert ((hasDerivAt_id' x).sub_const Θ).sin using 1
    ring
  have hA := (((hasDerivAt_const x (1:ℝ)).fun_sub hd).fun_mul hcos).const_add (1/2)
  have hh := hA.fun_add (hsin.const_mul (1-K))
  show HasDerivAt (fun y => 1/2+(1-value P y)*Real.cos (y-Θ)+(1-K)*Real.sin (y-Θ)) _ x
  convert hh using 1
  rw [derivative_rewrite P x hc]
  unfold plusDerivative
  ring

theorem minusDemand_hasDerivAt (P Θ x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt (minusDemand P Θ) (minusDerivative P Θ x) x := by
  have hd := value_hasDerivAt P x hc
  have hcos : HasDerivAt (fun y => Real.cos (Θ-y)) (Real.sin (Θ-x)) x := by
    convert ((hasDerivAt_const x Θ).fun_sub (hasDerivAt_id' x)).cos using 1
    ring
  have hsin : HasDerivAt (fun y => Real.sin (Θ-y)) (-Real.cos (Θ-x)) x := by
    convert ((hasDerivAt_const x Θ).fun_sub (hasDerivAt_id' x)).sin using 1
    ring
  have hA := (((hasDerivAt_const x (1:ℝ)).fun_sub hd).fun_mul hcos).const_add (1/2)
  have hh := hA.fun_add (hsin.const_mul K)
  show HasDerivAt (fun y => 1/2+(1-value P y)*Real.cos (Θ-y)+K*Real.sin (Θ-y)) _ x
  convert hh using 1
  rw [derivative_rewrite P x hc]
  unfold minusDerivative
  have hs : Real.sin Θ=Real.sin (Θ-x)*Real.cos x+
      Real.cos (Θ-x)*Real.sin x := by
    rw [← Real.sin_add]
    congr 1
    ring
  rw [Real.tan_eq_sin_div_cos,hs]
  field_simp
  ring

theorem minusDerivative_hasDerivAt (P Θ x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt (minusDerivative P Θ) (minusSecond P Θ x) x := by
  have hd := value_hasDerivAt P x hc
  have hsin := (Real.hasDerivAt_sin (Θ-x)).comp x
    ((hasDerivAt_const x Θ).sub (hasDerivAt_id x))
  have hh := hsin.sub ((hd.mul_const (Real.sin Θ)).div
    (Real.hasDerivAt_cos x) hc)
  convert hh using 1
  · rfl
  · rw [derivative_rewrite P x hc]
    unfold minusSecond
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hc]
    ring

theorem plusDerivative_reserve {P Θ x : ℝ}
    (hP : 1/2 < P ∧ P < 183/200)
    (hx : x ∈ Icc 0 (9/20 : ℝ)) (hh : x-Θ ∈ Icc 0 (7/10 : ℝ))
    (hcap : 1/2 ≤ value P x) :
    2/25 < plusDerivative P Θ x := by
  obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse hh
  obtain ⟨hcx,hsx,ht0,ht⟩ := short_transport_trig hx
  have hD := value_le_position ⟨by linarith [hP.1],hP.2.le⟩
    (show x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith [hx.1,hx.2])
  have hprod : value P x*Real.tan x ≤ (183/400 : ℝ) := by
    have h := mul_le_mul (hD.trans hP.2.le) ht.le ht0 (by norm_num : (0:ℝ)≤183/200)
    norm_num at h
    exact h
  have hfirst : (217/400 : ℝ)*(3/4) ≤
      (1-value P x*Real.tan x)*Real.cos (x-Θ) := by
    apply mul_le_mul (by linarith) hc.le (by norm_num)
    linarith
  have hsecond : -(13/40 : ℝ) ≤
      (value P x-1)*Real.sin (x-Θ) := by
    have h := mul_nonneg (by linarith : 0≤value P x-1/2) hs0
    linarith
  unfold plusDerivative
  linarith

theorem minusSecond_reserve {P Θ x : ℝ}
    (hΘ : Θ ∈ Icc 0 (7/10 : ℝ))
    (hx : x ∈ Icc 0 (9/20 : ℝ)) (horder : x ≤ Θ)
    (hcap : 1/2 ≤ value P x) :
    minusSecond P Θ x < -(11/240) := by
  obtain ⟨hC,hS0,hS⟩ := transport_trig_coarse hΘ
  obtain ⟨hc,hs0,ht0,ht⟩ := short_transport_trig hx
  have hc1 := Real.cos_le_one x
  have hC1 := Real.cos_le_one Θ
  have hsin : Real.sin x ≤ Real.sin Θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hx.1,Real.pi_pos])
      (by linarith [hΘ.2,Real.pi_gt_three]) horder
  have hrecip := cos_add_reciprocal_ge_two hc
  have hprod : (Real.sin x)^2 ≤ Real.sin Θ*Real.sin x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsin) hs0]
  have hfirst : 2*(Real.sin x)^2 ≤
      Real.sin Θ*Real.sin x*(Real.cos x+1/Real.cos x) := by
    have h := mul_le_mul_of_nonneg_left hrecip (mul_nonneg hS0 hs0)
    nlinarith
  have hsecond : Real.cos Θ*(Real.sin x)^2 ≤ (Real.sin x)^2 := by
    exact mul_le_of_le_one_left (sq_nonneg _) hC1
  have hthird : 0 ≤ Real.sin Θ*Real.sin x*(2*value P x-1)/Real.cos x := by
    exact div_nonneg (mul_nonneg (mul_nonneg hS0 hs0) (by linarith)) hc.le
  have hid : Real.cos x*minusSecond P Θ x =
      -Real.cos Θ+K*Real.sin Θ+Real.cos Θ*(Real.sin x)^2-
        Real.sin Θ*Real.sin x*(Real.cos x+1/Real.cos x)-
        Real.sin Θ*Real.sin x*(2*value P x-1)/Real.cos x := by
    have hs2 : (Real.sin x)^2=1-(Real.cos x)^2 := by
      linarith [Real.sin_sq_add_cos_sq x]
    unfold minusSecond
    rw [Real.cos_sub,Real.tan_eq_sin_div_cos,hs2]
    field_simp
    ring
  have hupper : Real.cos x*minusSecond P Θ x < -(11/240) := by
    unfold K at hid
    nlinarith [sq_nonneg (Real.sin x)]
  have hn : minusSecond P Θ x < 0 := by
    by_contra! h
    have hp := mul_nonneg hc.le h
    linarith
  have hm := mul_nonneg (sub_nonneg.mpr hc1) (neg_nonneg.mpr hn.le)
  nlinarith

/-- Maximizing the negative intermediate tangent improves its HG0 contact. -/
theorem cap_improves_original {P Θ z g : ℝ} {H : SignedPoint}
    (hgap : |z-Θ| ≤ (7/10 : ℝ)) (hgcap : g+1/2 ≤ value P z)
    (hHG : zeroFeasible H ⟨7/12,-g⟩ (z-Θ) 0) :
    demand P Θ z ≤ H.y := by
  have hc := transport_cos_pos hgap
  have hm := mul_nonneg (by linarith : 0≤value P z-1/2-g) hc.le
  unfold zeroFeasible zeroProjection at hHG
  simp only [Matrix.cons_val_zero] at hHG
  unfold demand
  linarith

/-- An endpoint at zero tangent below H is infeasible. -/
theorem zero_tangent_endpoint_infeasible {P Θ x h : ℝ}
    (hh : h < 9/10) (hx : Θ-x ∈ Icc 0 (7/10 : ℝ))
    (hcap : value P x=1/2) :
    h < minusDemand P Θ x := by
  have hb := contactHeight_ge_half hx
  unfold minusDemand
  rw [hcap]
  unfold contactHeight at hb
  linarith

/-- The choice of the endpoint on the whole interval: `x = 0` or `x = Θ`, between `min 0 Θ` and
`max z Θ`, with the cap and the contact, strictly when `z ≠ Θ`. -/
theorem endpoint {P Θ z h : ℝ}
    (hP : 1/2 < P ∧ P < 183/200)
    (hz : 0 < z ∧ z ≤ 7/10)
    (hΘ : |Θ| ≤ (7/10 : ℝ)) (hgap : |z-Θ| ≤ (7/10 : ℝ))
    (hcap : 1/2 ≤ value P z)
    (hcontact : demand P Θ z ≤ h) (hh : h < 9/10) :
    ∃ x, (x=0 ∨ x=Θ) ∧
      x ∈ Icc (min 0 Θ) (max z Θ) ∧
      x ∈ Icc 0 (9/20 : ℝ) ∧
      1/2 ≤ value P x ∧ demand P Θ x ≤ h ∧
      (z≠Θ → demand P Θ x < h) := by
  obtain ⟨z₀,⟨hz₀,hz₀val⟩,hunique⟩ := exists_unique_zero_tangent hP.1 hP.2
  have hzz₀ : z ≤ z₀ := (cap_feasible_iff_before hP hz₀ hz₀val ⟨hz.1.le,hz.2⟩).1 hcap
  have hzshort : z < 9/20 := hzz₀.trans_lt hz₀.2
  by_cases horder : Θ ≤ z
  · let l : ℝ := max 0 Θ
    have hl0 : 0 ≤ l := le_max_left _ _
    have hlΘ : Θ ≤ l := le_max_right _ _
    have hlz : l ≤ z := max_le hz.1.le horder
    have hinterval (x : ℝ) (hx : x ∈ Icc l z) :
        x ∈ Icc 0 (9/20 : ℝ) ∧ x-Θ ∈ Icc 0 (7/10 : ℝ) ∧
          1/2 ≤ value P x := by
      have hx0 : 0 ≤ x := hl0.trans hx.1
      have hxwide : x∈Icc 0 (7/10 : ℝ) := ⟨hx0,hx.2.trans hz.2⟩
      refine ⟨⟨hx0,(hx.2.trans hzshort.le)⟩,⟨by linarith [hx.1],?_⟩,?_⟩
      · linarith [(abs_le.mp hgap).2,hx.2]
      · exact (cap_feasible_iff_before hP hz₀ hz₀val hxwide).2 (hx.2.trans hzz₀)
    have hmono : StrictMonoOn (plusDemand P Θ) (Icc l z) := by
      apply strict_increase_of_reserve (df := plusDerivative P Θ) (k := 2/25)
      · intro x hx
        exact (plusDemand_hasDerivAt P Θ x
          (short_transport_trig (hinterval x hx).1).1.ne').continuousAt.continuousWithinAt
      · intro x hx
        exact plusDemand_hasDerivAt P Θ x
          (short_transport_trig (hinterval x (Ioo_subset_Icc_self hx)).1).1.ne'
      · norm_num
      · intro x hx
        obtain ⟨hxs,hxh,hxc⟩ := hinterval x (Ioo_subset_Icc_self hx)
        exact (plusDerivative_reserve hP hxs hxh hxc).le
    have hlmem : l∈Icc l z := ⟨le_rfl,hlz⟩
    have hzmem : z∈Icc l z := ⟨hlz,le_rfl⟩
    have hle : demand P Θ l ≤ demand P Θ z := by
      rw [demand_eq_plus (hinterval l hlmem).2.1,
        demand_eq_plus (hinterval z hzmem).2.1]
      exact hmono.monotoneOn hlmem hzmem hlz
    refine ⟨l,?_,?_,(hinterval l hlmem).1,(hinterval l hlmem).2.2,
      hle.trans hcontact,?_⟩
    · rcases le_total Θ 0 with h | h
      · exact Or.inl (max_eq_left h)
      · exact Or.inr (max_eq_right h)
    · exact ⟨(min_le_left 0 Θ).trans hl0,hlz.trans (le_max_left _ _)⟩
    · intro hne
      have hlzt : l<z := by
        apply max_lt hz.1
        exact lt_of_le_of_ne horder (Ne.symm hne)
      have ht := hmono hlmem hzmem hlzt
      rw [← demand_eq_plus (hinterval l hlmem).2.1,
        ← demand_eq_plus (hinterval z hzmem).2.1] at ht
      exact ht.trans_le hcontact
  · have hΘz : z < Θ := lt_of_not_ge horder
    have hΘ0 : 0 < Θ := hz.1.trans hΘz
    have hΘwide : Θ∈Icc 0 (7/10 : ℝ) := ⟨hΘ0.le,(abs_le.mp hΘ).2⟩
    have hzstrict : z < z₀ := by
      by_contra! h
      have he : z=z₀ := le_antisymm hzz₀ h
      have hfail := zero_tangent_endpoint_infeasible (P := P) (Θ := Θ)
        (x := z) hh
        (show Θ-z∈Icc 0 (7/10 : ℝ) by
          constructor <;> linarith [(abs_le.mp hgap).1])
        (he ▸ hz₀val)
      rw [← demand_eq_minus (show Θ-z∈Icc 0 (7/10 : ℝ) by
        constructor <;> linarith [(abs_le.mp hgap).1])] at hfail
      linarith
    let u : ℝ := min Θ z₀
    have hu0 : 0 < u := lt_min hΘ0 hz₀.1
    have hzu : z < u := lt_min hΘz hzstrict
    have hinterval (x : ℝ) (hx : x∈Icc 0 u) :
        x∈Icc 0 (9/20 : ℝ) ∧ x≤Θ ∧ 1/2≤value P x := by
      have hxu : x≤z₀ := hx.2.trans (min_le_right Θ z₀)
      have hxΘ : x≤Θ := hx.2.trans (min_le_left Θ z₀)
      refine ⟨⟨hx.1,hxu.trans hz₀.2.le⟩,hxΘ,?_⟩
      apply (cap_feasible_iff_before hP hz₀ hz₀val
        ⟨hx.1,by linarith [hz₀.2]⟩).2 hxu
    have hedge : minusDemand P Θ 0 < minusDemand P Θ z ∨
        minusDemand P Θ u < minusDemand P Θ z := by
      apply strict_endpoint_of_second_derivative
        (df := minusDerivative P Θ) (ddf := minusSecond P Θ)
        (k := 11/240) (by norm_num) ⟨hz.1,hzu⟩
      · intro x hx
        exact minusDemand_hasDerivAt P Θ x
          (short_transport_trig (hinterval x hx).1).1.ne'
      · intro x hx
        exact minusDerivative_hasDerivAt P Θ x
          (short_transport_trig (hinterval x hx).1).1.ne'
      · intro x hx
        obtain ⟨hxs,hxΘ,hxc⟩ := hinterval x hx
        exact (minusSecond_reserve hΘwide hxs hxΘ hxc).le
    have hdz : demand P Θ z=minusDemand P Θ z :=
      demand_eq_minus ⟨by linarith,by linarith [hΘwide.2]⟩
    have h0d : demand P Θ 0=minusDemand P Θ 0 :=
      demand_eq_minus (by simpa using hΘwide)
    have hud : demand P Θ u=minusDemand P Θ u := by
      apply demand_eq_minus
      constructor
      · exact sub_nonneg.mpr (min_le_left Θ z₀)
      · linarith [hΘwide.2,hu0]
    rcases hedge with hleft | hright
    · refine ⟨0,Or.inl rfl,⟨min_le_left _ _,by linarith [le_max_right z Θ]⟩,
        ⟨le_rfl,by norm_num⟩,?_,?_,?_⟩
      · rw [value_zero]; exact hP.1.le
      · rw [h0d]; rw [hdz] at hcontact; exact (hleft.trans_le hcontact).le
      · intro _; rw [h0d]; rw [hdz] at hcontact; exact hleft.trans_le hcontact
    · have huΘ : u=Θ := by
        by_contra hne
        have hz₀Θ : z₀≤Θ := by
          by_contra! h
          exact hne (min_eq_left h.le)
        have hueq : u=z₀ := min_eq_right hz₀Θ
        have hfail := zero_tangent_endpoint_infeasible (P := P) (Θ := Θ)
          (x := u) hh
          (show Θ-u∈Icc 0 (7/10 : ℝ) by
            constructor <;> linarith [hΘwide.2,min_le_left Θ z₀,hu0])
          (hueq ▸ hz₀val)
        rw [hdz] at hcontact
        linarith
      refine ⟨u,Or.inr huΘ,?_,(hinterval u ⟨hu0.le,le_rfl⟩).1,
        (hinterval u ⟨hu0.le,le_rfl⟩).2.2,?_,?_⟩
      · rw [huΘ]
        exact ⟨min_le_right _ _,le_max_right _ _⟩
      · rw [hud]; rw [hdz] at hcontact; exact (hright.trans_le hcontact).le
      · intro _; rw [hud]; rw [hdz] at hcontact; exact hright.trans_le hcontact

end PrimaryCap

/-- A negative GA1 with a noncanceling HG0 moves along the flat core: G is replaced by a core
point `G'` strictly inside the circle with the HG0 and GA1 witnesses, at the frame `x = 0` or
`x = Θ`. -/
theorem flat_core_negative_ga1_hg0_transport
    {q Θ z : ℝ} {H G A : SignedPoint}
    (hq : q ≤ qCap)
    (hHs : H.Sorted) (hGs : G.Sorted) (hAs : A.Sorted)
    (hHc : H.Contained q) (hGc : G.Contained q) (hAc : A.Contained q)
    (hHcore : H.AvoidsCore) (hGcore : G.AvoidsCore) (hAcore : A.AvoidsCore)
    (hGa : G.a=7/12) (hGy : G.y≤0)
    (hz : 0<z ∧ z≤7/10) (hΘ : |Θ|≤(7/10 : ℝ))
    (hgap : |z-Θ|≤(7/10 : ℝ))
    (hHG : zeroFeasible H G (z-Θ) 0)
    (hGA : quarterFeasible G A (-z) 1) :
    ∃ (G' : SignedPoint) (x : ℝ),
      G'.a=G.a ∧ (x=0 ∨ x=Θ) ∧
      x∈Icc (min 0 Θ) (max z Θ) ∧
      G'.Sorted ∧ G'.Core ∧ G'.AvoidsCore ∧ G'.circle<q ∧
      zeroFeasible H G' (x-Θ) 0 ∧ quarterFeasible G' A (-x) 1 ∧
      (x=0 → quarterFeasible G' A (-x) 0) ∧
      (z≠Θ → edgeWidth (x-Θ)<zeroProjection H G' (x-Θ) 0) ∧ G'.y<0 := by
  let P := A.a-1/2
  let g := -G.y
  have hg0 : 0≤g := neg_nonneg.mpr hGy
  have hzwide : z∈Icc 0 (7/10 : ℝ) := ⟨hz.1.le,hz.2⟩
  obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse hzwide
  have hc0 : 0<Real.cos z := by linarith
  have hsp : 0<Real.sin z := Real.sin_pos_of_pos_of_lt_pi hz.1
    (by linarith [hz.2,Real.pi_gt_three])
  have hwidth := edgeWidth_ge_one (-z)
  have hGA' : edgeWidth (-z)≤A.a-(7/12)*Real.sin z-g*Real.cos z := by
    have h1 := hGA
    simp [quarterFeasible,quarterProjection,hGa,Real.sin_neg,Real.cos_neg] at h1
    rw [edgeWidth_neg]
    dsimp only [g]
    linarith
  have ha : 1<A.a := by
    have hm := mul_nonneg hg0 hc0.le
    nlinarith
  obtain ⟨hAl,hAu,hAy⟩ := SignedPoint.coordinate_bounds hAs hAcore hAc hq
  obtain ⟨hHl,hHu,hHy⟩ := SignedPoint.coordinate_bounds hHs hHcore hHc hq
  have hP : 1/2<P ∧ P<183/200 := by
    dsimp [P]
    constructor <;> linarith
  have hcap : g+1/2≤PrimaryCap.value P z := by
    unfold PrimaryCap.value
    rw [le_div_iff₀ hc0]
    rw [edgeWidth_negative_formula hzwide] at hGA'
    dsimp [P,PrimaryCap.K]
    linarith
  have hqbig : (5/2 : ℝ)<q := by
    have hay := abs_nonneg A.y
    unfold SignedPoint.Contained SignedPoint.circle at hAc
    nlinarith
  have hGrep : G=⟨7/12,-g⟩ := by
    cases G
    simp_all [g]
  have hstart := PrimaryCap.cap_improves_original hgap hcap
    (H := H) (by simpa [hGrep] using hHG)
  have hHupper : H.y<9/10 := (le_abs_self H.y).trans_lt hHy
  obtain ⟨x,hend,hframe,hxs,hxc,hxcontact,hstrict⟩ := PrimaryCap.endpoint
    hP hz hΘ hgap (by linarith) hstart hHupper
  let G' := PrimaryCap.point P x
  have hxwide : x∈Icc 0 (7/10 : ℝ) := ⟨hxs.1,by linarith [hxs.2]⟩
  obtain ⟨hs',hc',havoid,hcircle⟩ := PrimaryCap.point_geometric hP hxwide hxc hqbig
  have hcontact := PrimaryCap.actual_primary_contact (A := A)
    (P := P) (x := x) (by dsimp [P]; ring) hxwide
  refine ⟨G',x,by simp [G',PrimaryCap.point,hGa],hend,hframe,
    hs',hc',havoid,hcircle,(PrimaryCap.demand_iff_actual H).1 hxcontact,
    hcontact.ge,?_,?_,?_⟩
  · intro hx0
    subst x
    have h1 : quarterFeasible G' A (-0) 1 := hcontact.ge
    rw [neg_zero] at h1 ⊢
    exact (quarter_low_tie G' A).2 h1
  · intro hne
    exact (PrimaryCap.demand_strict_iff_actual H).1 (hstrict hne)
  · rcases hend with hx0 | hxΘ
    · simp [G',PrimaryCap.point,hx0,PrimaryCap.value]
      linarith [hP.1]
    · have haligned := (PrimaryCap.demand_iff_actual H).1 hxcontact
      rw [hxΘ,sub_self] at haligned
      have hy : 1≤H.y-G'.y := by
        simpa [G',hxΘ,zeroFeasible,zeroProjection] using haligned
      linarith

end SquaresInCircles.Eight
end
end
end

section
/-!
## Negative GA1 with HG2: the canceling companion

The input is the original same-radius signed triple.
An unavailable GA0 forces the flat-core and original-A cuts. Negative HG
error reselects HG0 on the same state; positive HG error is transported by
a derivative estimate proved only where the actual HG2 contact is feasible.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace CancelingSupport

def composite (P a b Θ x : ℝ) : ℝ := PrimaryCap.value P x+S a b (x-Θ)

def compositeDerivative (P a b Θ x : ℝ) : ℝ :=
  PrimaryCap.derivative P x+U a b (x-Θ)

theorem composite_hasDerivAt (P a b Θ x : ℝ) (hc : Real.cos x≠0) :
    HasDerivAt (composite P a b Θ) (compositeDerivative P a b Θ x) x := by
  have hd := PrimaryCap.value_hasDerivAt P x hc
  have hs := (Real.hasDerivAt_sin (x-Θ)).comp x ((hasDerivAt_id x).sub_const Θ)
  have hcos := (Real.hasDerivAt_cos (x-Θ)).comp x ((hasDerivAt_id x).sub_const Θ)
  convert hd.add ((hs.const_mul (a-1/2)).add (hcos.const_mul (b-1/2))) using 1
  · rfl
  · unfold compositeDerivative U
    ring

theorem composite_actual_strict_iff {P Θ x : ℝ} (H : SignedPoint)
    (hx : x-Θ∈Icc 0 (7/10 : ℝ)) :
    1<composite P H.a H.y Θ x ↔
      edgeWidth (x-Θ)<zeroProjection H (PrimaryCap.point P x) (x-Θ) 2 := by
  rw [edgeWidth_positive_formula hx]
  simp [zeroProjection,PrimaryCap.point,composite,S]
  constructor <;> intro h <;> linarith

theorem composite_negative_on_feasible {P a b Θ z x q : ℝ}
    (hP : 1/2<P ∧ P<p₀) (hz : z∈Icc 0 (1/4 : ℝ))
    (hx : x∈Icc 0 z) (hh : x-Θ∈Icc 0 (7/10 : ℝ))
    (hcap : 1/2≤PrimaryCap.value P z)
    (hcircle : (a+1/2)^2+(b+1/2)^2≤q) (hq : q≤qCap)
    (hfeasible : 1≤composite P a b Θ x) :
    compositeDerivative P a b Θ x < -(1/10) := by
  have hPwide : 0≤P ∧ P≤183/200 := by
    dsimp [p₀] at hP; constructor <;> linarith [hP.1,hP.2]
  have hxwide : x∈Icc 0 (7/10 : ℝ) := ⟨hx.1,by linarith [hx.2,hz.2]⟩
  have hzwide : z∈Icc 0 (7/10 : ℝ) := ⟨hz.1,by linarith [hz.2]⟩
  have hanti := (PrimaryCap.value_strictAnti hPwide).antitoneOn hxwide hzwide hx.2
  have hDupper := PrimaryCap.value_le_position hPwide hxwide
  have hD : PrimaryCap.value P x∈Icc (1/2) p₀ :=
    ⟨hcap.trans hanti,hDupper.trans hP.2.le⟩
  obtain ⟨ht0,ht⟩ := quarter_tangent ⟨hx.1,hx.2.trans hz.2⟩
  have hprod : PrimaryCap.value P x*Real.tan x<1/5 := by
    have hh := mul_le_mul hD.2 ht.le ht0 (by norm_num : (0:ℝ)≤p₀)
    norm_num [p₀] at hh
    linarith
  have hc := transport_cos_pos (by rw [abs_of_nonneg hx.1]; linarith [hxwide.2])
  have hrewrite := PrimaryCap.derivative_rewrite P x hc.ne'
  have hbranches := actual_H_branches hD hh hcircle hq hfeasible
  have hcorr := correlated_upper hP hz hcap hx
  unfold compositeDerivative
  rcases hbranches with hleft | hright
  · unfold PrimaryCap.K at hrewrite
    linarith
  · unfold correlated at hcorr
    unfold PrimaryCap.K at hrewrite
    linarith

/-- Positive canceling HG error reaches G=A or G=H on the same flat core. -/
theorem positive_endpoint {q P Θ z : ℝ} {H : SignedPoint}
    (hP : 1/2<P ∧ P<p₀)
    (hz : 0<z ∧ z<1/4) (horder : Θ<z)
    (hgap : z-Θ≤7/10)
    (hcap : 1/2≤PrimaryCap.value P z)
    (hcircle : (H.a+1/2)^2+(H.y+1/2)^2≤q)
    (hq : q≤qCap) (hqbig : 5/2<q)
    (hstart : 1≤composite P H.a H.y Θ z) :
    ∃x, (x=0 ∨ x=Θ) ∧
      x∈Icc (min 0 Θ) (max z Θ) ∧ x∈Icc 0 (9/20 : ℝ) ∧
      (PrimaryCap.point P x).Sorted ∧ (PrimaryCap.point P x).Core ∧
      (PrimaryCap.point P x).AvoidsCore ∧ (PrimaryCap.point P x).circle<q ∧
      edgeWidth (x-Θ)<zeroProjection H (PrimaryCap.point P x) (x-Θ) 2 := by
  let l : ℝ := max 0 Θ
  have hl0 : 0≤l := le_max_left _ _
  have hlΘ : Θ≤l := le_max_right _ _
  have hlz : l<z := max_lt hz.1 horder
  have hPwide : 1/2<P ∧ P<183/200 := by
    dsimp [p₀] at hP; exact ⟨hP.1,by linarith [hP.2]⟩
  have hinterval (x : ℝ) (hx : x∈Icc l z) :
      x∈Icc 0 z ∧ x-Θ∈Icc 0 (7/10 : ℝ) := by
    exact ⟨⟨hl0.trans hx.1,hx.2⟩,⟨by linarith [hx.1],by linarith [hx.2]⟩⟩
  have hcontinue := feasible_left_continuation
    (f := composite P H.a H.y Θ) (df := compositeDerivative P H.a H.y Θ)
    (l := l) (u := z) (b := 1)
    (by
      intro x hx
      exact (composite_hasDerivAt P H.a H.y Θ x
        (transport_cos_pos (by
          rw [abs_of_nonneg ((hinterval x hx).1.1)]
          linarith [hx.2,hz.2])).ne').continuousAt.continuousWithinAt)
    (by
      intro x hx
      exact composite_hasDerivAt P H.a H.y Θ x
        (transport_cos_pos (by
          rw [abs_of_nonneg ((hinterval x hx).1.1)]
          linarith [hx.2,hz.2])).ne')
    (by
      intro x hx hfeas
      have hneg := composite_negative_on_feasible hP ⟨hz.1.le,hz.2.le⟩
        (hinterval x hx).1 (hinterval x hx).2 hcap hcircle hq hfeas
      linarith)
    hstart
  have hlcontact : 1<composite P H.a H.y Θ l :=
    hstart.trans_lt (hcontinue l ⟨le_rfl,hlz⟩)
  have hlwide : l∈Icc 0 (7/10 : ℝ) := ⟨hl0,by linarith⟩
  have hcapl : 1/2≤PrimaryCap.value P l := by
    have hanti := (PrimaryCap.value_strictAnti
      ⟨by linarith [hP.1],hPwide.2.le⟩).antitoneOn
      hlwide ⟨hz.1.le,by linarith [hz.2]⟩ hlz.le
    exact hcap.trans hanti
  obtain ⟨hs,hc,havoid,hinside⟩ := PrimaryCap.point_geometric hPwide hlwide hcapl hqbig
  refine ⟨l,?_,⟨(min_le_left _ _).trans hl0,hlz.le.trans (le_max_left _ _)⟩,
    ⟨hl0,by linarith⟩,hs,hc,havoid,hinside,?_⟩
  · rcases le_total Θ 0 with h | h
    · exact Or.inl (max_eq_left h)
    · exact Or.inr (max_eq_right h)
  · exact (composite_actual_strict_iff H (hinterval l ⟨le_rfl,hlz.le⟩).2).1 hlcontact

end CancelingSupport

/-- For nonpositive HG error the same original point already admits HG0.
The strict case retains the real physical projection, not merely its label. -/
theorem canceling_negative_error_reselection
    {H G : SignedPoint} {h : ℝ}
    (hHs : H.Sorted) (_hGs : G.Sorted)
    (hHy : 0≤H.y) (hGy : G.y≤0)
    (hGa : G.a=7/12) (hgsmall : |G.y|<39/250)
    (hh : -(7/10 : ℝ)≤h ∧ h<0)
    (hHG : zeroFeasible H G h 2) :
    edgeWidth h<zeroProjection H G h 0 := by
  have hc := transport_cos_pos (by rw [abs_of_neg hh.2]; linarith [hh.1])
  have hc1 := Real.cos_le_one h
  have hs : Real.sin h<0 := by
    have hp := Real.sin_pos_of_pos_of_lt_pi (x := -h) (by linarith)
      (by linarith [hh.1,Real.pi_gt_three])
    simpa using hp
  have hwidth := edgeWidth_ge_one h
  have hproj : edgeWidth h≤H.a*Real.sin h+H.y*Real.cos h+|G.y| := by
    have h1 := hHG
    simp [zeroFeasible,zeroProjection] at h1
    rw [abs_of_nonpos hGy]
    linarith
  have hfirst := mul_neg_of_pos_of_neg hHs.1 hs
  have hsecond := mul_le_mul_of_nonneg_left hc1 hHy
  have hHyhigh : 211/250<H.y := by linarith
  have hHa : G.a<H.a := by
    rw [hGa]
    have hh := hHs.2
    rw [abs_of_nonneg hHy] at hh
    linarith
  have hdiff : zeroProjection H G h 0-zeroProjection H G h 2 =
      (G.a-H.a)*Real.sin h+(H.y-|G.y|)*(1-Real.cos h) := by
    simp [zeroProjection,abs_of_nonpos hGy]
    ring
  have hp := mul_pos_of_neg_of_neg (sub_neg.mpr hHa) hs
  have hnonneg := mul_nonneg (show 0≤H.y-|G.y| by linarith)
    (sub_nonneg.mpr hc1)
  have hgt : zeroProjection H G h 2<zeroProjection H G h 0 := by
    linarith
  exact hHG.trans_lt hgt

/-- Actual same-q canceling endpoint, including both HG error signs and
zero HG alignment. Its output explicitly identifies the surviving owner. -/
theorem flat_core_negative_ga1_hg2_transport
    {q Θ z : ℝ} {H G A : SignedPoint}
    (hq : q≤qCap)
    (hHs : H.Sorted) (hGs : G.Sorted) (hAs : A.Sorted)
    (hHc : H.Contained q) (hGc : G.Contained q) (hAc : A.Contained q)
    (hHcore : H.AvoidsCore) (hGcore : G.AvoidsCore) (hAcore : A.AvoidsCore)
    (hGb : G.Boundary q) (hHy : 0≤H.y) (hGy : G.y≤0) (hAy : 0≤A.y)
    (hz : 0<z ∧ z≤7/10) (hΘ : |Θ|≤(7/10 : ℝ))
    (hgap : |z-Θ|≤(7/10 : ℝ))
    (hHG : zeroFeasible H G (z-Θ) 2)
    (hGA : quarterFeasible G A (-z) 1)
    (hnotGA0 : ¬quarterFeasible G A (-z) 0) :
    ∃ (G' : SignedPoint) (x : ℝ) (j : Fin 4),
      (j=0 ∨ j=2) ∧ G'.a=G.a ∧ (x=0 ∨ x=Θ) ∧
      x∈Icc (min 0 Θ) (max z Θ) ∧
      G'.Sorted ∧ G'.Core ∧ G'.AvoidsCore ∧ G'.circle<q ∧
      zeroFeasible H G' (x-Θ) j ∧ quarterFeasible G' A (-x) 1 ∧
      (x=0 → quarterFeasible G' A (-x) 0) ∧
      (z≠Θ → edgeWidth (x-Θ)<zeroProjection H G' (x-Θ) j) ∧ G'.y<0 := by
  obtain ⟨hGa,hgsmall,hzsmall,hAb,hPupper⟩ := exceptional_negative_primary_cuts
    hGs hAs hGb hAc hq hGy hAy hz hGA hnotGA0
  rcases lt_trichotomy z Θ with hnegative | haligned | hpositive
  · have hstrict := canceling_negative_error_reselection hHs hGs hHy hGy
      hGa hgsmall ⟨(abs_le.mp hgap).1,sub_neg.mpr hnegative⟩ hHG
    obtain ⟨G',x,ha,hend,hframe,hs,hc,havoid,hcircle,hHG',hGA',hhard,hstrict',hy'⟩ :=
      flat_core_negative_ga1_hg0_transport hq hHs hGs hAs hHc hGc hAc
        hHcore hGcore hAcore hGa hGy hz hΘ hgap hstrict.le hGA
    exact ⟨G',x,0,Or.inl rfl,ha,hend,hframe,hs,hc,havoid,hcircle,
      hHG',hGA',hhard,hstrict',hy'⟩
  all_goals
    let P : ℝ := A.a-1/2
    have hzwide : z∈Icc 0 (7/10 : ℝ) := ⟨hz.1.le,hz.2⟩
    have hcz := transport_cos_pos (by rw [abs_of_pos hz.1]; exact hz.2)
    have hsz := Real.sin_pos_of_pos_of_lt_pi hz.1
      (by linarith [hz.2,Real.pi_gt_three])
    have hwidth := edgeWidth_ge_one (-z)
    have hproj : edgeWidth (-z)≤A.a-(7/12)*Real.sin z-|G.y| * Real.cos z := by
      have h1 := hGA
      simp [quarterFeasible,quarterProjection,hGa,Real.sin_neg,Real.cos_neg] at h1
      rw [abs_of_nonpos hGy,edgeWidth_neg]
      linarith
    have hAgt : 1<A.a := by
      have hm := mul_nonneg (abs_nonneg G.y) hcz.le
      nlinarith
    have hP : 1/2<P ∧ P<CancelingSupport.p₀ := by
      dsimp [P,CancelingSupport.p₀]
      constructor <;> linarith
    have hPwide : 1/2<P ∧ P<183/200 := by
      exact ⟨hP.1,by dsimp [CancelingSupport.p₀] at hP; linarith [hP.2]⟩
    have hcap : |G.y|+1/2≤PrimaryCap.value P z := by
      unfold PrimaryCap.value
      rw [le_div_iff₀ hcz]
      rw [edgeWidth_negative_formula hzwide] at hproj
      dsimp [P,PrimaryCap.K]
      linarith
    have hcap0 : 1/2≤PrimaryCap.value P z := by linarith [abs_nonneg G.y]
    have hqbig : (5/2 : ℝ)<q := by
      have ha := abs_nonneg A.y
      unfold SignedPoint.Contained SignedPoint.circle at hAc
      nlinarith
    have hcircle : (H.a+1/2)^2+(H.y+1/2)^2≤q := by
      simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hHy] using hHc
  · let G' := PrimaryCap.point P z
    obtain ⟨hs,hc,havoid,hinside⟩ := PrimaryCap.point_geometric
      hPwide hzwide hcap0 hqbig
    have hprimary := PrimaryCap.actual_primary_contact (A := A)
      (P := P) (x := z) (by dsimp [P]; ring) hzwide
    have htransverse : zeroFeasible H G' (z-Θ) 2 := by
      have hslack := hHG
      rw [haligned,sub_self] at hslack ⊢
      simp [zeroFeasible,zeroProjection,G',PrimaryCap.point] at hslack ⊢
      linarith [abs_of_nonpos hGy]
    refine ⟨G',z,2,Or.inr rfl,by simp [G',PrimaryCap.point,hGa],
      Or.inr haligned,?_,hs,hc,havoid,hinside,htransverse,hprimary.ge,?_,?_,?_⟩
    · exact ⟨(min_le_left 0 Θ).trans hz.1.le,le_max_left _ _⟩
    · intro hz0
      exact False.elim (ne_of_gt hz.1 hz0)
    · intro hne
      exact False.elim (hne haligned)
    · have hHb := (H.coordinate_bounds hHs hHcore hHc hq).2.2
      have hHyupper : H.y<9/10 := (le_abs_self _).trans_lt hHb
      have hy : 1≤H.y-G'.y := by
        simpa [haligned,zeroFeasible,zeroProjection] using htransverse
      linarith
  · have hstart : 1≤CancelingSupport.composite P H.a H.y Θ z := by
      have hh := hHG
      rw [zeroFeasible,edgeWidth_positive_formula
        ⟨sub_nonneg.mpr hpositive.le,(abs_le.mp hgap).2⟩] at hh
      simp [zeroProjection] at hh
      unfold CancelingSupport.composite CancelingSupport.S
      linarith [abs_of_nonpos hGy]
    obtain ⟨x,hend,hframe,hxs,hs,hc,havoid,hinside,hstrict⟩ :=
      CancelingSupport.positive_endpoint hP ⟨hz.1,hzsmall⟩ hpositive
        (abs_le.mp hgap).2 hcap0 hcircle hq hqbig hstart
    let G' := PrimaryCap.point P x
    have hxwide : x∈Icc 0 (7/10 : ℝ) := ⟨hxs.1,by linarith [hxs.2]⟩
    have hprimary := PrimaryCap.actual_primary_contact (A := A)
      (P := P) (x := x) (by dsimp [P]; ring) hxwide
    refine ⟨G',x,2,Or.inr rfl,by simp [G',PrimaryCap.point,hGa],
      hend,hframe,hs,hc,havoid,hinside,hstrict.le,hprimary.ge,?_,(fun _ => hstrict),?_⟩
    · intro hx0
      subst x
      have h1 : quarterFeasible G' A (-0) 1 := hprimary.ge
      rw [neg_zero] at h1 ⊢
      exact (quarter_low_tie G' A).2 h1
    · rcases hend with hx0 | hxΘ
      · simp [G',PrimaryCap.point,hx0,PrimaryCap.value]
        linarith [hP.1]
      · have hHb := (H.coordinate_bounds hHs hHcore hHc hq).2.2
        have hHyupper : H.y<9/10 := (le_abs_self _).trans_lt hHb
        have hslack : 1<H.y-G'.y := by
          simpa [G',hxΘ,zeroProjection] using hstrict
        linarith

end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.FlatTStress
open Candidate SignedStress SecondaryEStress PositiveAngularEnvelope
open PositivePrimaryBaselines ActualOrdinaryBlocks OrdinaryNegativeEnvelope GlobalGA

def flatBound (C : SignedCycle) (ab bt td : Fin 4) (n k l b t R : ℝ) : Vertex → ℝ :=
  let F := forces C ab bt td n k l b t
  ![signedSupport R 1 (F H),circleSupport R (F G),
    signedSupport R 1 (F A),signedSupport R (-1) (F B),
    work (F T) (C.point T),signedSupport R (-1) (F D),0]

def flatDefect (C : SignedCycle) (ab bt td : Fin 4) (n k l b t R : ℝ) : ℝ :=
  demand C (weights n k l b t)-∑ i,flatBound C ab bt td n k l b t R i

theorem necessary_flat_stress {C : SignedCycle} {ab bt td : Fin 4}
    {n k l b t R : ℝ} (hR : 0≤R)
    (hs : ∀ i,i≠E → (C.point i).Sorted)
    (hc : ∀ i,i≠E → (C.point i).Contained (R^2))
    (hnormal : C.NormalAnchors) (hw : 0≤n ∧ 0≤k ∧ 0≤l ∧ 0≤b ∧ 0≤t)
    (hf : ∀ i,C.Feasible i (owners ab bt td i)) :
    flatDefect C ab bt td n k l b t R≤0 := by
  have hweight : ∀ i,0≤weights n k l b t i := by
    intro i
    fin_cases i <;> simp [weights] <;> linarith [hw.1,hw.2.1,hw.2.2.1,
      hw.2.2.2.1,hw.2.2.2.2]
  have hbound : ∀ i,work (forces C ab bt td n k l b t i) (C.point i)≤
      flatBound C ab bt td n k l b t R i := by
    intro i
    fin_cases i
    · exact work_le_signed_support hR (hc H (by decide)) (Or.inl rfl)
        (by simp [abs_of_nonneg hnormal.H_nonneg]) _
    · exact work_le_circleSupport hR (hs G (by decide)) (hc G (by decide)) _
    · exact work_le_signed_support hR (hc A (by decide)) (Or.inl rfl)
        (by simp [abs_of_nonneg hnormal.A_nonneg]) _
    · exact work_le_signed_support hR (hc B (by decide)) (Or.inr rfl)
        (by simp [abs_of_nonpos hnormal.B_nonpos]) _
    · rfl
    · exact work_le_signed_support hR (hc D (by decide)) (Or.inr rfl)
        (by simp [abs_of_nonpos hnormal.D_nonpos]) _
    · change work (forces C ab bt td n k l b t E) (C.point E)≤flatBound C ab bt td n k l b t R E
      rw [force_E]
      simp [work,flatBound,E]
  have h := weighted_separation_le hweight hf hbound
  dsimp [flatDefect]
  linarith

theorem necessary_flat_at_cap {C : SignedCycle} {q : ℝ} {ab bt td : Fin 4}
    {n k l b t : ℝ} (hq : q≤qCap) (hC : C.Necessary q)
    (hnormal : C.NormalAnchors) (hw : 0≤n ∧ 0≤k ∧ 0≤l ∧ 0≤b ∧ 0≤t)
    (hf : ∀ i,C.Feasible i (owners ab bt td i)) :
    flatDefect C ab bt td n k l b t (Real.sqrt qCap)≤0 := by
  apply necessary_flat_stress (Real.sqrt_nonneg _) (fun i _ => hC.sorted i) _ hnormal hw hf
  intro i _
  rw [Real.sq_sqrt (show 0≤qCap by norm_num [qCap])]
  exact (hC.contained i).trans hq

theorem flatDefect_as_anchors {C : SignedCycle} {ab bt td : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (n k l b t R : ℝ) :
    flatDefect C ab bt td n k l b t R=
      demand C (weights n k l b t)+anchorHalfShift C ab bt td n k l b t-
      R*anchorNormSum C ab bt td n k l b t-
      circleSupport R (forces C ab bt td n k l b t G)-
      work (forces C ab bt td n k l b t T) (C.point T) := by
  have hsum : (∑ i,flatBound C ab bt td n k l b t R i)=
      signedSupport R 1 (forces C ab bt td n k l b t H)+
      circleSupport R (forces C ab bt td n k l b t G)+
      signedSupport R 1 (forces C ab bt td n k l b t A)+
      signedSupport R (-1) (forces C ab bt td n k l b t B)+
      work (forces C ab bt td n k l b t T) (C.point T)+
      signedSupport R (-1) (forces C ab bt td n k l b t D) := by
    simp [flatBound,Fin.sum_univ_succ,H,G,A,B,T,D]
    ring
  rw [flatDefect,hsum,H_support,A_support hab,B_support hab hbt,D_support htd]
  dsimp [anchorHalfShift,anchorNormSum]
  ring

def secantCharge (R c a s : ℝ) : ℝ :=
  c*(1/Real.cos s-1+(13/12)*Real.tan s)-
    R*(pairNorm a (c/Real.cos s) 0-pairNorm a c 0)

theorem zero_norm_scale {c : ℝ} (hc : 0<c) (a w : ℝ) :
    pairNorm a (c*w) 0=c*Real.sqrt ((a/c)^2+w^2) := by
  have he : c*(a/c)=a := by field_simp [hc.ne']
  simpa only [he,pairNorm_zero] using pairNorm_homogeneous hc.le (a/c) w 0

theorem secantCharge_eq {c s : ℝ} (hc : 0<c) (hs : s∈Icc 0 frameCap) (a : ℝ) :
    secantCharge (Real.sqrt qCap) c a s=c*secantGain qCap (a/c) s := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  rw [secantGain_eq_secant_expression qCap (a/c) hcos]
  have hN : pairNorm a (c/Real.cos s) 0=
      c*Real.sqrt ((1/Real.cos s)^2+(a/c)^2) := by
    simpa only [div_eq_mul_inv,one_mul,add_comm] using zero_norm_scale hc a (1/Real.cos s)
  have hZ : pairNorm a c 0=c*Real.sqrt (1+(a/c)^2) := by
    simpa only [mul_one,one_pow,add_comm] using zero_norm_scale hc a 1
  dsimp [secantCharge]
  rw [hN,hZ]
  ring

def negativeTDIncrement (C : SignedCycle) (ab : Fin 4) (R k l c η s : ℝ) : ℝ :=
  ∑ i,(blocks C ab 2 2 (tiltedWeight k η (delta C.theta G)) k l c (c/Real.cos s) i).increment R

def negativeBTIncrement (C : SignedCycle) (ab : Fin 4) (R k l c η s : ℝ) : ℝ :=
  ∑ i,(blocks C ab 3 0 (tiltedWeight k η (delta C.theta G)) k l (c/Real.cos s) c i).increment R

theorem negative_TD_decomposition {C : SignedCycle} {ab : Fin 4} {R k l c η s : ℝ}
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hη : 0≤η)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hG : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hT : delta C.theta T= -s) (hflat : (C.point T).a=7/12) :
    flatDefect C ab 2 2 (tiltedWeight k η (delta C.theta G)) k l c (c/Real.cos s) R=
      secondaryBaseline R k l c η (delta C.theta G)+secantCharge R c 1 s+
        negativeTDIncrement C ab R k l c η s := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  rw [flatDefect_as_anchors hab (Or.inl rfl) (Or.inr rfl),
    positive_G_support hk hη hG,negative_TD_work hcos.ne' hT hflat,demand_eq]
  rw [width_eq (hsmall H),width_eq (hsmall G),width_eq (hsmall A),
    width_eq (hsmall B),width_eq (hsmall D),width_eq (hsmall E),
    hT,edgeWidth_negative_formula hs,psi_positive hG]
  rcases hab with rfl | rfl <;>
    simp [negativeTDIncrement,blocks,Block.increment,Fin.sum_univ_succ,
      anchorHalfShift,anchorNormSum,secondaryBaseline,secantCharge,zeroNorms,
      primaryCoefficient,primarySupport,tiltedWeight,PositiveAngularEnvelope.phi,
      Real.tan_eq_sin_div_cos,pairNorm_symm k l,pairNorm_symm _ 1] <;>
    field_simp [hcos.ne'] <;> ring

theorem negative_BT_decomposition {C : SignedCycle} {ab : Fin 4} {R k l c η s : ℝ}
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hη : 0≤η)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hG : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hB : delta C.theta B= -s) (hflat : (C.point T).a=7/12) :
    flatDefect C ab 3 0 (tiltedWeight k η (delta C.theta G)) k l (c/Real.cos s) c R=
      secondaryBaseline R k l c η (delta C.theta G)+secantCharge R c l s+
        negativeBTIncrement C ab R k l c η s := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  rw [flatDefect_as_anchors hab (Or.inr rfl) (Or.inl rfl),
    positive_G_support hk hη hG,negative_BT_work hcos.ne' hB hflat,demand_eq]
  rw [width_eq (hsmall H),width_eq (hsmall G),width_eq (hsmall A),
    width_eq (hsmall T),width_eq (hsmall D),width_eq (hsmall E),
    hB,edgeWidth_negative_formula hs,psi_positive hG]
  rcases hab with rfl | rfl <;>
    simp [negativeBTIncrement,blocks,Block.increment,Fin.sum_univ_succ,
      anchorHalfShift,anchorNormSum,secondaryBaseline,secantCharge,zeroNorms,
      primaryCoefficient,primarySupport,tiltedWeight,PositiveAngularEnvelope.phi,
      Real.tan_eq_sin_div_cos,pairNorm_symm k l,pairNorm_symm _ 1] <;>
    field_simp [hcos.ne'] <;> ring

theorem negative_TD_necessary {C : SignedCycle} {q k l c η s : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hl : 0≤l) (hc : 0<c) (hη : 0≤η)
    (hG : 0≤delta C.theta G) (hs : s∈Icc 0 frameCap)
    (hT : delta C.theta T= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (owners ab 2 2 i)) :
    secondaryBaseline (Real.sqrt qCap) k l c η (delta C.theta G)+
      c*secantGain qCap (1/c) s+
      negativeTDIncrement C ab (Real.sqrt qCap) k l c η s≤0 := by
  have hsmall : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hG' : delta C.theta G∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hsmall G)⟩
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have hnec := necessary_flat_at_cap hq hC hnormal
    ⟨tiltedWeight_nonneg hk hη hG',hk,hl,hc.le,div_nonneg hc.le hcos.le⟩ hf
  rw [negative_TD_decomposition hab hk hη hsmall hG' hs hT hflat,secantCharge_eq hc hs] at hnec
  exact hnec

theorem negative_BT_necessary {C : SignedCycle} {q k l c η s : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hl : 0≤l) (hc : 0<c) (hη : 0≤η)
    (hG : 0≤delta C.theta G) (hs : s∈Icc 0 frameCap)
    (hB : delta C.theta B= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (owners ab 3 0 i)) :
    secondaryBaseline (Real.sqrt qCap) k l c η (delta C.theta G)+
      c*secantGain qCap (l/c) s+
      negativeBTIncrement C ab (Real.sqrt qCap) k l c η s≤0 := by
  have hsmall : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hG' : delta C.theta G∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hsmall G)⟩
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have hnec := necessary_flat_at_cap hq hC hnormal
    ⟨tiltedWeight_nonneg hk hη hG',hk,hl,div_nonneg hc.le hcos.le,hc.le⟩ hf
  rw [negative_BT_decomposition hab hk hη hsmall hG' hs hB hflat,secantCharge_eq hc hs] at hnec
  exact hnec

end SquaresInCircles.Eight.FlatTStress
end
end
end
