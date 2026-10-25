module

public import SquaresInCircles.Eight.Owners.Primary.Cap

/-!
# Eight squares: a negative GA1 with a noncanceling HG0 moved along the flat core

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
