module

public import SquaresInCircles.Eight.Owners.Hard.SplitConstruction

/-!
# Eight squares: uniform bounds from the aligned four-anchor chain

The circles of the two middle squares are each used once: with the AB inequality they give
`A.a + B.a < 7547/3125` (`middle_primary_sum`). The rational vector `(X0, Y0)` lies outside the
circle `qCap`, and its support bounds the primary sum of H and D (`outer_primary_sum`). The
convexity of the cap then gives the short total span `t + u < 11/50` (`short_span`). E and its
owner, sign, frame and radial kind do not enter.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace AlignedChainBounds
open HardSplitCap

abbrev X0 : ℝ := 1873/1250
abbrev Y0 : ℝ := 4039/3125

theorem single_contact_bounds {q t : ℝ} {H A : SignedPoint}
    (hq : q≤qCap) (hHs : H.Sorted) (hAs : A.Sorted)
    (hHcore : H.AvoidsCore) (hAcore : A.AvoidsCore)
    (hHc : H.Contained q) (hAc : A.Contained q)
    (hHy : 0≤H.y) (hAy : 0≤A.y) (ht : t∈Icc 0 (7/10 : ℝ))
    (hcontact : 1+edgeWidth t≤H.y+A.a*Real.cos t-A.y*Real.sin t) :
    11/10<A.a ∧ A.y<133/200 ∧ 117/200<H.y := by
  have hHu := (H.coordinate_bounds hHs hHcore hHc hq).2.2
  have hAu := (A.coordinate_bounds hAs hAcore hAc hq).2.1
  rw [abs_of_nonneg hHy] at hHu
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig ht
  have hcos := mul_le_mul_of_nonneg_left hc1 hAs.1.le
  have hsin := mul_nonneg hAy hs0
  have hw := edgeWidth_ge_one t
  have ha : 11/10<A.a := by linarith
  have hb : A.y<133/200 := by
    have hh := hAc.trans hq
    rw [SignedPoint.circle,abs_of_nonneg hAy] at hh
    dsimp [qCap] at hh
    nlinarith
  exact ⟨ha,hb,by linarith⟩

/-- The AB inequality and the two middle circles give one strict primary-sum bound. -/
theorem middle_primary_sum {A B : SignedPoint}
    (_hAs : A.Sorted) (_hBs : B.Sorted) (hAy : 0≤A.y) (hBy : 0≤B.y)
    (hAc : A.circle≤qCap) (hBc : B.circle≤qCap) (hAB : 1≤A.y+B.y) :
    A.a+B.a<7547/3125 := by
  rw [SignedPoint.circle,abs_of_nonneg hAy] at hAc
  rw [SignedPoint.circle,abs_of_nonneg hBy] at hBc
  simp only [qCap] at hAc hBc
  have hpair : (A.a+B.a+1)^2+(A.y+B.y+1)^2≤4*(9789/2500) := by
    nlinarith [sq_nonneg (A.a-B.a),sq_nonneg (A.y-B.y)]
  have hminor := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2)
    (show 2≤A.y+B.y+1 by linarith) 2
  by_contra! hbad
  have hmajor := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤10672/3125)
    (show 10672/3125≤A.a+B.a+1 by linarith) 2
  nlinarith

/-- The rational reference vector lies strictly outside the circle `qCap`, so its support has
a strict reserve at every positive corner on or inside that circle. -/
theorem rational_tangent {P : SignedPoint} (hPa : 0<P.a) (hPy : 0≤P.y)
    (hPc : P.circle≤qCap) :
    X0*(P.a+1/2)+Y0*(P.y+1/2)<X0^2+Y0^2 := by
  rw [SignedPoint.circle,abs_of_nonneg hPy] at hPc
  have hnorm :
      (X0*(P.a+1/2)+Y0*(P.y+1/2))^2+
        (X0*(P.y+1/2)-Y0*(P.a+1/2))^2=
      (X0^2+Y0^2)*((P.a+1/2)^2+(P.y+1/2)^2) := by ring
  have hmul := mul_le_mul_of_nonneg_left hPc
    (show 0≤X0^2+Y0^2 by positivity)
  have hreserve : qCap<X0^2+Y0^2 := by norm_num [qCap,X0,Y0]
  have hN : 0<X0^2+Y0^2 := by norm_num [X0,Y0]
  have hstrict := mul_lt_mul_of_pos_left hreserve hN
  have hdot : 0≤X0*(P.a+1/2)+Y0*(P.y+1/2) := by
    dsimp [X0,Y0]
    positivity
  by_contra! hbad
  have hbadSq := pow_le_pow_left₀ hN.le hbad 2
  nlinarith [sq_nonneg (X0*(P.y+1/2)-Y0*(P.a+1/2))]

theorem sine_sum {t u : ℝ} (ht : t∈Icc 0 (7/10 : ℝ))
    (hu : u∈Icc 0 (7/10 : ℝ)) : Real.sin (t+u)≤Real.sin t+Real.sin u := by
  have hst := (transport_trig ht).2.2.1
  have hsu := (transport_trig hu).2.2.1
  have hfirst := mul_le_mul_of_nonneg_left (Real.cos_le_one u) hst
  have hsecond := mul_le_mul_of_nonneg_right (Real.cos_le_one t) hsu
  rw [Real.sin_add]
  nlinarith

theorem charged_outer_tangents {H A B D : SignedPoint} {t u : ℝ}
    (ht : t∈Icc 0 (7/10 : ℝ)) (hu : u∈Icc 0 (7/10 : ℝ))
    (hAa : 1/2≤A.a) (hBa : 1/2≤B.a)
    (hAy : 67/200≤A.y) (hBy : 67/200≤B.y)
    (hprim : A.a+B.a<7547/3125)
    (hHA : 1+edgeWidth t≤H.y+A.a*Real.cos t-A.y*Real.sin t)
    (hBD : 1+edgeWidth u≤D.y+B.a*Real.cos u-B.y*Real.sin u) :
    4953/3125+(167/200)*Real.sin (t+u)<H.y+D.y := by
  have hst := (transport_trig ht).2.2.1
  have hsu := (transport_trig hu).2.2.1
  have hAct := mul_nonneg (sub_nonneg.mpr hAa) (sub_nonneg.mpr (Real.cos_le_one t))
  have hBcu := mul_nonneg (sub_nonneg.mpr hBa) (sub_nonneg.mpr (Real.cos_le_one u))
  have hAst := mul_le_mul_of_nonneg_right
    (show 167/200≤A.y+1/2 by linarith) hst
  have hBsu := mul_le_mul_of_nonneg_right
    (show 167/200≤B.y+1/2 by linarith) hsu
  have hsum := sine_sum ht hu
  rw [edgeWidth_positive_formula ht] at hHA
  rw [edgeWidth_positive_formula hu] at hBD
  nlinarith

theorem outer_primary_sum {H D : SignedPoint} {α : ℝ}
    (hHa : 0<H.a) (hDa : 0<D.a) (hHy : 0≤H.y) (hDy : 0≤D.y)
    (hHc : H.circle≤qCap) (hDc : D.circle≤qCap) (hα : α∈Icc 0 (7/10 : ℝ))
    (hcharge : 4953/3125+(167/200)*Real.sin α<H.y+D.y) :
    H.a+D.a<1248/625-(359/500)*Real.sin α := by
  have hH := rational_tangent hHa hHy hHc
  have hD := rational_tangent hDa hDy hDc
  have hs := (transport_trig hα).2.2.1
  have hcoef : 0≤Y0*(167/200)-(359/500)*X0 := by norm_num [X0,Y0]
  have hgain := mul_nonneg hcoef hs
  have hcharged := mul_lt_mul_of_pos_left hcharge (by norm_num : 0<Y0)
  dsimp [X0,Y0] at hH hD hcharged hgain
  nlinarith

theorem coarse_cap_feasible : HardSplitCap.Feasible qCap (3/5) := by
  constructor <;> norm_num [qCap]

theorem coarse_cap_endpoint :
    cap qCap (3/5) 0+cap qCap (3/5) (11/50)<2 := by
  have hz : (0:ℝ)∈Icc 0 (7/10) := by norm_num
  have ht : (11/50 : ℝ)∈Icc 0 (7/10) := by norm_num
  have hzero := cap_upper coarse_cap_feasible hz
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤11/50 by norm_num)
  have hcl := cos_lower_six (show (0:ℝ)≤11/50 by norm_num)
  have hcu := cos_upper_four (show (0:ℝ)≤11/50 by norm_num)
  have hcos : 4879/5000<Real.cos (11/50 : ℝ) ∧ Real.cos (11/50 : ℝ)<122/125 := by
    constructor <;> norm_num at hcl hcu ⊢ <;> linarith
  have hsin : 109/500<Real.sin (11/50 : ℝ) := by norm_num at hs ⊢; linarith
  have hroot := root_sq coarse_cap_feasible ht
  have hr0 := root_pos coarse_cap_feasible ht
  have hcontact := contact_pos coarse_cap_feasible ht
  have hr : root qCap (3/5) (11/50)<1197/1000 := by
    dsimp [contact,qCap] at hroot
    nlinarith [hcos.1]
  have hp := mul_le_mul hcos.2.le hr.le hr0.le (by norm_num : (0:ℝ)≤122/125)
  have hn := mul_le_mul hsin.le
    (show 7879/5000≤contact (3/5) (11/50) by dsimp [contact]; linarith [hcos.1])
    (by norm_num : (0:ℝ)≤7879/5000)
    ((transport_trig ht).2.2.1)
  have hend : cap qCap (3/5) (11/50)≤2061869/2500000 := by
    unfold cap
    nlinarith
  linarith

/-- The scalar cap at the fixed ceiling `qCap` excludes a long span. -/
theorem short_span {H A B D : SignedPoint} {t u : ℝ}
    (hHy : H.y<9/10) (hDy : D.y<9/10)
    (hAy : 0≤A.y) (hBy : 0≤B.y)
    (hAc : A.circle≤qCap) (hBc : B.circle≤qCap)
    (ht : 0≤t) (hu : 0≤u) (hspan : t+u≤7/10) (hAB : 1≤A.y+B.y)
    (hHA : 1+edgeWidth t≤H.y+A.a*Real.cos t-A.y*Real.sin t)
    (hBD : 1+edgeWidth u≤D.y+B.a*Real.cos u-B.y*Real.sin u) : t+u<11/50 := by
  have htwide : t∈Icc 0 (7/10 : ℝ) := ⟨ht,by linarith⟩
  have huwide : u∈Icc 0 (7/10 : ℝ) := ⟨hu,by linarith⟩
  have hAcontact : (3/5 : ℝ)≤
      (A.a+1/2-1)*Real.cos t-(A.y+1/2)*Real.sin t := by
    rw [edgeWidth_positive_formula htwide] at hHA
    nlinarith
  have hBcontact : (3/5 : ℝ)≤
      (B.a+1/2-1)*Real.cos u-(B.y+1/2)*Real.sin u := by
    rw [edgeWidth_positive_formula huwide] at hBD
    nlinarith
  have hAc' : (A.a+1/2)^2+(A.y+1/2)^2≤qCap := by
    simpa [SignedPoint.circle,abs_of_nonneg hAy] using hAc
  have hBc' : (B.a+1/2)^2+(B.y+1/2)^2≤qCap := by
    simpa [SignedPoint.circle,abs_of_nonneg hBy] using hBc
  have hA := cap_majorizes_weak_contact coarse_cap_feasible htwide
    (show 0≤A.y+1/2 by linarith) hAcontact hAc'
  have hB := cap_majorizes_weak_contact coarse_cap_feasible huwide
    (show 0≤B.y+1/2 by linarith) hBcontact hBc'
  have hsplit := split_endpoint coarse_cap_feasible coarse_cap_feasible ht hu hspan
  have hsplit' : cap qCap (3/5) t+cap qCap (3/5) u≤
      cap qCap (3/5) 0+cap qCap (3/5) (t+u) := by
    simpa [add_comm] using hsplit
  by_contra! hlong
  have hmono := (cap_strictAnti coarse_cap_feasible).antitoneOn
    (show (11/50 : ℝ)∈Icc 0 (7/10) by norm_num)
    (show t+u∈Icc 0 (7/10 : ℝ) from ⟨by linarith,hspan⟩) hlong
  linarith [coarse_cap_endpoint]

end AlignedChainBounds
end SquaresInCircles.Eight
