module

public import SquaresInCircles.Eight.TableFree.CancelingSupport

/-!
# Negative GA1 with HG2: the canceling companion

Uncompiled draft. The input is the original same-radius signed triple.
An unavailable GA0 forces the flat-core and original-A cuts. Negative HG
error reselects HG0 on the same state; positive HG error is transported by
a derivative estimate proved only where the actual HG2 contact is feasible.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
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

theorem composite_actual_iff {P Θ x : ℝ} (H : SignedPoint)
    (hx : x-Θ∈Icc 0 (7/10 : ℝ)) :
    1≤composite P H.a H.y Θ x ↔
      zeroFeasible H (PrimaryCap.point P x) (x-Θ) 2 := by
  rw [zeroFeasible,edgeWidth_positive_formula hx]
  simp [zeroProjection,PrimaryCap.point,composite,S]
  constructor <;> intro h <;> linarith

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
    exact ⟨⟨hl0.trans hx.1,hx.2⟩,⟨by linarith,by linarith⟩⟩
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
    (hHs : H.Sorted) (hGs : G.Sorted)
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
    simpa [zeroFeasible,zeroProjection,abs_of_nonpos hGy] using hHG
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
      (z≠Θ → edgeWidth (x-Θ)<zeroProjection H G' (x-Θ) j) := by
  obtain ⟨hGa,hgsmall,hzsmall,hAb,hPupper⟩ := exceptional_negative_primary_cuts
    hGs hAs hGb hAc hq hGy hAy hz hGA hnotGA0
  rcases lt_trichotomy z Θ with hnegative | haligned | hpositive
  · have hstrict := canceling_negative_error_reselection hHs hGs hHy hGy
      hGa hgsmall ⟨(abs_le.mp hgap).1,sub_neg.mpr hnegative⟩ hHG
    obtain ⟨G',x,ha,hend,hframe,hs,hc,havoid,hcircle,hHG',hGA',hhard,hstrict'⟩ :=
      flat_core_negative_ga1_hg0_transport hq hHs hGs hAs hHc hGc hAc
        hHcore hGcore hAcore hGa hGy hz hΘ hgap hstrict.le hGA
    exact ⟨G',x,0,Or.inl rfl,ha,hend,hframe,hs,hc,havoid,hcircle,
      hHG',hGA',hhard,hstrict'⟩
  all_goals
    let P : ℝ := A.a-1/2
    have hzwide : z∈Icc 0 (7/10 : ℝ) := ⟨hz.1.le,hz.2⟩
    have hcz := transport_cos_pos (by rw [abs_of_pos hz.1]; exact hz.2)
    have hsz := Real.sin_pos_of_pos_of_lt_pi hz.1
      (by linarith [hz.2,Real.pi_gt_three])
    have hwidth := edgeWidth_ge_one (-z)
    have hproj : edgeWidth (-z)≤A.a-(7/12)*Real.sin z-|G.y|*Real.cos z := by
      simpa [quarterFeasible,quarterProjection,hGa,abs_of_nonpos hGy,
        Real.sin_neg,Real.cos_neg] using hGA
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
      simp [zeroFeasible,zeroProjection,G',PrimaryCap.point,
        abs_of_nonpos hGy] at hslack ⊢
      linarith
    refine ⟨G',z,2,Or.inr rfl,by simp [G',PrimaryCap.point,hGa],
      Or.inr haligned,?_,hs,hc,havoid,hinside,htransverse,hprimary.ge,?_,?_⟩
    · exact ⟨(min_le_left 0 Θ).trans hz.1.le,le_max_left _ _⟩
    · intro hz0
      exact False.elim (ne_of_gt hz.1 hz0)
    · intro hne
      exact False.elim (hne haligned)
  · have hstart : 1≤CancelingSupport.composite P H.a H.y Θ z := by
      have hh := hHG
      rw [zeroFeasible,edgeWidth_positive_formula
        ⟨sub_nonneg.mpr hpositive.le,(abs_le.mp hgap).2⟩] at hh
      simp [zeroProjection,abs_of_nonpos hGy] at hh
      unfold CancelingSupport.composite CancelingSupport.S
      linarith
    obtain ⟨x,hend,hframe,hxs,hs,hc,havoid,hinside,hstrict⟩ :=
      CancelingSupport.positive_endpoint hP ⟨hz.1,hzsmall⟩ hpositive
        (abs_le.mp hgap).2 hcap0 hcircle hq hqbig hstart
    let G' := PrimaryCap.point P x
    have hxwide : x∈Icc 0 (7/10 : ℝ) := ⟨hxs.1,by linarith [hxs.2]⟩
    have hprimary := PrimaryCap.actual_primary_contact (A := A)
      (P := P) (x := x) (by dsimp [P]; ring) hxwide
    refine ⟨G',x,2,Or.inr rfl,by simp [G',PrimaryCap.point,hGa],
      hend,hframe,hs,hc,havoid,hinside,hstrict.le,hprimary.ge,?_,fun _ => hstrict⟩
    intro hx0
    subst x
    exact (quarter_low_tie _ _).2 (by simpa using hprimary.ge)

end SquaresInCircles.Eight.TableFree