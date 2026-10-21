module

public import SquaresInCircles.Eight.TableFree.ShortMixedZeroPositive

/-!
# Original outer-source opposite-sign zero edges

All six nonnegative-angle families are treated on their complete half.
Four negative-angle families share an increasing secant/tangent support;
its derivative proof holds on the whole frame range and does not require
a numerical cutoff of the feasible contact.

The source outer coefficient is `-p r`, precisely the coefficient change
under reflection/reversal of the core-source families.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero

open CommonQuarter CorePairGeometry WrongWordCircleSupport

lemma core_primary_lower {a b : ℝ} (hc : CoreState a b) :
    CoreAngleEndpoint.diagonal≤a := by
  rcases hc with ⟨rfl,_,_⟩ | ⟨hb,hab,he⟩
  · linarith [CoreAngleEndpoint.diagonal_bounds.2]
  · exact (CoreAngleEndpoint.corner_diagonal hb hab he).2

/-- The four smooth-multiplier families have their actual outer support
at the diagonal for every multiplier at least the original core slope. -/
lemma outer_diagonal_support (r : Row) (h0 : r≠0) (h3 : r≠3)
    {a b l : ℝ} (hc : OuterState a b) (hl : g r≤l) :
    (-p r+q r-l)*outerDiagonal≤-p r*a+(q r-l)*b := by
  have hd := outer_bounds hc
  have hd0 : 0≤outerDiagonal := by linarith [outer_endpoint_bounds.2.2.1]
  have hcompare : (-p r+q r-g r)*outerDiagonal≤-p r*outerAxial := by
    have ha := outer_endpoint_bounds
    have hf := fine_diagonal_bounds
    fin_cases r <;> norm_num [p,q,g] at h0 h3 ⊢ <;>
      nlinarith [ha.1,ha.2.1,hf.1,hf.2]
  have hcompare' : (-p r+q r-l)*outerDiagonal≤-p r*outerAxial := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) hd0]
  by_cases hY : 0≤q r-l
  · exact outer_endpoints_lower hc hY hcompare' le_rfl
  · by_cases hP : 0≤-p r
    · have hp := mul_le_mul_of_nonneg_left hd.1 hP
      have hq := mul_le_mul_of_nonpos_left hd.2.2.2.1 (le_of_not_ge hY)
      nlinarith
    · have hs : q r-g r+p r≤0 := by
        fin_cases r <;> norm_num [p,q,g] at h0 h3 hP ⊢
      exact outer_diagonal_lower hc (le_of_not_ge hP) (by linarith)

def positiveSecant (r : Row) (x : ℝ) : ℝ :=
  x+c r+(-p r+q r)*outerDiagonal+g r/2+
    g r*(1/2-outerDiagonal)/Real.cos x-(g r/12)*Real.sin x/Real.cos x
def negativeSecant (r : Row) (x : ℝ) : ℝ :=
  -x+c r+(-p r+q r)*outerDiagonal+g r/2+
    g r*(1/2-outerDiagonal)/Real.cos x+
      g r*(1/2+CoreAngleEndpoint.diagonal)*Real.sin x/Real.cos x
def positiveSecantD (r : Row) (x : ℝ) : ℝ :=
  1-g r*((outerDiagonal-1/2)*Real.sin x+1/12)/(Real.cos x)^2
def negativeSecantD (r : Row) (x : ℝ) : ℝ :=
  -1+g r*((1/2+CoreAngleEndpoint.diagonal)-
    (outerDiagonal-1/2)*Real.sin x)/(Real.cos x)^2

lemma positiveSecant_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (positiveSecant r) (positiveSecantD r x) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  have hd := (((((hasDerivAt_id x).add_const (c r)).add_const
    ((-p r+q r)*outerDiagonal)).add_const (g r/2)).add
      ((hasDerivAt_const x (g r*(1/2-outerDiagonal))).div (Real.hasDerivAt_cos x) hc)).sub
        (((Real.hasDerivAt_sin x).const_mul (g r/12)).div (Real.hasDerivAt_cos x) hc)
  convert hd using 1
  · rfl
  · dsimp [positiveSecantD]
    field_simp [hc]
    have ht : g r*((Real.sin x)^2+(Real.cos x)^2)=g r := by
      rw [Real.sin_sq_add_cos_sq,mul_one]
    nlinarith only [ht]

lemma negativeSecant_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (negativeSecant r) (negativeSecantD r x) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  have hd := ((((((hasDerivAt_id x).neg).add_const (c r)).add_const
    ((-p r+q r)*outerDiagonal)).add_const (g r/2)).add
      ((hasDerivAt_const x (g r*(1/2-outerDiagonal))).div (Real.hasDerivAt_cos x) hc)).add
        (((Real.hasDerivAt_sin x).const_mul (g r*(1/2+CoreAngleEndpoint.diagonal))).div
          (Real.hasDerivAt_cos x) hc)
  convert hd using 1
  · rfl
  · dsimp [negativeSecantD]
    field_simp [hc]
    have ht : g r*(1/2+CoreAngleEndpoint.diagonal)*
        ((Real.sin x)^2+(Real.cos x)^2)=g r*(1/2+CoreAngleEndpoint.diagonal) := by
      rw [Real.sin_sq_add_cos_sq,mul_one]
    nlinarith only [ht]

lemma positiveSecantD_pos (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<positiveSecantD r x := by
  have ht := positive_trig hx
  have hg := (coefficient_bounds r).1
  have hgU : g r≤1139/1000 :=
    (coefficient_bounds r).2.2.1.trans (coefficient_bounds r).2.2.2.1
  have hd := outer_endpoint_bounds
  have hcos : (29/50:ℝ)<(Real.cos x)^2 := by nlinarith [ht.1]
  have hnum : 0≤(outerDiagonal-1/2)*Real.sin x+1/12 := by
    have hm := mul_nonneg (show 0≤outerDiagonal-1/2 by linarith [hd.2.2.1]) ht.2.2.1
    linarith
  have hprod : (outerDiagonal-1/2)*Real.sin x<(2/5)*(129/200:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left ht.2.2.2.1.le
      (show 0≤outerDiagonal-1/2 by linarith [hd.2.2.1])
    have h2 := mul_lt_mul_of_pos_right
      (show outerDiagonal-1/2<(2/5:ℝ) by linarith [hd.2.2.2]) (by norm_num : (0:ℝ)<16106/25000)
    nlinarith
  have hscale := mul_le_mul_of_nonneg_right hgU hnum
  have hupper := mul_lt_mul_of_pos_left (show
    (outerDiagonal-1/2)*Real.sin x+1/12<(2/5)*(129/200:ℝ)+1/12 by linarith)
    (by norm_num : (0:ℝ)<1139/1000)
  have hratio : g r*((outerDiagonal-1/2)*Real.sin x+1/12)/(Real.cos x)^2<1 :=
    (div_lt_one (by linarith : 0<(Real.cos x)^2)).2 (by nlinarith)
  dsimp [positiveSecantD]
  linarith

lemma negativeSecantD_pos (r : Row) (h0 : r≠0) (h3 : r≠3)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<negativeSecantD r x := by
  have hg : 1<g r := by fin_cases r <;> norm_num [g] at h0 h3 ⊢
  have hd := outer_endpoint_bounds
  have hc := CoreAngleEndpoint.diagonal_bounds
  have ht := positive_trig hx
  have hden : 0<(Real.cos x)^2 := sq_pos_of_pos (by linarith [ht.1])
  have hdisc : (outerDiagonal-1/2)^2<4*(CoreAngleEndpoint.diagonal-1/2) := by
    nlinarith [hd.2.2.1,hd.2.2.2,hc.1]
  have hquadratic : 0<(Real.sin x)^2-(outerDiagonal-1/2)*Real.sin x+
      CoreAngleEndpoint.diagonal-1/2 := by
    nlinarith [sq_nonneg (2*Real.sin x-(outerDiagonal-1/2))]
  have hbracket : (Real.cos x)^2<(1/2+CoreAngleEndpoint.diagonal)-
      (outerDiagonal-1/2)*Real.sin x := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hpositive : 0<(1/2+CoreAngleEndpoint.diagonal)-
      (outerDiagonal-1/2)*Real.sin x := hden.trans hbracket
  have hm := mul_lt_mul_of_pos_right hg hpositive
  have hratio : 1<g r*((1/2+CoreAngleEndpoint.diagonal)-
      (outerDiagonal-1/2)*Real.sin x)/(Real.cos x)^2 :=
    (one_lt_div hden).2 (by nlinarith)
  dsimp [negativeSecantD]
  linarith

lemma secant_initial (r : Row) (h0 : r≠0) (h3 : r≠3) :
    (449/500:ℝ)<positiveSecant r 0 ∧ (449/500:ℝ)<negativeSecant r 0 := by
  have hl : multiplier r=g r := by simp [multiplier,h0,h3]
  have hh := diagonal_initial r
  rw [hl] at hh
  simp [diagonal,base,X,Y,intercept,hl,positiveSecant,negativeSecant] at hh ⊢
  constructor <;> nlinarith

lemma positiveSecant_lower (r : Row) (h0 : r≠0) (h3 : r≠3)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<positiveSecant r x := by
  have hm : MonotoneOn (positiveSecant r) (Icc 0 (7/10)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z hz => (positiveSecant_hasDerivAt r hz).continuousAt.continuousWithinAt
    · exact fun z hz => positiveSecant_hasDerivAt r (Ioo_subset_Icc_self hz)
    · exact fun z hz => (positiveSecantD_pos r (Ioo_subset_Icc_self hz)).le
  exact (secant_initial r h0 h3).1.trans_le (hm (by norm_num) hx hx.1)

lemma negativeSecant_lower (r : Row) (h0 : r≠0) (h3 : r≠3)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<negativeSecant r x := by
  have hm : MonotoneOn (negativeSecant r) (Icc 0 (7/10)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z hz => (negativeSecant_hasDerivAt r hz).continuousAt.continuousWithinAt
    · exact fun z hz => negativeSecant_hasDerivAt r (Ioo_subset_Icc_self hz)
    · exact fun z hz => (negativeSecantD_pos r h0 h3 (Ioo_subset_Icc_self hz)).le
  exact (secant_initial r h0 h3).2.trans_le (hm (by norm_num) hx hx.1)

lemma secant_multiplier (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<g r/Real.cos x ∧ g r≤g r/Real.cos x ∧
      (g r/Real.cos x)*Real.cos x=g r := by
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hg := (coefficient_bounds r).1
  exact ⟨div_pos hg hc,(le_div_iff₀ hc).2 (by nlinarith [Real.cos_le_one x]),
    div_mul_cancel₀ _ hc.ne'⟩

theorem opposite_outer_positive_secant (r : Row) (h0 : r≠0) (h3 : r≠3)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b+A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)<x+c r-p r*a+q r*b+g r*B := by
  let l := g r/Real.cos x
  have hl := secant_multiplier r hx
  have hsource := outer_diagonal_support r h0 h3 hs hl.2.1
  have hA := (CoreAngleEndpoint.state_bounds ht).2.1
  have hcore := mul_nonneg (mul_nonneg hl.1.le (positive_trig hx).2.2.1)
    (sub_nonneg.mpr hA)
  have hsep := mul_nonneg hl.1.le (sub_nonneg.mpr hm)
  have hh := positiveSecant_lower r h0 h3 hx
  have hid : positiveSecant r x=x+c r+(-p r+q r-l)*outerDiagonal+
      l*(1+Real.sin x+Real.cos x)/2-l*(7/12)*Real.sin x := by
    dsimp [positiveSecant,l]
    field_simp [(ne_of_gt (show 0<Real.cos x by linarith [(positive_trig hx).1]))]
    ring
  rw [hid] at hh
  change 0≤(l*Real.sin x)*(7/12-A) at hcore
  change 0≤l*(b+A*Real.sin x+B*Real.cos x-(1+Real.sin x+Real.cos x)/2) at hsep
  change (-p r+q r-l)*outerDiagonal≤-p r*a+(q r-l)*b at hsource
  have hlc : l*Real.cos x=g r := hl.2.2
  nlinarith

/-- The four large-slope negative-angle families are controlled on the
whole frame interval, directly from their original weak separator. -/
theorem opposite_outer_negative_secant (r : Row) (h0 : r≠0) (h3 : r≠3)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)<-x+c r-p r*a+q r*b+g r*B := by
  let l := g r/Real.cos x
  have hl := secant_multiplier r hx
  have hsource := outer_diagonal_support r h0 h3 hs hl.2.1
  have hA := core_primary_lower ht
  have hcore := mul_nonneg (mul_nonneg hl.1.le (positive_trig hx).2.2.1)
    (sub_nonneg.mpr hA)
  have hsep := mul_nonneg hl.1.le (sub_nonneg.mpr hm)
  have hh := negativeSecant_lower r h0 h3 hx
  have hid : negativeSecant r x=-x+c r+(-p r+q r-l)*outerDiagonal+
      l*(1+Real.sin x+Real.cos x)/2+l*CoreAngleEndpoint.diagonal*Real.sin x := by
    dsimp [negativeSecant,l]
    field_simp [(ne_of_gt (show 0<Real.cos x by linarith [(positive_trig hx).1]))]
    ring
  rw [hid] at hh
  change 0≤(l*Real.sin x)*(A-CoreAngleEndpoint.diagonal) at hcore
  change 0≤l*(b-A*Real.sin x+B*Real.cos x-(1+Real.sin x+Real.cos x)/2) at hsep
  change (-p r+q r-l)*outerDiagonal≤-p r*a+(q r-l)*b at hsource
  have hlc : l*Real.cos x=g r := hl.2.2
  nlinarith

def constantOuter (r : Row) (x : ℝ) : ℝ :=
  x+c r+(p r-q r+multiplier r)/2-radius*N (p r) (q r) (multiplier r) 0+
    multiplier r/2+g r*CoreAngleEndpoint.diagonal-(multiplier r/12)*Real.sin x+
      multiplier r*(1/2-CoreAngleEndpoint.diagonal)*Real.cos x
def constantOuterD (r : Row) (x : ℝ) : ℝ :=
  1-(multiplier r/12)*Real.cos x+
    multiplier r*(CoreAngleEndpoint.diagonal-1/2)*Real.sin x

lemma constantOuter_hasDerivAt (r : Row) (x : ℝ) :
    HasDerivAt (constantOuter r) (constantOuterD r x) x := by
  convert (((((((hasDerivAt_id x).add_const (c r)).add_const
    ((p r-q r+multiplier r)/2)).sub_const
      (radius*N (p r) (q r) (multiplier r) 0)).add_const (multiplier r/2)).add_const
        (g r*CoreAngleEndpoint.diagonal)).sub
          ((Real.hasDerivAt_sin x).const_mul (multiplier r/12))).add
            ((Real.hasDerivAt_cos x).const_mul (multiplier r*(1/2-CoreAngleEndpoint.diagonal)))
    using 1 <;> dsimp [constantOuter,constantOuterD] <;> ring

lemma constantOuter_lower (r : Row) (he : r=0 ∨ r=3)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<constantOuter r x := by
  have hzero : constantOuter r 0=full (intercept r) (p r) (q r) (multiplier r) 0 := by
    rw [full_expression]
    simp only [constantOuter,intercept,Real.sin_zero,Real.cos_zero]
    ring
  have hinit : (449/500:ℝ)<constantOuter r 0 := by
    rw [hzero]
    rcases he with rfl | rfl
    · have hd := CoreAngleEndpoint.diagonal_bounds
      norm_num [full,base,X,Y,N,CircularNorm.norm,CircularNorm.energy,mass,
        intercept,c,p,q,g,multiplier]
      nlinarith [hd.1,hd.2]
    · exact third_full_initial
  have hm : MonotoneOn (constantOuter r) (Icc 0 (7/10)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z _ => (constantOuter_hasDerivAt r z).continuousAt.continuousWithinAt
    · exact fun z _ => constantOuter_hasDerivAt r z
    · intro z hz
      have ht := positive_trig (Ioo_subset_Icc_self hz)
      have hc := coefficient_bounds r
      have h₁ := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤multiplier r/12 by linarith [hc.2.1])
      have h₂ := mul_nonneg (mul_nonneg hc.2.1.le
        (show 0≤CoreAngleEndpoint.diagonal-1/2 by linarith [CoreAngleEndpoint.diagonal_bounds.1])) ht.2.2.1
      dsimp [constantOuterD]
      linarith [hc.2.2.2.1]
  exact hinit.trans_le (hm (by norm_num) hx hx.1)

theorem opposite_outer_positive_constant (r : Row) (he : r=0 ∨ r=3)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b+A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)<x+c r-p r*a+q r*b+g r*B := by
  have hc := coefficient_bounds r
  have htr := positive_trig hx
  have hcoef : g r-multiplier r*Real.cos x≤0 := by
    have hp := mul_lt_mul_of_pos_left htr.1 hc.2.1
    rcases he with rfl | rfl <;> norm_num [g,multiplier,q] at hp ⊢ <;> linarith
  have hA := (CoreAngleEndpoint.state_bounds ht).2.1
  have hB := (CoreAngleEndpoint.state_bounds ht).2.2.2.2
  have hprimary := mul_nonneg (mul_nonneg hc.2.1.le htr.2.2.1) (sub_nonneg.mpr hA)
  have hsecondary := mul_nonneg_of_nonpos_of_nonpos hcoef (sub_nonpos.mpr hB)
  have hsource := outer_circle_lower (X := -p r) (Y := q r-multiplier r) hs
  have hN : N (p r) (q r) (multiplier r) 0=
      Real.sqrt ((-p r)^2+(q r-multiplier r)^2) := by
    rw [N,CircularNorm.norm,energy_eq]
    simp [X,Y]
  rw [← hN] at hsource
  have hsep := mul_nonneg hc.2.1.le (sub_nonneg.mpr hm)
  have hh := constantOuter_lower r he hx
  dsimp [constantOuter] at hh
  nlinarith

/-- All six original outer-source opposite-sign secondary families on
the nonnegative angle half. -/
theorem opposite_outer_positive (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b+A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)<x+c r-p r*a+q r*b+g r*B := by
  by_cases he : r=0 ∨ r=3
  · exact opposite_outer_positive_constant r he hs ht hx hm
  · exact opposite_outer_positive_secant r (fun h => he (Or.inl h))
      (fun h => he (Or.inr h)) hs ht hx hm

end SquaresInCircles.Eight.TableFree.ShortMixedZero
