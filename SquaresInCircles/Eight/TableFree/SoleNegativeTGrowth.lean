module

public import SquaresInCircles.Eight.TableFree.SoleNegativeTCoefficients

/-!
# Every negative sole-E charge pays its own separated positive budget

Uncompiled source. The full-domain chords already proved for positive
T are stronger than the negative-primary positive budgets. Concavity
allows both endpoints of each chord to be shifted left by the actual
negative primary. Thus no far-angle comparison between different
negative indices, and no additional low-family subdivision, is needed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SoleNegativeTGrowth
open SoleTScalarModel SoleNegativeTCoefficients SolePositiveTCoefficients
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeEnvelope
open SingleAngleConcavity SolePositiveTGrowth

theorem old_concave {f : Family} (atG : Bool) {R t : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (i : Fin 4) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun v => oldV f atG R t v i) := by
  exact Vnu_concave hR hQ (positive atG ht i).2.2 min_le_max
    (SoleNegativeTCoefficients.half_ratio atG ht i)
    (SoleNegativeTCoefficients.nu_between f atG t i).1

theorem zero (f : Family) (atG : Bool) (R t : ℝ) (i : Fin 4) :
    oldV f atG R t 0 i=0 := by simp [oldV]

theorem chord {f : Family} (atG : Bool) {R t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain f) (i : Fin 4) :
    gamma f*(frameCap-t)≤oldV f atG R t frameCap i-oldV f atG R t t i := by
  have hp := (positive atG ht i).2.2
  have hpq : small f atG t i≤large f atG t i := min_le_max
  have hq := hp.trans_le hpq
  have hnu := (SoleNegativeTCoefficients.nu_between f atG t i).2
  have hr := ratio_lower (face f atG) ht (zero_mem ht) i
  change ratio f t i*large f atG t i≤small f atG t i at hr
  have hlo := larger_lower (face f atG) ht (zero_mem ht) i
  change (largeFloor f:ℝ)≤large f atG t i at hlo
  have hsmall := smaller_lower (face f atG) ht (zero_mem ht) i
  change (smallFloor f:ℝ)≤small f atG t i at hsmall
  have ht' := angle ht
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hlen : 0≤frameCap-t := by linarith [ht'.2]
  change _≤Vnu R (small f atG t i) (large f atG t i) (nu f atG t i) frameCap-
    Vnu R (small f atG t i) (large f atG t i) (nu f atG t i) t
  cases hf : f
  · have hratio : (117/200)*large f atG t i≤small f atG t i := by
      simp [ratio,hf] at hr
      nlinarith [mul_nonneg ht'.1 hq.le]
    have htg : t∈Icc 0 (1/5:ℝ) := by simpa [domain,hf,left,right] using ht
    have hfloor : 431/500≤large f atG t i := by simpa [largeFloor,hf] using hlo
    have hg := low_growth hR hQL hp hpq hratio hfloor hnu htg
    have hc : gamma f≤121/200 := by norm_num [gamma,hf]
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (13/20)*large f atG t i≤small f atG t i := by simpa [ratio,hf] using hr
    have htg : t∈Icc 0 (7/20:ℝ) := by
      have hu := ht.2
      norm_num [domain,hf,right] at hu
      exact ⟨ht'.1,hu⟩
    have hfloor : 923/1000≤large f atG t i := by simpa [largeFloor,hf] using hlo
    have hg := middle_growth hR hQL hp hpq hratio hfloor hnu htg
    have hc : gamma f≤7/10 := by norm_num [gamma,hf]
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (18/25)*large f atG t i≤small f atG t i := by simpa [ratio,hf] using hr
    have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
    have hc : gamma f≤small f atG t i := by
      norm_num [smallFloor,hf] at hsmall
      norm_num [gamma,hf]
      linarith
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have htg : t∈Icc 0 (7/20:ℝ) := by simpa [domain,hf,left,right] using ht
    by_cases hA : i=1
    · subst i
      obtain ⟨hs,hl,hn,hrA⟩ := SolePositiveTOrdinaryData.DE_A_data (face f atG)
        (by simpa [face] using hf) ht (zero_mem ht)
      have hd := de_A (face f atG) (by simpa [face] using hf) ht (zero_mem ht)
      have hg := DE_A_growth hR hQL hQU hd.1
        (by rw [← hs,← hl]; exact hpq) hrA ht'
      change small f atG t 1=ell f t 0 at hs
      change large f atG t 1=k f t 0 at hl
      rw [hs,hl]
      change _≤Vnu R (ell f t 0) (k f t 0) (ell f t 0) frameCap-
        Vnu R (ell f t 0) (k f t 0) (ell f t 0) t
      have hc : gamma f≤18/25 := by norm_num [gamma,hf]
      exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
    · by_cases hB : i=2
      · subst i
        have hratio : (5/8+27/100*t)*large f atG t 2≤small f atG t 2 := by
          simpa [ratio,hf] using hr
        have hfloor := SolePositiveTOrdinaryData.DE_B_large (face f atG)
          (by simpa [face] using hf) ht (zero_mem ht)
        have hg := SolePositiveTDEChord.growth hR hQL hp hpq hratio hfloor hnu htg
        have hc : gamma f≤7/10 := by norm_num [gamma,hf]
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
      · have hi : i=0 ∨ i=3 := by fin_cases i <;> simp_all
        have hratio : (18/25)*large f atG t i≤small f atG t i := by
          simpa [ratio,hf,hA,hB] using hr
        have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
        have hsmall := SolePositiveTOrdinaryData.DE_outer_small (face f atG)
          (by simpa [face] using hf) ht (zero_mem ht) i hi
        change 18/25≤small f atG t i at hsmall
        have hc : gamma f≤small f atG t i := by norm_num [gamma,hf]; linarith
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (18/25)*large f atG t i≤small f atG t i := by simpa [ratio,hf] using hr
    have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
    have hc : gamma f≤small f atG t i := by
      norm_num [smallFloor,hf] at hsmall
      norm_num [gamma,hf]
      linarith
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg

/-- The equal-length secant is larger after shifting left. The proof
integrates the difference of the two actual derivatives. -/
theorem shifted_secant {R p q ν a b s : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hν : p≤ν) (hs : 0≤s) (ha : a∈Icc s frameCap) (hb : b∈Icc s frameCap)
    (hab : a≤b) :
    Vnu R p q ν b-Vnu R p q ν a≤
      Vnu R p q ν (b-s)-Vnu R p q ν (a-s) := by
  let F : ℝ → ℝ := fun x => Vnu R p q ν (x-s)-Vnu R p q ν x
  have hx (x : ℝ) (hxx : x∈Icc s frameCap) :
      x∈Icc 0 frameCap ∧ x-s∈Icc 0 frameCap :=
    ⟨⟨hs.trans hxx.1,hxx.2⟩,⟨by linarith [hxx.1],by linarith [hxx.2]⟩⟩
  have hd (x : ℝ) (hxx : x∈Icc s frameCap) :
      HasDerivAt F (VnuDeriv R p q ν (x-s)-VnuDeriv R p q ν x) x := by
    have hfirst := (Vnu_hasDerivAt hp (hp.trans_le hpq) (hx x hxx).2).comp x
      ((hasDerivAt_id x).sub_const s)
    simpa only [mul_one] using hfirst.sub (Vnu_hasDerivAt hp (hp.trans_le hpq) (hx x hxx).1)
  have hm : MonotoneOn F (Icc s frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x hxx => (hd x hxx).continuousAt.continuousWithinAt
    · exact fun x hxx => hd x (Ioo_subset_Icc_self hxx)
    · intro x hxx
      have hxx' := hx x (Ioo_subset_Icc_self hxx)
      exact sub_nonneg.mpr
        ((VnuDeriv_antitone hR hQ hp hpq hqp hν) hxx'.2 hxx'.1 (by linarith))
  have hh := hm ha hb hab
  dsimp [F] at hh
  linarith

theorem shifted_chord {f : Family} (atG : Bool) {R t s : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain f) (hs : s∈Icc 0 t) (i : Fin 4) :
    gamma f*(frameCap-t)≤oldV f atG R t (frameCap-s) i-oldV f atG R t (t-s) i := by
  have hshift := shifted_secant hR hQU (positive atG ht i).2.2 min_le_max
    (SoleNegativeTCoefficients.half_ratio atG ht i)
    (SoleNegativeTCoefficients.nu_between f atG t i).1 hs.1
    ⟨hs.2,(angle ht).2⟩ ⟨hs.2.trans (angle ht).2,le_rfl⟩ (angle ht).2
  exact (chord atG hR hQL hQU ht i).trans hshift

theorem linear_coefficient {f : Family} (atG : Bool) {t : ℝ}
    (ht : t∈domain f) (i : Fin 4) : gamma f≤(87/70)*small f atG t i := by
  have hr := ratio_lower (face f atG) ht (zero_mem ht) i
  change ratio f t i*large f atG t i≤small f atG t i at hr
  have hlo := larger_lower (face f atG) ht (zero_mem ht) i
  change (largeFloor f:ℝ)≤large f atG t i at hlo
  have hsmall := smaller_lower (face f atG) ht (zero_mem ht) i
  change (smallFloor f:ℝ)≤small f atG t i at hsmall
  have hq := (positive atG ht i).2.2.trans_le (min_le_max : small f atG t i≤large f atG t i)
  have ht0 := (angle ht).1
  cases hf : f
  · norm_num [ratio,largeFloor,gamma,hf] at hr hlo ⊢
    nlinarith [mul_nonneg ht0 hq.le]
  · norm_num [ratio,largeFloor,gamma,hf] at hr hlo ⊢
    linarith
  · norm_num [smallFloor,gamma,hf] at hsmall ⊢
    linarith
  · by_cases hA : i=1
    · subst i
      have hd := de_A (face f atG) (by simpa [face] using hf) ht (zero_mem ht)
      obtain ⟨hs,hl,hn,hra⟩ := SolePositiveTOrdinaryData.DE_A_data (face f atG)
        (by simpa [face] using hf) ht (zero_mem ht)
      change small f atG t 1=ell f t 0 at hs
      rw [hs]
      norm_num [gamma,hf]
      linarith [hd.1]
    · by_cases hB : i=2
      · subst i
        have hb := SolePositiveTOrdinaryData.DE_B_large (face f atG)
          (by simpa [face] using hf) ht (zero_mem ht)
        change 903/1000≤large f atG t 2 at hb
        norm_num [ratio,gamma,hf] at hr ⊢
        nlinarith [mul_nonneg ht0 hq.le]
      · have hi : i=0 ∨ i=3 := by fin_cases i <;> simp_all
        have hh := SolePositiveTOrdinaryData.DE_outer_small (face f atG)
          (by simpa [face] using hf) ht (zero_mem ht) i hi
        change 18/25≤small f atG t i at hh
        norm_num [gamma,hf]
        linarith
  · norm_num [smallFloor,gamma,hf] at hsmall ⊢
    linarith

theorem radius_chord {R p q ν v : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hν : p≤ν) (hνq : ν≤q)
    (hv : v∈Icc 0 frameCap) : (87/70)*p*v≤Vnu R p q ν v := by
  have hh : 0<frameCap := by norm_num [frameCap]
  have hα : 0≤v/frameCap ∧ v/frameCap≤1 :=
    ⟨div_nonneg hv.1 hh.le,(div_le_one hh).2 hv.2⟩
  have hc := Vnu_concave hR hQU hp hpq hqp hν
  have hch := hc.2 ⟨le_rfl,hh.le⟩ ⟨hh.le,le_rfl⟩
    (sub_nonneg.mpr hα.2) hα.1 (by ring)
  have he : (1-v/frameCap)*0+(v/frameCap)*frameCap=v := by field_simp [hh.ne']; ring
  simp only [smul_eq_mul,he,Vnu_zero,mul_zero,zero_add] at hch
  have hend := (V_endpoint_lower (SoleAngleGrowth.radius_lower hR hQL) hp hpq hqp).le.trans
    (Vnu_ge_V hνq)
  have hm := mul_le_mul_of_nonneg_left hend hα.1
  have hid : (v/frameCap)*((87/100)*p)=(87/70)*p*v := by dsimp [frameCap]; ring
  rw [hid] at hm
  exact hm.trans hch

theorem linear_lower {f : Family} (atG : Bool) {R t v : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain f) (hv : v∈Icc 0 frameCap) (i : Fin 4) :
    gamma f*v≤oldV f atG R t v i := by
  have hbound := radius_chord hR hQL hQU (positive atG ht i).2.2 min_le_max
    (SoleNegativeTCoefficients.half_ratio atG ht i)
    (SoleNegativeTCoefficients.nu_between f atG t i).1
    (SoleNegativeTCoefficients.nu_between f atG t i).2 hv
  exact (mul_le_mul_of_nonneg_right (linear_coefficient atG ht i) hv.1).trans hbound

end SquaresInCircles.Eight.TableFree.SoleNegativeTGrowth
