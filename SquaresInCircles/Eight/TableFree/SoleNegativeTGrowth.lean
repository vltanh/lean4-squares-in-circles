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
  change ratio f t i*large f atG t i≤ small f atG t i at hr
  have hlo := larger_lower (face f atG) ht (zero_mem ht) i
  change (largeFloor f:ℝ)≤large f atG t i at hlo
  have hsmall := smaller_lower (face f atG) ht (zero_mem ht) i
  change (smallFloor f:ℝ)≤ small f atG t i at hsmall
  have ht' := angle ht
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hlen : 0≤frameCap-t := by linarith [ht'.2]
  change _≤Vnu R (small f atG t i) (large f atG t i) (nu f atG t i) frameCap-
    Vnu R (small f atG t i) (large f atG t i) (nu f atG t i) t
  cases f
  · have hratio : (117/200)*large .ehLow atG t i≤ small .ehLow atG t i := by
      simp only [ratio] at hr
      nlinarith [mul_nonneg ht'.1 hq.le]
    have htg : t∈Icc 0 (1/5:ℝ) := by simpa [domain,left,right] using ht
    have hfloor : 431/500≤large .ehLow atG t i := by simpa [largeFloor] using hlo
    have hg := low_growth hR hQL hp hpq hratio hfloor hnu htg
    have hc : gamma .ehLow≤121/200 := by norm_num [gamma]
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (13/20)*large .ehMiddle atG t i≤ small .ehMiddle atG t i := by
      simpa [ratio] using hr
    have htg : t∈Icc 0 (7/20:ℝ) := by
      have hu := ht.2
      norm_num [domain,right] at hu
      exact ⟨ht'.1,hu⟩
    have hfloor : 923/1000≤large .ehMiddle atG t i := by simpa [largeFloor] using hlo
    have hg := middle_growth hR hQL hp hpq hratio hfloor hnu htg
    have hc : gamma .ehMiddle≤7/10 := by norm_num [gamma]
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (18/25)*large .ehHigh atG t i≤ small .ehHigh atG t i := by
      simpa [ratio] using hr
    have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
    have hc : gamma .ehHigh≤ small .ehHigh atG t i := by
      norm_num [smallFloor] at hsmall
      norm_num [gamma]
      linarith
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have htg : t∈Icc 0 (7/20:ℝ) := by simpa [domain,left,right] using ht
    by_cases hA : i=1
    · subst i
      obtain ⟨hs,hl,hn,hrA⟩ := SolePositiveTOrdinaryData.DE_A_data (face .deLow atG)
        (by simp [face]) ht (zero_mem ht)
      have hd := de_A (face .deLow atG) (by simp [face]) ht (zero_mem ht)
      change small .deLow atG t 1=ell .deLow t 0 at hs
      change large .deLow atG t 1=k .deLow t 0 at hl
      change (113/200:ℝ)≤ell .deLow t 0 ∧ ell .deLow t 0≤(81/100)*k .deLow t 0 at hd
      change ell .deLow t 0/k .deLow t 0∈Icc (533/1000:ℝ) (81/100) at hrA
      have hpq' : ell .deLow t 0≤k .deLow t 0 := by rw [← hs,← hl]; exact hpq
      have hg := DE_A_growth hR hQL hQU hd.1 hpq' hrA ht'
      have hnu1 : nu .deLow atG t 1=ell .deLow t 0 := rfl
      rw [hs,hl,hnu1]
      have hc : gamma .deLow≤18/25 := by norm_num [gamma]
      exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
    · by_cases hB : i=2
      · subst i
        have hratio : (5/8+27/100*t)*large .deLow atG t 2≤ small .deLow atG t 2 := by
          simpa [ratio] using hr
        have hfloor := SolePositiveTOrdinaryData.DE_B_large (face .deLow atG)
          (by simp [face]) ht (zero_mem ht)
        change 903/1000≤large .deLow atG t 2 at hfloor
        have hg := SolePositiveTDEChord.growth hR hQL hp hpq hratio hfloor hnu htg
        have hc : gamma .deLow≤7/10 := by norm_num [gamma]
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
      · have hi : i=0 ∨ i=3 := by fin_cases i <;> simp_all
        have hratio : (18/25)*large .deLow atG t i≤ small .deLow atG t i := by
          simpa [ratio,hA,hB] using hr
        have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
        have hsmall' := SolePositiveTOrdinaryData.DE_outer_small (face .deLow atG)
          (by simp [face]) ht (zero_mem ht) i hi
        change 18/25≤ small .deLow atG t i at hsmall'
        have hc : gamma .deLow≤ small .deLow atG t i := by norm_num [gamma]; linarith
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (18/25)*large .deHigh atG t i≤ small .deHigh atG t i := by
      simpa [ratio] using hr
    have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
    have hc : gamma .deHigh≤ small .deHigh atG t i := by
      norm_num [smallFloor] at hsmall
      norm_num [gamma]
      linarith
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg

/-- The equal-length secant is larger after shifting left. The proof
integrates the difference of the two actual derivatives. -/
theorem shifted_secant {R p q ν a b s : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hν : p≤ν) (hs : 0≤ s) (ha : a∈Icc s frameCap) (hb : b∈Icc s frameCap)
    (hab : a≤b) :
    Vnu R p q ν b-Vnu R p q ν a≤
      Vnu R p q ν (b-s)-Vnu R p q ν (a-s) := by
  have hx (x : ℝ) (hxx : x∈Icc s frameCap) :
      x∈Icc 0 frameCap ∧ x-s∈Icc 0 frameCap :=
    ⟨⟨hs.trans hxx.1,hxx.2⟩,⟨by linarith [hxx.1],by linarith [hxx.2]⟩⟩
  have hd (x : ℝ) (hxx : x∈Icc s frameCap) :
      HasDerivAt (fun x => Vnu R p q ν (x-s)-Vnu R p q ν x)
        (VnuDeriv R p q ν (x-s)-VnuDeriv R p q ν x) x := by
    have hfirst : HasDerivAt (fun x => Vnu R p q ν (x-s)) (VnuDeriv R p q ν (x-s)) x :=
      HasDerivAt.comp_sub_const x s
        (Vnu_hasDerivAt (R := R) (nu := ν) hp (hp.trans_le hpq) (hx x hxx).2)
    exact hfirst.fun_sub
      (Vnu_hasDerivAt (R := R) (nu := ν) hp (hp.trans_le hpq) (hx x hxx).1)
  have hm : MonotoneOn (fun x => Vnu R p q ν (x-s)-Vnu R p q ν x) (Icc s frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x hxx => (hd x hxx).continuousAt.continuousWithinAt
    · exact fun x hxx => hd x (Ioo_subset_Icc_self hxx)
    · intro x hxx
      have hxx' := hx x (Ioo_subset_Icc_self hxx)
      exact sub_nonneg.mpr
        ((VnuDeriv_antitone hR hQ hp hpq hqp hν) hxx'.2 hxx'.1 (by linarith))
  have hh := hm ha hb hab
  simp only at hh
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
  change ratio f t i*large f atG t i≤ small f atG t i at hr
  have hlo := larger_lower (face f atG) ht (zero_mem ht) i
  change (largeFloor f:ℝ)≤large f atG t i at hlo
  have hsmall := smaller_lower (face f atG) ht (zero_mem ht) i
  change (smallFloor f:ℝ)≤ small f atG t i at hsmall
  have hq := (positive atG ht i).2.2.trans_le (min_le_max : small f atG t i≤large f atG t i)
  have ht0 := (angle ht).1
  cases f
  · norm_num [ratio,largeFloor,gamma] at hr hlo ⊢
    nlinarith [mul_nonneg ht0 hq.le]
  · norm_num [ratio,largeFloor,gamma] at hr hlo ⊢
    linarith
  · norm_num [smallFloor,gamma] at hsmall ⊢
    linarith
  · by_cases hA : i=1
    · subst i
      have hd := de_A (face .deLow atG) (by simp [face]) ht (zero_mem ht)
      obtain ⟨hs,hl,hn,hra⟩ := SolePositiveTOrdinaryData.DE_A_data (face .deLow atG)
        (by simp [face]) ht (zero_mem ht)
      change small .deLow atG t 1=ell .deLow t 0 at hs
      change (113/200:ℝ)≤ell .deLow t 0 ∧ ell .deLow t 0≤(81/100)*k .deLow t 0 at hd
      rw [hs]
      norm_num [gamma]
      linarith [hd.1]
    · by_cases hB : i=2
      · subst i
        have hb := SolePositiveTOrdinaryData.DE_B_large (face .deLow atG)
          (by simp [face]) ht (zero_mem ht)
        change 903/1000≤large .deLow atG t 2 at hb
        norm_num [ratio,gamma] at hr ⊢
        nlinarith [mul_nonneg ht0 hq.le]
      · have hi : i=0 ∨ i=3 := by fin_cases i <;> simp_all
        have hh := SolePositiveTOrdinaryData.DE_outer_small (face .deLow atG)
          (by simp [face]) ht (zero_mem ht) i hi
        change 18/25≤ small .deLow atG t i at hh
        norm_num [gamma]
        linarith
  · norm_num [smallFloor,gamma] at hsmall ⊢
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
  have he : v/frameCap*frameCap=v := div_mul_cancel₀ v hh.ne'
  simp only [smul_eq_mul,Vnu_zero,mul_zero,zero_add,he] at hch
  have hend := (V_endpoint_lower (SoleAngleGrowth.radius_lower hR hQL) hp hpq hqp).le.trans
    (Vnu_ge_V hνq)
  have hm := mul_le_mul_of_nonneg_left hend hα.1
  have hid : (v/frameCap)*((87/100)*p)=(87/70)*p*v := by simp only [frameCap]; ring
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
