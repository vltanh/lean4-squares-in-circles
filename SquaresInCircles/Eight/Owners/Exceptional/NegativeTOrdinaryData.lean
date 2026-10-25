module

public import SquaresInCircles.Eight.Owners.Critical.NegativeTOrdinaryData

/-!
# Eight squares: actual and canonical ordinary coefficients outside the critical strip

The canonical B pair is `(l, c)`; the actual BT3 pair has `c sec s` and the one-angle negative
coefficient `l`. H is a two-angle block whose negative coefficient is its larger force
coefficient. A positive ordinary angle costs `0.573` on the low band and `0.619` on the others
(`positiveCost`, `positive_lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ExceptionalNegativeTOrdinaryData
open Candidate ExceptionalECoefficients ExceptionalContactStress
open ExceptionalEBalanced (endpointX endpointE endpoints_mem)
open CriticalNegativeTOrdinaryData (shortDomain short_small bWeight single)
open PositiveAngularEnvelope OrdinaryAngleConcavity SingleAngleConcavity

def positiveCost (b : Band) : ℝ := if b=.low then 573/1000 else 619/1000
def coefficientCap (b : Band) : ℝ := if b=.low then 21/20 else 227/200
def p (b : Band) (t : ℝ) (face td : Bool) (s : ℝ) : Fin 3 → ℝ :=
  CriticalNegativeTOrdinaryData.small (k b t) (ell b t) (c b t) (eta b t)
    (endpointX face t) (endpointE face t) s td
def q (b : Band) (t : ℝ) (face td : Bool) (s : ℝ) : Fin 3 → ℝ :=
  CriticalNegativeTOrdinaryData.large (k b t) (ell b t) (c b t) (eta b t)
    (endpointX face t) (endpointE face t) s td
def nu (b : Band) (t : ℝ) (face td : Bool) (s : ℝ) : Fin 3 → ℝ :=
  CriticalNegativeTOrdinaryData.nu (k b t) (ell b t) (c b t) (eta b t)
    (endpointX face t) (endpointE face t) s td
def canonicalP (b : Band) (t : ℝ) (face : Bool) : Fin 3 → ℝ := p b t face true 0
def canonicalQ (b : Band) (t : ℝ) (face : Bool) : Fin 3 → ℝ := q b t face true 0
def canonicalNu (b : Band) (t : ℝ) (face : Bool) : Fin 3 → ℝ := nu b t face true 0
def canonical (b : Band) (R t : ℝ) (face : Bool) (i : Fin 3) (v : ℝ) : ℝ :=
  Vnu R (canonicalP b t face i) (canonicalQ b t face i) (canonicalNu b t face i) v

theorem cost_bounds (b : Band) : 0<positiveCost b ∧ positiveCost b≤619/1000 ∧
    (109/200)*coefficientCap b≤positiveCost b := by
  cases b <;> norm_num [positiveCost,coefficientCap]

theorem coefficient_order {b : Band} {t : ℝ} (ht : t∈domain b) :
    0<ell b t ∧ ell b t≤k b t ∧ ell b t≤c b t ∧
      (117/200)*c b t≤ell b t ∧ c b t≤113/100 := by
  by_cases hb : b=.low
  · subst b
    have hb := low_bounds ht
    have hr := low_correlations ht
    have h0 := (ranges ht).1.1
    have ht0 := (angle ht).1
    have hc0 := (ranges ht).2.2.2.1
    refine ⟨by linarith [hb.2.2.2.2.1],?_,?_,?_,?_⟩ <;>
      nlinarith [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.2.2.1,hr.1,
        mul_nonneg ht0 hc0.le]
  · rcases balanced_bounds hb ht with ⟨hk,hl0,hl1,hc0,hc1,hcl,he0,he1⟩
    refine ⟨by linarith,?_,by linarith,by nlinarith,hc1⟩
    rw [hk]
    exact hl1.le

theorem canonical_AB (face : Bool) {b : Band} {t : ℝ} (ht : t∈domain b) :
    canonicalP b t face 1=ell b t ∧ canonicalQ b t face 1=k b t ∧
      canonicalP b t face 2=ell b t ∧ canonicalQ b t face 2=c b t := by
  have ho := coefficient_order ht
  simp [canonicalP,canonicalQ,p,q,CriticalNegativeTOrdinaryData.small,
    CriticalNegativeTOrdinaryData.large,CriticalNegativeTOrdinaryData.alpha,
    CriticalNegativeTOrdinaryData.beta,bWeight,min_eq_left ho.2.1,max_eq_right ho.2.1,
    min_eq_left ho.2.2.1,max_eq_right ho.2.2.1]

theorem old_coefficients (face : Bool) (b : Band) (t : ℝ) (i : Fin 3) :
    canonicalP b t face i=ExceptionalContactBlocks.small (k b t) (ell b t) (c b t) (eta b t)
      (endpointX face t) (endpointE face t) ⟨i.val,by omega⟩ ∧
    canonicalQ b t face i=ExceptionalContactBlocks.large (k b t) (ell b t) (c b t) (eta b t)
      (endpointX face t) (endpointE face t) ⟨i.val,by omega⟩ ∧
    canonicalNu b t face i=ExceptionalContactBlocks.nu (k b t) (ell b t) (c b t) (eta b t)
      (endpointX face t) (endpointE face t) ⟨i.val,by omega⟩ := by
  fin_cases i <;> simp [canonicalP,canonicalQ,canonicalNu,p,q,nu,
    CriticalNegativeTOrdinaryData.small,CriticalNegativeTOrdinaryData.large,
    CriticalNegativeTOrdinaryData.alpha,CriticalNegativeTOrdinaryData.beta,
    CriticalNegativeTOrdinaryData.nu,bWeight,ExceptionalContactBlocks.small,
    ExceptionalContactBlocks.large,ExceptionalContactBlocks.alpha,
    ExceptionalContactBlocks.beta,ExceptionalContactBlocks.nu]

theorem low_canonical (face : Bool) {t : ℝ} (ht : t∈domain .low) (i : Fin 3) :
    0<canonicalP .low t face i ∧ canonicalP .low t face i≤canonicalNu .low t face i ∧
      canonicalNu .low t face i≤canonicalQ .low t face i ∧
      canonicalQ .low t face i≤21/20 ∧ 431/500≤canonicalQ .low t face i ∧
      (117/200+(7/20)*t)*canonicalQ .low t face i≤canonicalP .low t face i := by
  obtain ⟨hx,he⟩ := endpoints_mem face (angle ht).1
  let j : Fin 4 := ⟨i.val,by omega⟩
  have hbase := ExceptionalELowEnvelope.coefficient_conditions ht hx he j
  have hn := ExceptionalContactBlocks.nu_between (k .low t) (ell .low t) (c .low t)
    (eta .low t) (endpointX face t) (endpointE face t) j
  have hold := old_coefficients face .low t i
  rw [← hold.1,← hold.2.1] at hbase
  rw [← hold.1,← hold.2.1,← hold.2.2] at hn
  have h0P : canonicalP .low t face 0=ExceptionalContactBlocks.small (k .low t) (ell .low t)
      (c .low t) (eta .low t) (endpointX face t) (endpointE face t) 0 :=
    (old_coefficients face .low t 0).1
  have h0Q : canonicalQ .low t face 0=ExceptionalContactBlocks.large (k .low t) (ell .low t)
      (c .low t) (eta .low t) (endpointX face t) (endpointE face t) 0 :=
    (old_coefficients face .low t 0).2.1
  have hh := ExceptionalELowEnvelope.wide_data ht hx he (Or.inl rfl)
  rw [← h0P,← h0Q] at hh
  simp only [SoleLowChargeBounds.base] at hh
  refine ⟨hbase.1,hn.1,hn.2,hbase.2.2,?_,?_⟩
  · fin_cases i <;> dsimp only [Fin.reduceFinMk]
    · linarith [hh.2.1]
    · rw [(canonical_AB face ht).2.1]
      linarith [(low_bounds ht).1]
    · rw [(canonical_AB face ht).2.2.2]
      linarith [(low_bounds ht).1,(low_bounds ht).2.2.1]
  · fin_cases i <;> dsimp only [Fin.reduceFinMk]
    · have hcoef : 117/200+(7/20)*t≤2/3 := by linarith [ht.2]
      have hm := mul_le_mul_of_nonneg_right hcoef
        (show 0 ≤ canonicalQ .low t face 0 by linarith [hh.2.1])
      linarith [hh.1,hh.2.2]
    · obtain ⟨hp,hq,_,_⟩ := canonical_AB face ht
      rw [hp,hq]
      have hkc := (low_bounds ht).2.2.1
      have hc := mul_le_mul_of_nonneg_left hkc
        (show 0≤117/200+(7/20)*t by linarith [ht.1])
      linarith [(low_correlations ht).1]
    · obtain ⟨_,_,hp,hq⟩ := canonical_AB face ht
      rw [hp,hq]
      exact (low_correlations ht).1

theorem balanced_canonical (face : Bool) {b : Band} {t : ℝ}
    (hb : b≠.low) (ht : t∈domain b) (i : Fin 3) :
    0<canonicalP b t face i ∧ canonicalP b t face i≤canonicalNu b t face i ∧
      canonicalNu b t face i≤canonicalQ b t face i ∧
      (2/3)*canonicalQ b t face i≤canonicalP b t face i ∧
      1≤canonicalQ b t face i ∧ canonicalQ b t face i≤1131/1000 := by
  obtain ⟨hx,he⟩ := endpoints_mem face (angle ht).1
  let j : Fin 4 := ⟨i.val,by omega⟩
  have hbase := ExceptionalEBalanced.conditions hb ht hx he
  have hold := old_coefficients face b t i
  have hr := hbase.1 j
  have hq := hbase.2 j
  have hn := ExceptionalContactBlocks.nu_between (k b t) (ell b t) (c b t)
    (eta b t) (endpointX face t) (endpointE face t) j
  rw [← hold.1,← hold.2.1] at hr
  rw [← hold.2.1] at hq
  rw [← hold.1,← hold.2.1,← hold.2.2] at hn
  refine ⟨by linarith [hq.1],hn.1,hn.2,hr,?_,hq.2⟩
  have hk := (balanced_bounds hb ht).1
  fin_cases i <;> dsimp only [Fin.reduceFinMk]
  · cases face <;> simp [canonicalQ,q,CriticalNegativeTOrdinaryData.large,
      CriticalNegativeTOrdinaryData.alpha,CriticalNegativeTOrdinaryData.beta,
      endpointX,endpointE,hk,ExceptionalContactStress.tilt]
  · rw [(canonical_AB face ht).2.1,hk]
  · rw [(canonical_AB face ht).2.2.2]
    exact (balanced_bounds hb ht).2.2.2.1.le

theorem canonical_conditions (face : Bool) {b : Band} {t : ℝ} (ht : t∈domain b) (i : Fin 3) :
    0<canonicalP b t face i ∧ canonicalP b t face i≤canonicalNu b t face i ∧
      canonicalNu b t face i≤canonicalQ b t face i ∧
      canonicalQ b t face i≤2*canonicalP b t face i := by
  by_cases hb : b=.low
  · subst b
    have hh := low_canonical face ht i
    have hq : 0≤canonicalQ .low t face i := by linarith [hh.2.2.2.2.1]
    exact ⟨hh.1,hh.2.1,hh.2.2.1,by
      nlinarith [hh.2.2.2.2.2,mul_nonneg ht.1 hq]⟩
  · have hh := balanced_canonical face hb ht i
    exact ⟨hh.1,hh.2.1,hh.2.2.1,by linarith [hh.2.2.2.1]⟩

theorem b_bounds {b : Band} {t s : ℝ} {td : Bool}
    (ht : t∈domain b) (hs : s∈shortDomain td) :
    c b t≤bWeight td (c b t) s ∧ ell b t≤bWeight td (c b t) s ∧
      bWeight td (c b t) s≤2*ell b t ∧ bWeight td (c b t) s≤coefficientCap b := by
  have ho := coefficient_order ht
  have hc := (ranges ht).2.2.2.1
  have hsmall := short_small hs
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hsmall.1]; exact hsmall.2)
  have hcL : td=false → (19919/20000:ℝ)≤Real.cos s := by
    intro htd
    subst td
    have hs' : s∈Icc 0 (9/100:ℝ) := by simpa [shortDomain] using hs
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := s),hs'.1,hs'.2]
  have hsec : c b t≤bWeight td (c b t) s := by
    cases td
    · simp only [bWeight,Bool.false_eq_true,ite_false]
      exact (le_div_iff₀ hcos).2 (by nlinarith [Real.cos_le_one s])
    · simp [bWeight]
  have htwo : bWeight td (c b t) s≤2*ell b t := by
    cases td
    · simp only [bWeight,Bool.false_eq_true,ite_false]
      apply (div_le_iff₀ hcos).2
      have hh := mul_le_mul_of_nonneg_left (hcL rfl) ho.1.le
      nlinarith [ho.2.2.2.1]
    · simp only [bWeight,ite_true]
      nlinarith [ho.2.2.2.1]
  refine ⟨hsec,ho.2.2.1.trans hsec,htwo,?_⟩
  by_cases hb : b=.low
  · subst b
    have hcU := (low_bounds ht).2.2.2.1
    cases td
    · simp only [bWeight,Bool.false_eq_true,ite_false,coefficientCap,ite_true]
      apply (div_le_iff₀ hcos).2
      nlinarith [hcL rfl]
    · simp [bWeight,coefficientCap]
      linarith
  · cases td
    · simp only [bWeight,Bool.false_eq_true,ite_false,coefficientCap,ite_eq_right hb]
      apply (div_le_iff₀ hcos).2
      nlinarith [hcL rfl,ho.2.2.2.2]
    · simp only [bWeight,ite_true,coefficientCap,ite_eq_right hb]
      linarith [ho.2.2.2.2]

theorem actual_conditions (face : Bool) {b : Band} {t s : ℝ} {td : Bool}
    (ht : t∈domain b) (hs : s∈shortDomain td) (i : Fin 3) :
    0<p b t face td s i ∧ p b t face td s i≤nu b t face td s i ∧
      nu b t face td s i≤q b t face td s i ∧
      q b t face td s i≤2*p b t face td s i ∧ q b t face td s i≤coefficientCap b := by
  have hcanon := canonical_conditions face ht i
  have hbound : canonicalQ b t face i≤coefficientCap b := by
    by_cases hb : b=.low
    · subst b
      simpa [coefficientCap] using (low_canonical face ht i).2.2.2.1
    · have hh := (balanced_canonical face hb ht i).2.2.2.2.2
      simp only [coefficientCap,ite_eq_right hb]
      linarith
  have ho := coefficient_order ht
  have hbb := b_bounds ht hs
  fin_cases i <;> dsimp only [Fin.reduceFinMk] at hcanon hbound ⊢
  · rw [show p b t face td s 0=canonicalP b t face 0 from rfl,
      show q b t face td s 0=canonicalQ b t face 0 from rfl,
      show nu b t face td s 0=canonicalNu b t face 0 from rfl]
    exact ⟨hcanon.1,hcanon.2.1,hcanon.2.2.1,hcanon.2.2.2,hbound⟩
  · rw [show p b t face td s 1=canonicalP b t face 1 from rfl,
      show q b t face td s 1=canonicalQ b t face 1 from rfl,
      show nu b t face td s 1=canonicalNu b t face 1 from rfl]
    exact ⟨hcanon.1,hcanon.2.1,hcanon.2.2.1,hcanon.2.2.2,hbound⟩
  · have e1 : p b t face td s 2=ell b t := by
      show min (ell b t) (bWeight td (c b t) s)=ell b t
      exact min_eq_left hbb.2.1
    have e2 : q b t face td s 2=bWeight td (c b t) s := by
      show max (ell b t) (bWeight td (c b t) s)=bWeight td (c b t) s
      exact max_eq_right hbb.2.1
    have e3 : nu b t face td s 2=if td then c b t else ell b t := rfl
    rw [e1,e2,e3]
    cases td
    · simp only [Bool.false_eq_true,↓reduceIte]
      exact ⟨ho.1,le_rfl,hbb.2.1,hbb.2.2.1,hbb.2.2.2⟩
    · simp only [↓reduceIte,bWeight] at hbb ⊢
      exact ⟨ho.1,ho.2.2.1,le_rfl,hbb.2.2.1,hbb.2.2.2⟩

theorem canonical_le_pure (face : Bool) {b : Band} {R t s v : ℝ} {td : Bool}
    (hR : 0≤R) (ht : t∈domain b) (hs : s∈shortDomain td)
    (hv : v∈Icc 0 frameCap) (i : Fin 3) :
    canonical b R t face i v≤pure (single td i) R
      (p b t face td s i) (q b t face td s i) (nu b t face td s i) v := by
  have ho := coefficient_order ht
  have hb := b_bounds ht hs
  fin_cases i <;> dsimp only [Fin.reduceFinMk]
  · exact le_rfl
  · exact le_rfl
  · obtain ⟨_,_,hp,hq⟩ := canonical_AB face ht
    have hn : canonicalNu b t face 2=c b t := rfl
    rw [canonical,hp,hq,hn]
    cases td
    · have hm := HalfRatioNormGain.larger_monotone hR ho.1 ho.2.2.1 hb.1 hb.2.2.1 hv
      have hpen := mul_nonneg (sub_nonneg.mpr ho.2.2.1)
        (show 0≤1-Real.cos v by linarith [Real.cos_le_one v])
      have e1 : p b t face false s 2=ell b t := by
        show min (ell b t) (bWeight false (c b t) s)=ell b t
        exact min_eq_left hb.2.1
      have e2 : q b t face false s 2=bWeight false (c b t) s := by
        show max (ell b t) (bWeight false (c b t) s)=bWeight false (c b t) s
        exact max_eq_right hb.2.1
      have e3 : nu b t face false s 2=ell b t := rfl
      have e4 : single false 2=true := rfl
      rw [e1,e2,e3,e4]
      simp only [SingleAngleConcavity.pure,↓reduceIte]
      dsimp only [Vnu,SoleNormGain.normGain] at hm ⊢
      linarith
    · have e1 : p b t face true s 2=ell b t := by
        show min (ell b t) (bWeight true (c b t) s)=ell b t
        exact min_eq_left ho.2.2.1
      have e2 : q b t face true s 2=c b t := by
        show max (ell b t) (bWeight true (c b t) s)=c b t
        exact max_eq_right ho.2.2.1
      have e3 : nu b t face true s 2=c b t := rfl
      rw [e1,e2,e3]
      exact le_rfl

theorem positive_lower (face : Bool) {b : Band} {R t s v : ℝ} {td : Bool}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain b) (hs : s∈shortDomain td)
    (hv : v∈Icc 0 frameCap) (i : Fin 3) :
    -positiveCost b*v≤U R (p b t face td s i) (q b t face td s i) v := by
  have hc := actual_conditions face ht hs i
  have hh := OrdinaryPositiveEnvelope.U_lower hR hQ hc.1 (hc.2.1.trans hc.2.2.1) hc.2.2.2.1 hv
  have hq := mul_le_mul_of_nonneg_right hc.2.2.2.2 hv.1
  have hcost := mul_le_mul_of_nonneg_right (cost_bounds b).2.2 hv.1
  nlinarith

theorem canonical_growth (face : Bool) {b : Band} {R t v : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain b) (hv : v∈Icc 0 t) (i : Fin 3) :
    positiveCost b*(frameCap-v)≤canonical b R t face i frameCap-canonical b R t face i v := by
  have hcan := canonical_conditions face ht i
  have hlen : 0≤frameCap-v := by linarith [(angle ht).2,hv.2]
  by_cases hb : b=.low
  · subst b
    have hh := low_canonical face ht i
    have hq0 : 0≤canonicalQ .low t face i := by linarith [hh.2.2.2.2.1]
    have hr : (117/200)*canonicalQ .low t face i≤canonicalP .low t face i := by
      nlinarith [hh.2.2.2.2.2,mul_nonneg ht.1 hq0]
    have hg := SolePositiveTGrowth.low_growth hR hQL hcan.1 (hcan.2.1.trans hcan.2.2.1) hr
      hh.2.2.2.2.1 hcan.2.2.1 (show v∈Icc 0 (1/5:ℝ) from ⟨hv.1,by linarith [ht.2,hv.2]⟩)
    dsimp [canonical,positiveCost]
    simp only [frameCap] at hg hlen ⊢
    linarith
  · have hh := balanced_canonical face hb ht i
    have hg := SoleAngleGrowth.Vnu_growth hR hQL hQU hcan.1 (hcan.2.1.trans hcan.2.2.1) hh.2.2.2.1 hcan.2.2.1
      (show v∈Icc 0 frameCap from ⟨hv.1,hv.2.trans (angle ht).2⟩)
      (by norm_num [frameCap]) (hv.2.trans (angle ht).2)
    have hscale := mul_le_mul_of_nonneg_right hh.2.2.2.2.1 hlen
    dsimp [canonical,positiveCost]
    rw [ite_eq_right hb]
    simp only [frameCap] at hg hlen hscale ⊢
    linarith

end SquaresInCircles.Eight.ExceptionalNegativeTOrdinaryData
