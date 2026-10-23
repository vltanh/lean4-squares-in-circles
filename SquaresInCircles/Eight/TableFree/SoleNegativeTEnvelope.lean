module

public import SquaresInCircles.Eight.TableFree.SoleNegativeTOrdinaryData
public import SquaresInCircles.Eight.TableFree.SolePositiveTEnvelope

/-!
# Complete ordinary-angle envelope for both negative T rows

Uncompiled source. Each separated alternative pays its own pure
negative charge by a shifted concave secant. The same-block alternatives
occur only at the original two-angle H/B blocks. The positive-surplus
side follows from the same original occupied-sign concentration and the
uniform negative chord, including both equality junctions.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleNegativeTEnvelope
open SoleTScalarModel SoleNegativeTCoefficients SoleNegativeTOrdinaryData
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity ActualOrdinaryBlocks CorrelatedSameBlock

theorem mixed_ratio {f : Family} (atG : Bool) {td : Bool} {t : ℝ}
    (ht : t∈domain f) (i : Fin 4) (hi : single f td i=false) :
    (117/200)*large f atG t i≤small f atG t i := by
  have hr := SolePositiveTCoefficients.ratio_lower (face f atG) ht (zero_mem ht) i
  change SolePositiveTCoefficients.ratio f t i*large f atG t i≤small f atG t i at hr
  have hq := (SoleNegativeTCoefficients.positive atG ht i).2.2.trans_le
    (min_le_max : small f atG t i≤large f atG t i)
  have ht0 := (angle ht).1
  rcases mixed_indices hi with ⟨rfl,hde⟩ | ⟨rfl,htd⟩
  · cases f <;> simp [isDE] at hde <;>
      simp [SolePositiveTCoefficients.ratio] at hr <;> linarith
  · cases f <;> simp [SolePositiveTCoefficients.ratio] at hr <;>
      nlinarith [mul_nonneg ht0 hq.le]

theorem base_mixed {f : Family} (atG : Bool) {td : Bool} (R : ℝ) {t : ℝ}
    (ht : t∈domain f) (i : Fin 4) (hi : single f td i=false) :
    V R (small f atG t i) (large f atG t i) t≤
      M R (small f atG t i) (large f atG t i) t := by
  have hflag : SolePositiveTOrdinaryData.single (face f atG) i=false := by
    rcases mixed_indices hi with ⟨rfl,hde⟩ | ⟨rfl,htd⟩
    · simp [SolePositiveTOrdinaryData.single,face,hde]
    · simp [SolePositiveTOrdinaryData.single,face]
  have hh := SolePositiveTEnvelope.same_block (face f atG) (R:=R) ht (zero_mem ht) i hflag
  simpa only [SingleAngleConcavity.pure,hflag,if_false] using hh

theorem negative_from_base {R p q t s : ℝ} (hq : 0≤q)
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 t)
    (hbase : V R p q t≤M R p q t) :
    V R p q (t-s)≤mixedBlock R p q (frameCap-t) (frameCap-s) := by
  have ha : frameCap-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hw : t-s∈Icc 0 (frameCap-(frameCap-t)) :=
    ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have ht' : t∈Icc 0 (frameCap-(frameCap-t)) := ⟨ht.1,by ring_nf⟩
  have hc := cosine_increment_anti ha hw ht' (by linarith [hs.1])
  have hc' : Real.cos frameCap-Real.cos t≤Real.cos (frameCap-s)-Real.cos (t-s) := by
    convert hc using 1 <;> congr 1 <;> ring
  have hm := mul_le_mul_of_nonneg_left hc' hq
  dsimp [V,M,mixedBlock] at hbase ⊢
  rw [show frameCap-t-(frameCap-s)= -(t-s) by ring]
  nlinarith

theorem same_negative {f : Family} (atG td : Bool) (R : ℝ) {t s : ℝ}
    (ht : t∈domain f) (hs : s∈Icc 0 t) (i : Fin 4) (hi : single f td i=false) :
    oldV f atG R t (t-s) i≤block f atG td R t s (frameCap-t) (frameCap-s) i := by
  have hq := (SoleNegativeTCoefficients.positive atG ht i).2.2.trans_le
    (min_le_max : small f atG t i≤large f atG t i)
  rw [oldV,mixed_nu atG ht i hi,Vnu_larger,block,hi,if_false]
  exact negative_from_base hq.le (angle ht) hs (base_mixed atG R ht i hi)

theorem same_positive {f : Family} (atG td : Bool) {R t s : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f)
    (hs : s∈shortDomain td) (hts : t≤s) (i : Fin 4) (hi : single f td i=false) :
    -gamma f*(s-t)≤block f atG td R t s (frameCap-t) (frameCap-s) i := by
  have hp := (SoleNegativeTCoefficients.positive atG ht i).2.2
  have hq := hp.trans_le (min_le_max : small f atG t i≤large f atG t i)
  have ht' := angle ht
  have hs' := short_small hs
  have hP : frameCap-t∈Icc 0 frameCap := ⟨by linarith [ht'.2],by linarith [ht'.1]⟩
  have hN : frameCap-s∈Icc 0 (frameCap-t) := ⟨by linarith [hs'.2],by linarith⟩
  have hm := positive_surplus (R:=R) hq.le (mixed_ratio atG ht i hi) hP hN
  rw [show frameCap-t-(frameCap-s)=s-t by ring] at hm
  have hU := positive_lower atG td hR hQ ht hs
    (show s-t∈Icc 0 frameCap from ⟨by linarith,by linarith [hs'.2,ht'.1]⟩) i
  rw [positive_mixed atG R t s (s-t) i hi] at hU
  simpa only [block,hi,if_false] using hU.trans hm

theorem mixed_line {f : Family} (atG td : Bool) (R : ℝ) {t s : ℝ}
    (ht : t∈domain f) (hs : s∈shortDomain td) (i : Fin 4) (hi : single f td i=false) :
    ConcaveOn ℝ (Icc (max 0 (s-t)) (frameCap-t))
      (fun P => block f atG td R t s P (t-s+P) i) := by
  let p := small f atG t i
  let q := large f atG t i
  have hp : 0≤p := (SoleNegativeTCoefficients.positive atG ht i).2.2.le
  have hq : 0≤q := hp.trans min_le_max
  have hdom := OccupiedSignedConcentration.Data.line_domain (angle ht) (short_small hs)
  let K := R*(pairNorm p q (s-t)-pairNorm p q 0)
  have he (P : ℝ) : block f atG td R t s P (t-s+P) i=
      p*(phi P-1)+q*(Real.cos (t-s+P)-1)-K := by
    simp only [block,hi,if_false,mixedBlock]
    rw [show P-(t-s+P)=s-t by ring]
    rfl
  have hc : ConcaveOn ℝ (Icc (max 0 (s-t)) (frameCap-t))
      (fun P => p*(phi P-1)+q*(Real.cos (t-s+P)-1)-K) := by
    apply concave_of_deriv2
      (f' := fun P => p*(Real.cos P-Real.sin P)-q*Real.sin (t-s+P))
      (f'' := fun P => -p*(Real.sin P+Real.cos P)-q*Real.cos (t-s+P))
    · intro P hP
      have hfirst := ((phi_hasDerivAt P).sub_const 1).const_mul p
      have hsecond := ((((hasDerivAt_id P).const_add (t-s)).cos).sub_const 1).const_mul q
      convert (hfirst.add hsecond).sub_const K using 1 <;> ring
    · intro P hP
      have hfirst := ((Real.hasDerivAt_cos P).sub (Real.hasDerivAt_sin P)).const_mul p
      have hsecond := (((hasDerivAt_id P).const_add (t-s)).sin).const_mul q
      convert hfirst.sub hsecond using 1 <;> ring
    · intro P hP
      obtain ⟨hPP,hNN⟩ := hdom.2 P hP
      obtain ⟨hcP,_,hsP,_,_⟩ := transport_trig hPP
      obtain ⟨hcN,_,hsN,_,_⟩ := transport_trig hNN
      have hfirst := mul_nonneg hp (show 0≤Real.sin P+Real.cos P by linarith)
      have hsecond := mul_nonneg hq (show 0≤Real.cos (t-s+P) by linarith)
      linarith
  convert hc using 1
  funext P
  exact he P

theorem negative_balance {f : Family} (atG td : Bool) (P N : Fin 4 → ℝ) {R t s L : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain f) (hs : s∈shortDomain td) (hst : s≤t)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-t) (hbalance : (∑ i,N i)=t-s+∑ i,P i)
    (hsingle : ∀ i,single f td i=true → P i=0 ∨ N i=0)
    (hpure : ∀ i,Used f i → L≤oldV f atG R t (t-s) i) :
    L≤∑ i,block f atG td R t s (P i) (N i) i := by
  let D := data atG td hR hQU ht hs
  have hs' := short_small hs
  have hst' : s∈Icc 0 t := ⟨hs'.1,hst⟩
  apply D.lower_from_endpoints P N hP hN (angle ht) hs' hbudget hbalance hsingle
    (fun i hi => mixed_line atG td R ht hs i hi)
  · intro _ i
    exact negative_lower atG hpure i
  · intro hts i
    have he : s=t := le_antisymm hst hts
    have hp := hpure 0 (Or.inr (by decide))
    rw [he,sub_self,SoleNegativeTGrowth.zero] at hp
    simpa [D,data,he] using hp
  · intro i hi
    have hused : Used f i := by
      rcases mixed_indices hi with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> exact Or.inr (by decide)
    exact (hpure i hused).trans (same_negative atG td R ht hst' i hi)
  · intro i j _
    have hshift (k : Fin 4) (hk : Used f k) :
        L+gamma f*(frameCap-t)≤oldV f atG R t (frameCap-s) k := by
      have hh := SoleNegativeTGrowth.shifted_chord atG hR hQL hQU ht hst' k
      linarith [hpure k hk]
    have hneg := negative_lower atG hshift j
    have hpos := positive_lower atG td hR hQU ht hs
      (show frameCap-t∈Icc 0 frameCap from ⟨by linarith [(angle ht).2],by linarith [(angle ht).1]⟩) i
    change L≤positive f atG td R t s (frameCap-t) i+negative f atG R t (frameCap-s) j
    linarith

theorem positive_balance {f : Family} (atG td : Bool) (P N : Fin 4 → ℝ) {R t s : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain f) (hs : s∈shortDomain td) (hts : t≤s)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-t) (hbalance : (∑ i,N i)=t-s+∑ i,P i)
    (hsingle : ∀ i,single f td i=true → P i=0 ∨ N i=0) :
    -gamma f*(s-t)≤∑ i,block f atG td R t s (P i) (N i) i := by
  let D := data atG td hR hQU ht hs
  have hs' := short_small hs
  apply D.lower_from_endpoints P N hP hN (angle ht) hs' hbudget hbalance hsingle
    (fun i hi => mixed_line atG td R ht hs i hi)
  · intro hst i
    have he : s=t := le_antisymm hst hts
    simp [D,data,he]
  · intro _ i
    exact positive_lower atG td hR hQU ht hs
      ⟨by linarith,by linarith [hs'.2,(angle ht).1]⟩ i
  · intro i hi
    exact same_positive atG td hR hQU ht hs hts i hi
  · intro i j _
    have hneg := negative_linear atG hR hQL hQU ht
      (show frameCap-s∈Icc 0 frameCap from ⟨by linarith [hs'.2],by linarith [hs'.1]⟩) j
    have hpos := positive_lower atG td hR hQU ht hs
      (show frameCap-t∈Icc 0 frameCap from ⟨by linarith [(angle ht).2],by linarith [(angle ht).1]⟩) i
    change -gamma f*(s-t)≤positive f atG td R t s (frameCap-t) i+
      negative f atG R t (frameCap-s) j
    linarith

end SquaresInCircles.Eight.TableFree.SoleNegativeTEnvelope
