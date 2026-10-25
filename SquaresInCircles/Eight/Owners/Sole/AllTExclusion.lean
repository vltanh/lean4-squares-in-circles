module

public import SquaresInCircles.Eight.Owners.Flat.TStress
public import SquaresInCircles.Eight.Owners.SecantNormCurvature
public import SquaresInCircles.Eight.Owners.Negative.SecondaryEExclusion
public import SquaresInCircles.Eight.Owners.Positive.GAOuterSoleReduction
public import SquaresInCircles.Eight.Owners.Sole.NegativeTDSupport
public import SquaresInCircles.Eight.Owners.Sole.PositiveExclusion
public import SquaresInCircles.Eight.Owners.Sole.NegativeTScalar
public import SquaresInCircles.Eight.Owners.Sole.PositiveTEndpoint
public import SquaresInCircles.Eight.Owners.Sole.PositiveTEnvelope

/-!
# Eight squares: the complete T-owner join for sole EH and nonpositive sole DE

This finite dispatch consumes the actual preprocessed
T rows, including the negative-BT alignment produced by preprocessing.
It permits all original ordinary signs and both weak AB owners. Its
sole-DE sign is explicit; the positive-E contact successor is separate.
-/

section
/-!
## Complete ordinary-angle envelope for both negative T rows

Each separated alternative pays its own pure
negative charge by a shifted concave secant. The same-block alternatives
occur only at the original two-angle H/B blocks. The positive-surplus
side follows from the same original occupied-sign concentration and the
uniform negative chord, including both equality junctions.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleNegativeTEnvelope
open SoleTScalarModel SoleNegativeTCoefficients SoleNegativeTOrdinaryData
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity ActualOrdinaryBlocks CorrelatedSameBlock

theorem mixed_ratio {f : Family} (atG : Bool) {td : Bool} {t : ℝ}
    (ht : t∈domain f) (i : Fin 4) (hi : single f td i=false) :
    (117/200)*large f atG t i≤ small f atG t i := by
  have hr := SolePositiveTCoefficients.ratio_lower (face f atG) ht (zero_mem ht) i
  change SolePositiveTCoefficients.ratio f t i*large f atG t i≤ small f atG t i at hr
  have hq : 0<large f atG t i := (SoleNegativeTCoefficients.positive atG ht i).2.2.trans_le
    (min_le_max : small f atG t i≤ large f atG t i)
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
  simp only [SingleAngleConcavity.pure,hflag,Bool.false_eq_true,↓reduceIte] at hh
  exact hh

theorem negative_from_base {R p q t s : ℝ} (hq : 0≤q)
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 t)
    (hbase : V R p q t≤M R p q t) :
    V R p q (t-s)≤ mixedBlock R p q (frameCap-t) (frameCap-s) := by
  have ha : frameCap-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hw : t-s∈Icc 0 (frameCap-(frameCap-t)) :=
    ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have ht' : t∈Icc 0 (frameCap-(frameCap-t)) := ⟨ht.1,le_of_eq (by ring)⟩
  have hc := cosine_increment_anti ha hw ht' (by linarith [hs.1])
  have hc' : Real.cos frameCap-Real.cos t≤Real.cos (frameCap-s)-Real.cos (t-s) := by
    have e1 : frameCap-t+t=frameCap := by ring
    have e2 : frameCap-t+(t-s)=frameCap-s := by ring
    simp only [e1,e2] at hc
    exact hc
  have hm := mul_le_mul_of_nonneg_left hc' hq
  simp only [V,M,mixedBlock] at hbase ⊢
  rw [show frameCap-t-(frameCap-s)= -(t-s) by ring]
  linarith

theorem same_negative {f : Family} (atG td : Bool) (R : ℝ) {t s : ℝ}
    (ht : t∈domain f) (hs : s∈Icc 0 t) (i : Fin 4) (hi : single f td i=false) :
    oldV f atG R t (t-s) i≤block f atG td R t s (frameCap-t) (frameCap-s) i := by
  have hq := (SoleNegativeTCoefficients.positive atG ht i).2.2.trans_le
    (min_le_max : small f atG t i≤ large f atG t i)
  rw [oldV,mixed_nu atG ht i hi,Vnu_larger]
  simp only [block,hi,Bool.false_eq_true,↓reduceIte]
  exact negative_from_base hq.le (angle ht) hs (base_mixed atG R ht i hi)

theorem same_positive {f : Family} (atG td : Bool) {R t s : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f)
    (hs : s∈shortDomain td) (hts : t≤ s) (i : Fin 4) (hi : single f td i=false) :
    -gamma f*(s-t)≤block f atG td R t s (frameCap-t) (frameCap-s) i := by
  have hp := (SoleNegativeTCoefficients.positive atG ht i).2.2
  have hq := hp.trans_le (min_le_max : small f atG t i≤ large f atG t i)
  have ht' := angle ht
  have hs' := short_small hs
  have hP : frameCap-t∈Icc 0 frameCap := ⟨by linarith [ht'.2],by linarith [ht'.1]⟩
  have hN : frameCap-s∈Icc 0 (frameCap-t) := ⟨by linarith [hs'.2],by linarith⟩
  have hm := positive_surplus (R:=R) hq.le (mixed_ratio atG ht i hi) hP hN
  rw [show frameCap-t-(frameCap-s)=s-t by ring] at hm
  have hU := positive_lower atG td hR hQ ht hs
    (show s-t∈Icc 0 frameCap from ⟨by linarith,by linarith [hs'.2,ht'.1]⟩) i
  rw [positive_mixed atG R t s (s-t) i hi] at hU
  simp only [block,hi,Bool.false_eq_true,↓reduceIte]
  exact hU.trans hm

theorem mixed_line {f : Family} (atG td : Bool) (R : ℝ) {t s : ℝ}
    (ht : t∈domain f) (hs : s∈shortDomain td) (i : Fin 4) (hi : single f td i=false) :
    ConcaveOn ℝ (Icc (max 0 (s-t)) (frameCap-t))
      (fun P => block f atG td R t s P (t-s+P) i) := by
  obtain ⟨p,hp_def⟩ : ∃ p, p=small f atG t i := ⟨_,rfl⟩
  obtain ⟨q,hq_def⟩ : ∃ q, q=large f atG t i := ⟨_,rfl⟩
  have hp0 : 0 ≤ small f atG t i := (SoleNegativeTCoefficients.positive atG ht i).2.2.le
  have hp : 0≤p := by rw [hp_def]; exact hp0
  have hq : 0≤q := by rw [hq_def]; exact hp0.trans min_le_max
  have hdom := OccupiedSignedConcentration.Data.line_domain (angle ht) (short_small hs)
  obtain ⟨K,hK⟩ : ∃ K, K=R*(pairNorm p q (s-t)-pairNorm p q 0) := ⟨_,rfl⟩
  have he (P : ℝ) : block f atG td R t s P (t-s+P) i=
      p*(PositiveAngularEnvelope.phi P-1)+q*(Real.cos (t-s+P)-1)-K := by
    simp only [block,hi,Bool.false_eq_true,↓reduceIte,mixedBlock]
    rw [show P-(t-s+P)=s-t by ring,hK,hp_def,hq_def]
  have hc : ConcaveOn ℝ (Icc (max 0 (s-t)) (frameCap-t))
      (fun P => p*(PositiveAngularEnvelope.phi P-1)+q*(Real.cos (t-s+P)-1)-K) := by
    apply concave_of_deriv2
      (f' := fun P => p*(Real.cos P-Real.sin P)-q*Real.sin (t-s+P))
      (f'' := fun P => -p*(Real.sin P+Real.cos P)-q*Real.cos (t-s+P))
    · intro P _
      have hfirst := ((phi_hasDerivAt P).sub_const 1).const_mul p
      have hsecond := ((((hasDerivAt_id' P).const_add (t-s)).cos).sub_const 1).const_mul q
      convert (hfirst.fun_add hsecond).sub_const K using 1
      ring
    · intro P _
      have hfirst := ((Real.hasDerivAt_cos P).fun_sub (Real.hasDerivAt_sin P)).const_mul p
      have hsecond := (((hasDerivAt_id' P).const_add (t-s)).sin).const_mul q
      convert hfirst.fun_sub hsecond using 1
      ring
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
    (ht : t∈domain f) (hs : s∈shortDomain td) (hts : t≤ s)
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

end SquaresInCircles.Eight.SoleNegativeTEnvelope
end
end
end

section
/-!
## The ordinary blocks of the cycle for a negative T primary

The negative primary removes exactly its negative variation (`original_budgets`); the other
ordinary angles and the weak owner of AB stay. D is charged against its sorted support at the
radius `q`, and the other three anchors keep their circle supports (`D_minorant`,
`block_minorant`, `negative_original`, `positive_original`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleNegativeTOriginalBlocks
open Candidate SoleTScalarModel SolePositiveTSplitModel
open SoleNegativeTCoefficients SoleNegativeTOrdinaryData
open ActualCoreEBlocks ActualOrdinaryBlocks PositiveAngularEnvelope
open OrdinaryAngleConcavity SingleAngleConcavity

def blocks (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ) :
    Fin 4 → Block :=
  SoleEStress.blocks C ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f)
    (n (face f atG) t 0) (k f t 0) (ell f t 0)
    (SoleNegativeTSplit.btWeight f td t s) (SoleNegativeTSplit.tdWeight f td t s)
    (p (face f atG) t 0) (lambda f)

def contribution (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool)
    (q t s : ℝ) (i : Fin 4) : ℝ :=
  if i=3 then SoleNegativeTDSupport.increment q (p (face f atG) t 0)
    (dCoefficient f td t s) (ordinaryDE C (deOwner f))
  else (blocks C ab f atG td t s i).increment (Real.sqrt q)

def ordinary (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool) (q t s : ℝ) : ℝ :=
  ∑ i,contribution C ab f atG td q t s i

theorem sum_parts (C : SignedCycle) {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (f : Family) (atG td : Bool) (t s : ℝ) (F : ℝ → ℝ) (hF : F 0=0) :
    (∑ i,(F (blocks C ab f atG td t s i).u+F (blocks C ab f atG td t s i).v))=
      (∑ j,F (delta C.theta j))-F (delta C.theta G)-F (ePrimary C f)-F (tPrimary C td) := by
  have hh := ActualCoreEBlocks.sum_parts C hab
    (SolePositiveTOriginalBlocks.btOwner_cases td) (SolePositiveTOriginalBlocks.tdOwner_cases td)
    (SolePositiveTSplitSupport.deOwner_cases f) (SolePositiveTSplitSupport.ehOwner_cases f)
    (n (face f atG) t 0) (k f t 0) (ell f t 0)
    (SoleNegativeTSplit.btWeight f td t s) (SoleNegativeTSplit.tdWeight f td t s) F hF
  have he : (∑ i,(F (blocks C ab f atG td t s i).u+F (blocks C ab f atG td t s i).v))=
      ∑ i,(F (ActualCoreEBlocks.blocks C ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f)
        (n (face f atG) t 0) (k f t 0) (ell f t 0)
        (SoleNegativeTSplit.btWeight f td t s) (SoleNegativeTSplit.tdWeight f td t s) i).u+
      F (ActualCoreEBlocks.blocks C ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f)
        (n (face f atG) t 0) (k f t 0) (ell f t 0)
        (SoleNegativeTSplit.btWeight f td t s) (SoleNegativeTSplit.tdWeight f td t s) i).v) := by
    apply Finset.sum_congr rfl
    intro i _
    fin_cases i <;> rfl
  rw [he,hh]
  cases f <;> cases td <;>
    simp [btOwner,tdOwner,deOwner,ehOwner,ePrimary,tPrimary,primaryDE,primaryEH,isDE,hF] <;> ring

theorem original_budgets {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (f : Family) (atG td : Bool) {t s : ℝ}
    (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤ePrimary C f) (hs : 0≤ s)
    (hsource : tPrimary C td= -s) (htotal : delta C.theta G+ePrimary C f=t) :
    0≤t ∧ (∑i,(blocks C ab f atG td t s i).P)≤frameCap-t ∧
      (∑i,(blocks C ab f atG td t s i).N)=t-s+∑i,(blocks C ab f atG td t s i).P := by
  have hp := sum_parts C hab f atG td t s positivePart positivePart_zero
  have hn := sum_parts C hab f atG td t s negativePart negativePart_zero
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hG
  have hPE : positivePart (ePrimary C f)=ePrimary C f := max_eq_left hE
  have hPT : positivePart (tPrimary C td)=0 := by
    rw [hsource]
    exact max_eq_right (by linarith)
  have hNG : negativePart (delta C.theta G)=0 := max_eq_right (by linarith)
  have hNE : negativePart (ePrimary C f)=0 := max_eq_right (by linarith)
  have hNT : negativePart (tPrimary C td)=s := by
    simp [hsource,negativePart,max_eq_left hs]
  change (∑ i,(blocks C ab f atG td t s i).P)=
    positiveVariation C.theta-positivePart (delta C.theta G)-positivePart (ePrimary C f)-
      positivePart (tPrimary C td) at hp
  change (∑ i,(blocks C ab f atG td t s i).N)=
    negativeVariation C.theta-negativePart (delta C.theta G)-negativePart (ePrimary C f)-
      negativePart (tPrimary C td) at hn
  rw [hPG,hPE,hPT] at hp
  rw [hNG,hNE,hNT] at hn
  have hv := variations_equal C.theta
  refine ⟨by linarith,by linarith,by linarith⟩

theorem individual_budgets {C : SignedCycle} {ab : Fin 4} {f : Family} {atG td : Bool}
    {t s : ℝ} (ht : 0≤t) (hs : 0≤ s)
    (hP : (∑i,(blocks C ab f atG td t s i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab f atG td t s i).N)=t-s+∑i,(blocks C ab f atG td t s i).P)
    (i : Fin 4) :
    (blocks C ab f atG td t s i).P≤frameCap ∧ (blocks C ab f atG td t s i).N≤frameCap := by
  have hp := Finset.single_le_sum (fun j _ => (blocks C ab f atG td t s j).P_nonneg)
    (Finset.mem_univ i)
  have hn := Finset.single_le_sum (fun j _ => (blocks C ab f atG td t s j).N_nonneg)
    (Finset.mem_univ i)
  constructor <;> linarith

theorem single_data {C : SignedCycle} (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ)
    (hflat : td=false → delta C.theta T=0) (i : Fin 4) (hi : single f td i=true) :
    (blocks C ab f atG td t s i).v=0 := by
  fin_cases i <;> cases f <;> cases td <;>
    simp_all [single,blocks,SoleEStress.blocks,btOwner,tdOwner,deOwner,ehOwner,
      ordinaryDE,ordinaryEH,isDE]

theorem single_parts {C : SignedCycle} (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ)
    (hflat : td=false → delta C.theta T=0) (i : Fin 4) (hi : single f td i=true) :
    (blocks C ab f atG td t s i).P=0 ∨ (blocks C ab f atG td t s i).N=0 := by
  have hv := single_data ab f atG td t s hflat i hi
  by_cases hu : 0≤(blocks C ab f atG td t s i).u
  · right
    simp [Block.N,hv,negativePart,max_eq_right (show -(blocks C ab f atG td t s i).u≤0 by linarith)]
  · left
    simp [Block.P,hv,positivePart,max_eq_right (le_of_lt (lt_of_not_ge hu))]

theorem angles_small {C : SignedCycle} (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (i : Fin 4) :
    |(blocks C ab f atG td t s i).u|≤frameCap ∧ |(blocks C ab f atG td t s i).v|≤frameCap := by
  have hz : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hite (P : Prop) [Decidable P] (j : Vertex) :
      |(if P then delta C.theta j else 0)|≤frameCap := by
    split_ifs
    · exact ha j
    · exact hz
  have hite' (P : Prop) [Decidable P] (j : Vertex) :
      |(if P then 0 else delta C.theta j)|≤frameCap := by
    split_ifs
    · exact hz
    · exact ha j
  fin_cases i
  · exact ⟨ha H,hite _ _⟩
  · exact ⟨hite' _ _,hz⟩
  · exact ⟨hite _ _,hite _ _⟩
  · exact ⟨hite _ _,hite _ _⟩

theorem Vnu_min_max (R a b nu v : ℝ) :
    Vnu R (min a b) (max a b) nu v=Vnu R a b nu v := by
  rcases le_total a b with hab | hba
  · simp [min_eq_left hab,max_eq_right hab]
  · simp [min_eq_right hba,max_eq_left hba,Vnu,pairNorm_symm]

theorem old_A (f : Family) (atG : Bool) (R t v : ℝ) :
    oldV f atG R t v 1=Vnu R (ell f t 0) (k f t 0) (ell f t 0) v := by
  change Vnu R (min (k f t 0) (ell f t 0)) (max (k f t 0) (ell f t 0))
    (ell f t 0) v=_
  rw [Vnu_min_max]
  simp [Vnu,pairNorm_symm]

theorem old_B (f : Family) (atG : Bool) (R t v : ℝ) :
    oldV f atG R t v 2=Vnu R (ell f t 0) (c f t 0) (c f t 0) v := by
  simp only [oldV,small,large,SoleNegativeTCoefficients.first,SoleNegativeTCoefficients.second,
    face,SoleTScalarModel.first,SoleTScalarModel.second,m,Real.cos_zero,Real.sin_zero,mul_one,
    mul_zero,add_zero,↓reduceIte,SoleNegativeTCoefficients.nu,Matrix.cons_val]
  rw [Vnu_min_max]

theorem old_D (f : Family) (atG : Bool) (R t v : ℝ) :
    oldV f atG R t v 3=Vnu R (p (face f atG) t 0) (c f t 0)
      (max (p (face f atG) t 0) (c f t 0)) v := by
  simp only [oldV,small,large,SoleNegativeTCoefficients.first,SoleNegativeTCoefficients.second,
    face,SoleTScalarModel.first,SoleTScalarModel.second,m,Real.cos_zero,Real.sin_zero,mul_one,
    mul_zero,add_zero,↓reduceIte,SoleNegativeTCoefficients.nu,Matrix.cons_val]
  rw [Vnu_min_max]

theorem changed_B_negative {f : Family} (atG : Bool) {R t s v : ℝ}
    (hR : 0≤R) (ht : t∈domain f) (hs : s∈Icc 0 (9/100:ℝ)) (hv : v∈Icc 0 frameCap) :
    oldV f atG R t v 2≤Vnu R (ell f t 0) (c f t 0/Real.cos s) (ell f t 0) v := by
  have hb := changed_B_domain atG ht hs
  have hc := c_ge_ell atG ht
  have hcpos := (coefficient_positive ht (zero_mem ht)).2.2.1
  have hsec := SoleNegativeTSplit.secant_nonneg
    (show s∈Icc 0 frameCap from ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩)
  have hcg : c f t 0≤c f t 0/Real.cos s := by
    have hh := mul_nonneg hcpos.le hsec.2
    have he : c f t 0/Real.cos s=c f t 0*(1/Real.cos s) := by ring
    nlinarith
  have hgain := HalfRatioNormGain.larger_monotone hR hb.1 hc hcg hb.2.2 hv
  have hcos := mul_le_mul_of_nonpos_right hc (show Real.cos v-1≤0 by linarith [Real.cos_le_one v])
  rw [old_B]
  dsimp only [Vnu,SoleNormGain.normGain] at *
  linarith

theorem unchanged_coefficients (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool)
    (t s : ℝ) (i : Fin 4) (hD : i≠3) (hB : ¬(i=2 ∧ td=false)) :
    (blocks C ab f atG td t s i).p=small f atG t i ∧
      (blocks C ab f atG td t s i).q=large f atG t i := by
  fin_cases i <;> cases td <;>
    simp_all [blocks,SoleEStress.blocks,Block.p,Block.q,small,large,
      SoleNegativeTCoefficients.first,SoleNegativeTCoefficients.second,face,
      SoleTScalarModel.first,SoleTScalarModel.second,SoleNegativeTSplit.btWeight,
      SoleNegativeTSplit.tdWeight,m,min_comm,max_comm]

theorem unchanged_nu (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool)
    (t s : ℝ) (i : Fin 4) (hD : i≠3) (hB : ¬(i=2 ∧ td=false))
    (hi : single f td i=true) : (blocks C ab f atG td t s i).alpha=nu f atG t i := by
  fin_cases i <;> cases hf : isDE f <;> cases td <;>
    simp_all [single,blocks,SoleEStress.blocks,SoleNegativeTCoefficients.nu]

theorem D_minorant {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s : ℝ}
    (hQL : qLow≤q) (hQU : q≤qCap) (ht : t∈domain f) (hs : s∈shortDomain td)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hflat : td=false → delta C.theta T=0) :
    block f atG td (Real.sqrt q) t s (blocks C ab f atG td t s 3).P
      (blocks C ab f atG td t s 3).N 3≤contribution C ab f atG td q t s 3 := by
  have hv := single_data ab f atG td t s hflat 3 (by simp [single])
  have hu : (blocks C ab f atG td t s 3).u=ordinaryDE C (deOwner f) := rfl
  have hd := (ordinary_small (de:=deOwner f) (eh:=ehOwner f) ha).1
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hp := p_ge_one atG ht
  have hcoeff := coefficient_positive ht (zero_mem ht)
  have hcg := d_coefficient_ge td ht hs
  have hpc := p_half_c atG ht
  have hc3 : contribution C ab f atG td q t s 3=SoleNegativeTDSupport.increment q
      (p (face f atG) t 0) (dCoefficient f td t s) (ordinaryDE C (deOwner f)) := by
    simp [contribution]
  rw [hc3]
  by_cases hde : isDE f=true
  · have hd0 : ordinaryDE C (deOwner f)=0 := by simp [deOwner,ordinaryDE,hde]
    have hP : (blocks C ab f atG td t s 3).P=0 := by
      simp [Block.P,hv,hu,hd0,positivePart]
    have hN : (blocks C ab f atG td t s 3).N=0 := by
      simp [Block.N,hv,hu,hd0,negativePart]
    rw [hP,hN,hd0,block_right,positive_zero]
    simp [SoleNegativeTDSupport.increment]
  · have heh := Bool.eq_false_of_not_eq_true hde
    have hAb := EH_A_bounds heh ht
    by_cases hsign : 0≤ordinaryDE C (deOwner f)
    · have hd' : ordinaryDE C (deOwner f)∈Icc 0 frameCap :=
        ⟨hsign,by simpa [abs_of_nonneg hsign] using hd⟩
      have hP : (blocks C ab f atG td t s 3).P=ordinaryDE C (deOwner f) := by
        simp [Block.P,hv,hu,positivePart,max_eq_left hsign]
      have hN : (blocks C ab f atG td t s 3).N=0 := by
        simp [Block.N,hv,hu,negativePart,
          max_eq_right (show -ordinaryDE C (deOwner f)≤0 by linarith)]
      rw [hP,hN,block_right]
      simp only [SoleNegativeTOrdinaryData.positive,↓reduceIte,heh,Bool.false_eq_true]
      split_ifs with hdiag
      · exact SoleNegativeTDSupport.positive_diagonal_lower hQL hQU (by linarith) hdiag hd'
      · exact SoleNegativeTDSupport.positive_full_lower hq0 (by linarith)
          (lt_of_not_ge hdiag) (by linarith) hd'
    · have hsign' : ordinaryDE C (deOwner f)≤0 := (lt_of_not_ge hsign).le
      have hd' : -ordinaryDE C (deOwner f)∈Icc 0 frameCap :=
        ⟨by linarith,by simpa [abs_of_nonpos hsign'] using hd⟩
      have hP : (blocks C ab f atG td t s 3).P=0 := by
        simp [Block.P,hv,hu,positivePart,max_eq_right hsign']
      have hN : (blocks C ab f atG td t s 3).N= -ordinaryDE C (deOwner f) := by
        simp [Block.N,hv,hu,negativePart,
          max_eq_left (show 0≤-ordinaryDE C (deOwner f) by linarith)]
      have hh := SoleNegativeTDSupport.negative_min hQL hp hcoeff.2.2.1 hcg hpc
        hcoeff.1 hcoeff.2.1 hAb.1 hAb.2 hd'
      rw [hP,hN,block_left atG td (Real.sqrt q) ht]
      simp only [negative,↓reduceIte,heh,Bool.false_eq_true]
      rw [old_D,old_A]
      simpa only [neg_neg] using hh

theorem block_minorant {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s : ℝ}
    (hQL : qLow≤q) (hQU : q≤qCap) (ht : t∈domain f) (hs : s∈shortDomain td)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hflat : td=false → delta C.theta T=0)
    (hP : (∑i,(blocks C ab f atG td t s i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab f atG td t s i).N)=t-s+∑i,(blocks C ab f atG td t s i).P)
    (i : Fin 4) :
    block f atG td (Real.sqrt q) t s (blocks C ab f atG td t s i).P
      (blocks C ab f atG td t s i).N i≤contribution C ab f atG td q t s i := by
  by_cases hD : i=3
  · subst i
    exact D_minorant atG td hQL hQU ht hs ha hflat
  have hb := individual_budgets (angle ht).1 (short_small hs).1 hP hN i
  by_cases hB : i=2 ∧ td=false
  · rcases hB with ⟨rfl,rfl⟩
    have hs' : s∈Icc 0 (9/100:ℝ) := by simpa [shortDomain] using hs
    have hpair := changed_B_domain atG ht hs'
    have hv := single_data ab f atG false t s hflat 2 (by simp [single])
    have hraw := SoleOriginalBlocks.one_angle_minorant (blocks C ab f atG false t s 2)
      (Real.sqrt q) hv (angles_small ab f atG false t s ha 2).1
    have hneg := changed_B_negative atG (Real.sqrt_nonneg q) ht hs'
      (show (blocks C ab f atG false t s 2).N∈Icc 0 frameCap from
        ⟨(blocks C ab f atG false t s 2).N_nonneg,hb.2⟩)
    have hpairdata : (blocks C ab f atG false t s 2).p=ell f t 0 ∧
        (blocks C ab f atG false t s 2).q=c f t 0/Real.cos s ∧
        (blocks C ab f atG false t s 2).alpha=ell f t 0 := by
      simp [blocks,SoleEStress.blocks,Block.p,Block.q,SoleNegativeTSplit.btWeight,
        min_eq_left hpair.2.1,max_eq_right hpair.2.1]
    rw [hpairdata.1,hpairdata.2.1,hpairdata.2.2] at hraw
    simp only [F,↓reduceIte] at hraw
    have hc2 : contribution C ab f atG false q t s 2=
        (blocks C ab f atG false t s 2).increment (Real.sqrt q) := by
      simp [contribution]
    have hblock : block f atG false (Real.sqrt q) t s (blocks C ab f atG false t s 2).P
        (blocks C ab f atG false t s 2).N 2=
        U (Real.sqrt q) (ell f t 0) (c f t 0/Real.cos s) (blocks C ab f atG false t s 2).P+
          oldV f atG (Real.sqrt q) t (blocks C ab f atG false t s 2).N 2 := by
      simp [block,single,SoleNegativeTOrdinaryData.positive,negative]
    rw [hc2,hblock]
    linarith
  · obtain ⟨hp,hq⟩ := unchanged_coefficients C ab f atG td t s i hD hB
    have hci : contribution C ab f atG td q t s i=
        (blocks C ab f atG td t s i).increment (Real.sqrt q) := by
      simp [contribution,hD]
    rw [hci]
    cases hi : single f td i
    · have hh := (blocks C ab f atG td t s i).minorant (Real.sqrt q)
        (by rw [hp]; exact (SoleNegativeTCoefficients.positive atG ht i).2.2.le) hb.1 hb.2
      simpa only [block,hi,Bool.false_eq_true,↓reduceIte,hp,hq] using hh
    · have hv := single_data ab f atG td t s hflat i hi
      have hnu := unchanged_nu C ab f atG td t s i hD hB hi
      have hh := SoleOriginalBlocks.one_angle_minorant (blocks C ab f atG td t s i)
        (Real.sqrt q) hv (angles_small ab f atG td t s ha i).1
      have hpos : positive f atG td (Real.sqrt q) t s (blocks C ab f atG td t s i).P i=
          U (Real.sqrt q) (small f atG t i) (large f atG t i)
            (blocks C ab f atG td t s i).P := by
        simp [SoleNegativeTOrdinaryData.positive,hD,hB]
      have hnegv : negative f atG (Real.sqrt q) t (blocks C ab f atG td t s i).N i=
          oldV f atG (Real.sqrt q) t (blocks C ab f atG td t s i).N i := by
        simp [negative,hD]
      simp only [block,hi,↓reduceIte,hpos,hnegv]
      simpa only [F,↓reduceIte,hp,hq,hnu,oldV] using hh

theorem negative_original {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s L : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qCap)
    (ht : t∈domain f) (hs : s∈shortDomain td) (hst : s≤t)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hflat : td=false → delta C.theta T=0)
    (hvar : positiveVariation C.theta≤frameCap) (hG : 0≤delta C.theta G)
    (hE : 0≤ePrimary C f) (hsource : tPrimary C td= -s)
    (htotal : delta C.theta G+ePrimary C f=t)
    (hpure : ∀ i,Used f i → L≤oldV f atG (Real.sqrt q) t (t-s) i) :
    L≤ordinary C ab f atG td q t s := by
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab f atG td hvar hG hE (short_small hs).1 hsource htotal
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hsquare := Real.sq_sqrt hq0
  have he := SoleNegativeTEnvelope.negative_balance atG td
    (fun i => (blocks C ab f atG td t s i).P) (fun i => (blocks C ab f atG td t s i).N)
    (Real.sqrt_nonneg q) (by simpa only [hsquare] using hQL)
    (by simpa only [hsquare] using hQU) ht hs hst
    (fun i => (blocks C ab f atG td t s i).P_nonneg)
    (fun i => (blocks C ab f atG td t s i).N_nonneg) hP hN
    (single_parts ab f atG td t s hflat) hpure
  exact he.trans (Finset.sum_le_sum fun i _ => block_minorant atG td hQL hQU ht hs ha hflat hP hN i)

theorem positive_original {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qCap)
    (ht : t∈domain f) (hs : s∈shortDomain td) (hts : t≤ s)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hflat : td=false → delta C.theta T=0)
    (hvar : positiveVariation C.theta≤frameCap) (hG : 0≤delta C.theta G)
    (hE : 0≤ePrimary C f) (hsource : tPrimary C td= -s)
    (htotal : delta C.theta G+ePrimary C f=t) :
    -gamma f*(s-t)≤ordinary C ab f atG td q t s := by
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab f atG td hvar hG hE (short_small hs).1 hsource htotal
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hsquare := Real.sq_sqrt hq0
  have he := SoleNegativeTEnvelope.positive_balance atG td
    (fun i => (blocks C ab f atG td t s i).P) (fun i => (blocks C ab f atG td t s i).N)
    (Real.sqrt_nonneg q) (by simpa only [hsquare] using hQL)
    (by simpa only [hsquare] using hQU) ht hs hts
    (fun i => (blocks C ab f atG td t s i).P_nonneg)
    (fun i => (blocks C ab f atG td t s i).N_nonneg) hP hN
    (single_parts ab f atG td t s hflat)
  exact he.trans (Finset.sum_le_sum fun i _ => block_minorant atG td hQL hQU ht hs ha hflat hP hN i)

end SquaresInCircles.Eight.SoleNegativeTOriginalBlocks
end
end
end

section
/-!
## Continuous negative-primary interpolation from the 34 endpoint scalars

The actual BT secant is bounded on its original .09
interval before this scalar argument is used. Only the scalar gain
1.05 c s is extended to .3. The interpolation includes s=t and all
coefficient-family junctions, and uses only the three active DE indices.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleNegativeTContinuation
open SoleTScalarModel SoleNegativeTCoefficients SoleNegativeTOrdinaryData
open PositiveAngularEnvelope SingleAngleConcavity

def baseline (f : Family) (atG : Bool) (q t : ℝ) : ℝ :=
  SolePositiveTOrdinaryData.baseline (face f atG) (Real.sqrt q) (Real.sqrt (q-1/4)) t 0

def correction (f : Family) (atG : Bool) (t : ℝ) : ℝ :=
  if f=.ehMiddle ∨ f=.ehHigh then (8/25)*(c f t 0-p (face f atG) t 0)^2 else 0

def interpolation (f : Family) (atG : Bool) (q t : ℝ) (i : Fin 4) (s : ℝ) : ℝ :=
  baseline f atG q t+correction f atG t+(21/20)*c f t 0*s+
    oldV f atG (Real.sqrt q) t (t-s) i

theorem correction_nonneg (f : Family) (atG : Bool) (t : ℝ) : 0≤correction f atG t := by
  unfold correction
  split_ifs <;> positivity

theorem old_nu_scalar_upper {f : Family} (atG : Bool) {t : ℝ}
    (ht : t∈domain f) (i : Fin 4) :
    SoleNegativeTCoefficients.nu f atG t i≤SoleTScalarModel.nu {face f atG with negative:=i} t 0 := by
  have hD := SolePositiveTCoefficients.D_upper (face f atG) ht (zero_mem ht)
  have hD' : max (p (face f atG) t 0) (c f t 0)≤1131/1000 := hD
  fin_cases i
  · show (if isDE f then lambda f else n (face f atG) t 0)≤
      (if isDE f then 5/4 else n (face f atG) t 0)
    cases hde : isDE f <;> simp [lambda,hde]
  · exact le_refl _
  · show c f t 0 ≤ m {face f atG with negative:=2} t 0
    simp [m,face]
  · exact hD'

theorem zero_positive {f : Family} (atG : Bool) {q t : ℝ}
    (hq : q≤qTrial) (ht : t∈domain f) (i : Fin 4) :
    0< interpolation f atG q t i 0 := by
  have hs := SolePositiveTScalar.actual_radius_positive {face f atG with negative:=i}
    hq ht (zero_mem ht)
  have hid := SolePositiveTOrdinaryData.scalar_identity (face f atG)
    (Real.sqrt q) (Real.sqrt (q-1/4)) t 0 i
  have hcoef := mul_le_mul_of_nonpos_right (old_nu_scalar_upper atG ht i)
    (show Real.cos t-1≤0 by linarith [Real.cos_le_one t])
  have hJ := correction_nonneg f atG t
  rw [hid] at hs
  have hs' : (1/10000:ℝ)<baseline f atG q t+
      Vnu (Real.sqrt q) (small f atG t i) (large f atG t i)
        (SoleTScalarModel.nu {face f atG with negative:=i} t 0) t := hs
  have hg : interpolation f atG q t i 0=baseline f atG q t+correction f atG t+
      Vnu (Real.sqrt q) (small f atG t i) (large f atG t i)
        (SoleNegativeTCoefficients.nu f atG t i) t := by
    simp only [interpolation,oldV,sub_zero,mul_zero,add_zero]
  rw [hg]
  simp only [Vnu] at hs' ⊢
  linarith

theorem diagonal_positive {f : Family} (atG : Bool) {q t : ℝ}
    (hq : q≤qTrial) (ht : t∈domain f) (ht3 : t≤3/10) :
    0<baseline f atG q t+correction f atG t+(21/20)*c f t 0*t := by
  cases f with
  | ehLow =>
      have hh := SoleNegativeTScalar.actual_radius_positive
        ⟨.ehLowDiagonal,atG⟩ hq (by simpa [SoleNegativeTScalarModel.domain,
          SoleNegativeTScalarModel.left,SoleNegativeTScalarModel.right,domain,left,right] using ht)
      rw [SoleNegativeTScalarModel.scalar_identity] at hh
      simpa [baseline,correction,SoleNegativeTScalarModel.correction,
        SoleNegativeTScalarModel.scalar,SoleNegativeTScalarModel.family,
        SoleNegativeTScalarModel.angle,SoleNegativeTScalarModel.removed,
        SoleNegativeTScalarModel.shifted,SoleNegativeTScalarModel.index,face] using hh
  | ehMiddle =>
      have hdom : t∈SoleNegativeTScalarModel.domain .ehMiddleDiagonal := by
        norm_num [SoleNegativeTScalarModel.domain,SoleNegativeTScalarModel.left,
          SoleNegativeTScalarModel.right,domain,left,right] at ht ⊢
        exact ⟨ht.1,ht3⟩
      have hh := SoleNegativeTScalar.actual_radius_positive ⟨.ehMiddleDiagonal,atG⟩ hq hdom
      rw [SoleNegativeTScalarModel.scalar_identity] at hh
      simpa [baseline,correction,SoleNegativeTScalarModel.correction,
        SoleNegativeTScalarModel.scalar,SoleNegativeTScalarModel.family,
        SoleNegativeTScalarModel.angle,SoleNegativeTScalarModel.removed,
        SoleNegativeTScalarModel.shifted,SoleNegativeTScalarModel.index,face] using hh
  | ehHigh => norm_num [domain,left,right] at ht; linarith [ht.1]
  | deLow =>
      have hdom : t∈SoleNegativeTScalarModel.domain .deLowDiagonal := by
        norm_num [SoleNegativeTScalarModel.domain,SoleNegativeTScalarModel.left,
          SoleNegativeTScalarModel.right,domain,left,right] at ht ⊢
        exact ⟨ht.1,ht3⟩
      have hh := SoleNegativeTScalar.actual_radius_positive ⟨.deLowDiagonal,atG⟩ hq hdom
      rw [SoleNegativeTScalarModel.scalar_identity] at hh
      simpa [baseline,correction,SoleNegativeTScalarModel.correction,
        SoleNegativeTScalarModel.scalar,SoleNegativeTScalarModel.family,
        SoleNegativeTScalarModel.angle,SoleNegativeTScalarModel.removed,
        SoleNegativeTScalarModel.shifted,SoleNegativeTScalarModel.index,face] using hh
  | deHigh => norm_num [domain,left,right] at ht; linarith [ht.1]

theorem shifted_positive {f : Family} (atG : Bool) {q t : ℝ}
    (hq : q≤qTrial) (ht : t∈domain f) (ht3 : 3/10≤t) (i : Fin 4) (hi : Used f i) :
    0< interpolation f atG q t i (3/10) := by
  have hmatch {r : SoleNegativeTScalarModel.Row}
      (hf : SoleNegativeTScalarModel.family r=f) (hr : SoleNegativeTScalarModel.shifted r=true)
      (hindex : SoleNegativeTScalarModel.index r=i)
      (hdom : t∈SoleNegativeTScalarModel.domain r)
      (hcoef : SoleNegativeTScalarModel.coefficient ⟨r,atG⟩ t=
        SoleNegativeTCoefficients.nu f atG t i) :
      0< interpolation f atG q t i (3/10) := by
    have hh := SoleNegativeTScalar.actual_radius_positive ⟨r,atG⟩ hq hdom
    rw [SoleNegativeTScalarModel.scalar_identity,hcoef] at hh
    have hrem : SoleNegativeTScalarModel.removed r t=3/10 := by
      simp [SoleNegativeTScalarModel.removed,hr]
    have hang : SoleNegativeTScalarModel.angle r t=t-3/10 := by
      simp [SoleNegativeTScalarModel.angle,hr]
    rw [hrem,hang] at hh
    subst hf hindex
    exact hh
  cases f with
  | ehLow => norm_num [domain,left,right] at ht; linarith [ht.2]
  | ehMiddle =>
      apply hmatch (r:=.ehMiddleShifted i) rfl rfl rfl
      · norm_num [SoleNegativeTScalarModel.domain,SoleNegativeTScalarModel.left,
          SoleNegativeTScalarModel.right,domain,left,right] at ht ⊢
        exact ⟨ht3,ht.2⟩
      · have hp := (correction_domain atG ht (Or.inl rfl)).1
        fin_cases i <;> simp [SoleNegativeTScalarModel.coefficient,SoleNegativeTScalarModel.scalar,
          SoleNegativeTScalarModel.index,SoleNegativeTScalarModel.family,
          SoleNegativeTCoefficients.nu,SoleTScalarModel.nu,face,isDE,m]
        exact hp
  | ehHigh =>
      apply hmatch (r:=.ehHighShifted i) rfl rfl rfl
      · simpa [SoleNegativeTScalarModel.domain,SoleNegativeTScalarModel.left,
          SoleNegativeTScalarModel.right,domain,left,right] using ht
      · have hp := (correction_domain atG ht (Or.inr rfl)).1
        fin_cases i <;> simp [SoleNegativeTScalarModel.coefficient,SoleNegativeTScalarModel.scalar,
          SoleNegativeTScalarModel.index,SoleNegativeTScalarModel.family,
          SoleNegativeTCoefficients.nu,SoleTScalarModel.nu,face,isDE,m]
        exact hp
  | deLow =>
      have hne : i≠3 := by simpa [Used,isDE] using hi
      have hi3 : i.val<3 := by have := i.isLt; omega
      have hj : SoleNegativeTScalarModel.index (.deLowShifted ⟨i.val,hi3⟩)=i := by
        apply Fin.ext; rfl
      apply hmatch (r:=.deLowShifted ⟨i.val,hi3⟩) rfl rfl hj
      · norm_num [SoleNegativeTScalarModel.domain,SoleNegativeTScalarModel.left,
          SoleNegativeTScalarModel.right,domain,left,right] at ht ⊢
        exact ⟨ht3,ht.2⟩
      · simp only [SoleNegativeTScalarModel.coefficient,hj,hne,↓reduceIte]
        fin_cases i <;> simp_all [SoleNegativeTScalarModel.scalar,SoleNegativeTScalarModel.family,
          SoleTScalarModel.nu,SoleNegativeTCoefficients.nu,face,lambda,isDE,m]
  | deHigh =>
      have hne : i≠3 := by simpa [Used,isDE] using hi
      have hi3 : i.val<3 := by have := i.isLt; omega
      have hj : SoleNegativeTScalarModel.index (.deHighShifted ⟨i.val,hi3⟩)=i := by
        apply Fin.ext; rfl
      apply hmatch (r:=.deHighShifted ⟨i.val,hi3⟩) rfl rfl hj
      · simpa [SoleNegativeTScalarModel.domain,SoleNegativeTScalarModel.left,
          SoleNegativeTScalarModel.right,domain,left,right] using ht
      · simp only [SoleNegativeTScalarModel.coefficient,hj,hne,↓reduceIte]
        fin_cases i <;> simp_all [SoleNegativeTScalarModel.scalar,SoleNegativeTScalarModel.family,
          SoleTScalarModel.nu,SoleNegativeTCoefficients.nu,face,lambda,isDE,m]

theorem interpolation_concave {f : Family} (atG : Bool) {q t : ℝ}
    (hQL : qLow≤q) (hQU : q≤qCap) (ht : t∈domain f) (i : Fin 4) :
    ConcaveOn ℝ (Icc 0 (min t (3/10))) (interpolation f atG q t i) := by
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hq2 : (Real.sqrt q)^2≤qCap := by rw [Real.sq_sqrt hq0]; exact hQU
  have hc := SoleNegativeTGrowth.old_concave atG (Real.sqrt_nonneg q) hq2 ht i
  have hdom (a : ℝ) (ha : a∈Icc 0 (min t (3/10))) : t-a∈Icc 0 frameCap :=
    ⟨by linarith [ha.2.trans (min_le_left _ _)],by linarith [(angle ht).2,ha.1]⟩
  refine ⟨convex_Icc _ _,?_⟩
  intro a ha b hb u v hu hv huv
  have hh := hc.2 (hdom a ha) (hdom b hb) hu hv huv
  simp only [smul_eq_mul] at hh ⊢
  have he : t-(u*a+v*b)=u*(t-a)+v*(t-b) := by linear_combination (-t)*huv
  have h2 : u*(baseline f atG q t+correction f atG t)+v*(baseline f atG q t+correction f atG t)=
      baseline f atG q t+correction f atG t := by
    rw [← add_mul,huv,one_mul]
  simp only [interpolation]
  rw [he]
  linarith

theorem negative_positive {f : Family} (atG : Bool) {q t s : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (ht : t∈domain f)
    (hs : s∈Icc 0 (3/10:ℝ)) (hst : s≤t) (i : Fin 4) (hi : Used f i) :
    0< interpolation f atG q t i s := by
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  have hconc := interpolation_concave atG hQL hcap ht i
  have h0 := zero_positive atG hQU ht i
  have hend : 0< interpolation f atG q t i (min t (3/10)) := by
    rcases le_total t (3/10:ℝ) with ht3 | ht3
    · rw [min_eq_left ht3]
      simpa [interpolation,SoleNegativeTGrowth.zero] using diagonal_positive atG hQU ht ht3
    · rw [min_eq_right ht3]
      exact shifted_positive atG hQU ht ht3 i hi
  have hlen : 0≤ min t (3/10:ℝ) := le_min (angle ht).1 (by norm_num)
  have hh := hconc.min_le_of_mem_Icc (left_mem_Icc.mpr hlen) (right_mem_Icc.mpr hlen)
    (show s∈Icc 0 (min t (3/10)) from ⟨hs.1,le_min hst hs.2⟩)
  exact (lt_min h0 hend).trans_le hh

theorem positive_surplus_positive {f : Family} (atG : Bool) {q t s : ℝ}
    (hQU : q≤qTrial) (ht : t∈domain f) (hs : s∈Icc 0 (3/10:ℝ)) (hts : t≤ s) :
    0<baseline f atG q t+correction f atG t+(21/20)*c f t 0*s-gamma f*(s-t) := by
  have hd := diagonal_positive atG hQU ht (hts.trans hs.2)
  have hg := gain_exceeds_cost ht
  have hh := mul_nonneg (sub_nonneg.mpr hg.le) (sub_nonneg.mpr hts)
  nlinarith

end SquaresInCircles.Eight.SoleNegativeTContinuation
end
end
end

section
/-!
## Negative-T endpoint supports on the cycle

The flat coordinate of T is the one captured from the negative primary. H, A, B use their circle
supports and D the sorted support at the same `q` (`circle_supports`, `D_force`). The reserve of the
sorted baseline enters only after the split of G and E at fixed coordinates has reached an
endpoint (`decomposition`, `value_lower`), and the endpoint scalars are positive
(`endpoint_positive`); no packing is claimed at an auxiliary scalar endpoint.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleNegativeTEndpoint
open Candidate SignedStress SecondaryEStress SoleResiduals
open SoleTScalarModel SolePositiveTSplitModel SoleNegativeTCoefficients
open SoleNegativeTOrdinaryData SoleNegativeTOriginalBlocks
open ActualCoreEBlocks ActualOrdinaryBlocks PositiveAngularEnvelope

def faceForces (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ) :
    Vertex → Point :=
  SoleEStress.forces C ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f)
    (n (face f atG) t 0) (k f t 0) (ell f t 0)
    (SoleNegativeTSplit.btWeight f td t s) (SoleNegativeTSplit.tdWeight f td t s)
    (p (face f atG) t 0) (lambda f)

def blockSupport (B : Block) (R : ℝ) : ℝ :=
  R*pairNorm B.alpha B.beta (B.u+B.v)-(B.alpha*PositiveAngularEnvelope.phi B.u+B.beta*PositiveAngularEnvelope.phi B.v)/2

def anchorSupport (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool) (q t s : ℝ) : ℝ :=
  blockSupport (blocks C ab f atG td t s 0) (Real.sqrt q)+
  blockSupport (blocks C ab f atG td t s 1) (Real.sqrt q)+
  blockSupport (blocks C ab f atG td t s 2) (Real.sqrt q)+
  ActualSortedSupport.support q
    (p (face f atG) t 0*Real.cos (ordinaryDE C (deOwner f)))
    (dCoefficient f td t s+p (face f atG) t 0*Real.sin (ordinaryDE C (deOwner f)))

def correction (f : Family) (atG : Bool) (q t : ℝ) : ℝ :=
  ActualSortedSupport.full q (p (face f atG) t 0) (c f t 0)-
    ActualSortedSupport.support q (p (face f atG) t 0) (c f t 0)

def gain (f : Family) (atG td : Bool) (q t s : ℝ) : ℝ :=
  if td then c f t 0*((1/Real.cos s-1)/2+(13/12)*Real.tan s)-
    ActualSortedSupport.support q (p (face f atG) t 0) (c f t 0/Real.cos s)+
    ActualSortedSupport.support q (p (face f atG) t 0) (c f t 0)
  else FlatTStress.secantCharge (Real.sqrt q) (c f t 0) (ell f t 0) s

theorem face_forces_eq (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ) :
    SoleNegativeTSplit.forceData C ab f td t s (x (face f atG) t 0) (SoleTScalarModel.e (face f atG) t 0)=
      faceForces C ab f atG td t s := rfl

theorem circle_supports {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (C : SignedCycle) (f : Family) (atG td : Bool) (R t s : ℝ) :
    signedSupport R 1 (faceForces C ab f atG td t s H)=
      blockSupport (blocks C ab f atG td t s 0) R ∧
    signedSupport R 1 (faceForces C ab f atG td t s A)=
      blockSupport (blocks C ab f atG td t s 1) R ∧
    signedSupport R (-1) (faceForces C ab f atG td t s B)=
      blockSupport (blocks C ab f atG td t s 2) R := by
  refine ⟨?_,?_,?_⟩
  · rw [faceForces,SoleEStress.force_H (SolePositiveTSplitSupport.ehOwner_cases f),
      rotatedPair_signedSupport]
    simp [blockSupport,SoleNegativeTOriginalBlocks.blocks,SoleEStress.blocks,pairNorm_symm]
    ring
  · rw [faceForces,SoleEStress.force_A hab,rotatedPair_signedSupport]
    simp [blockSupport,SoleNegativeTOriginalBlocks.blocks,SoleEStress.blocks,pairNorm_symm]
    ring
  · rw [faceForces,SoleEStress.force_B hab (SolePositiveTOriginalBlocks.btOwner_cases td)]
    simp only []
    rw [reflected_rotatedPair_signedSupport]
    simp [blockSupport,SoleNegativeTOriginalBlocks.blocks,SoleEStress.blocks,pairNorm_symm]
    ring

theorem D_force {C : SignedCycle} (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ)
    (hflat : td=false → delta C.theta T=0) :
    faceForces C ab f atG td t s D=
      (p (face f atG) t 0*Real.cos (ordinaryDE C (deOwner f)),
        -(dCoefficient f td t s+p (face f atG) t 0*Real.sin (ordinaryDE C (deOwner f)))) := by
  rw [faceForces,SoleEStress.force_D (SolePositiveTOriginalBlocks.tdOwner_cases td)
    (SolePositiveTSplitSupport.deOwner_cases f)]
  cases td <;> simp_all [tdOwner,rotatedPair,dCoefficient] <;> ring

theorem T_work {C : SignedCycle} (ab : Fin 4) (f : Family) (atG td : Bool) {t s : ℝ}
    (hs : s∈Icc 0 frameCap) (hsource : tPrimary C td= -s) (hcore : (C.point T).a=7/12) :
    work (faceForces C ab f atG td t s T) (C.point T)= -(7/12)*c f t 0*Real.tan s := by
  have hcos : Real.cos s≠0 := ne_of_gt (by linarith [(transport_trig hs).1])
  rw [faceForces,SoleEStress.force_T]
  cases td
  · exact negative_BT_work hcos (by simpa [tPrimary] using hsource) hcore
  · exact negative_TD_work hcos (by simpa [tPrimary] using hsource) hcore

theorem fixedWork_le {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (ht : t∈domain f) (hs : s∈shortDomain td)
    (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hsource : tPrimary C td= -s) (hcore : (C.point T).a=7/12)
    (hflat : td=false → delta C.theta T=0) :
    SoleNegativeTSplit.fixedWork C ab f td t s (x (face f atG) t 0) (SoleTScalarModel.e (face f atG) t 0)≤
      anchorSupport C ab f atG td q t s-(7/12)*c f t 0*Real.tan s := by
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by
    simpa [Real.sq_sqrt hq0] using hC.contained
  have hH : work (faceForces C ab f atG td t s H) (C.point H)≤
      signedSupport (Real.sqrt q) 1 (faceForces C ab f atG td t s H) :=
    work_le_signed_support (Real.sqrt_nonneg q) (hc H) (Or.inl rfl)
      (by simp [abs_of_nonneg hn.H_nonneg]) (faceForces C ab f atG td t s H)
  have hA : work (faceForces C ab f atG td t s A) (C.point A)≤
      signedSupport (Real.sqrt q) 1 (faceForces C ab f atG td t s A) :=
    work_le_signed_support (Real.sqrt_nonneg q) (hc A) (Or.inl rfl)
      (by simp [abs_of_nonneg hn.A_nonneg]) (faceForces C ab f atG td t s A)
  have hB : work (faceForces C ab f atG td t s B) (C.point B)≤
      signedSupport (Real.sqrt q) (-1) (faceForces C ab f atG td t s B) :=
    work_le_signed_support (Real.sqrt_nonneg q) (hc B) (Or.inr rfl)
      (by simp [abs_of_nonpos hn.B_nonpos]) (faceForces C ab f atG td t s B)
  obtain ⟨hHs,hAs,hBs⟩ := circle_supports hab C f atG td (Real.sqrt q) t s
  rw [hHs] at hH
  rw [hAs] at hA
  rw [hBs] at hB
  have hp := p_ge_one atG ht
  have hcg := d_coefficient_ge td ht hs
  have hpc := p_half_c atG ht
  have hsmall := (ordinary_small (de:=deOwner f) (eh:=ehOwner f)
    (fun i => hC.spread (next i) i)).1
  have hD := ActualSortedSupport.actual_negative_support hq0 (hC.sorted D) hn.D_nonpos
    (hC.contained D) (SoleNegativeTDSupport.force_sum_positive
      (show 0<p (face f atG) t 0 by linarith)
      (show p (face f atG) t 0/2≤dCoefficient f td t s by linarith) hsmall).le
  have hDw : work (faceForces C ab f atG td t s D) (C.point D)≤
      ActualSortedSupport.support q
        (p (face f atG) t 0*Real.cos (ordinaryDE C (deOwner f)))
        (dCoefficient f td t s+p (face f atG) t 0*Real.sin (ordinaryDE C (deOwner f))) := by
    rw [D_force ab f atG td t s hflat]
    simp only [work]
    linarith
  have hT := T_work (t := t) ab f atG td (short_small hs) hsource hcore
  simp only [SoleNegativeTSplit.fixedWork,face_forces_eq]
  dsimp only [anchorSupport]
  linarith

theorem secantCharge_eq {q c s : ℝ} (hc : 0<c) (hs : s∈Icc 0 frameCap) (a : ℝ) :
    FlatTStress.secantCharge (Real.sqrt q) c a s=c*GlobalGA.secantGain q (a/c) s := by
  have hcos : 0<Real.cos s := by linarith [(transport_trig hs).1]
  rw [GlobalGA.secantGain_eq_secant_expression q (a/c) hcos]
  have hN : pairNorm a (c/Real.cos s) 0=c*Real.sqrt ((1/Real.cos s)^2+(a/c)^2) := by
    simpa only [div_eq_mul_inv,one_mul,add_comm] using FlatTStress.zero_norm_scale hc a (1/Real.cos s)
  have hZ : pairNorm a c 0=c*Real.sqrt (1+(a/c)^2) := by
    simpa only [mul_one,one_pow,add_comm] using FlatTStress.zero_norm_scale hc a 1
  dsimp [FlatTStress.secantCharge]
  rw [hN,hZ]
  ring

theorem gain_strict {f : Family} (atG td : Bool) {q t s : ℝ}
    (hQL : qLow≤q) (hQU : q≤qCap) (ht : t∈domain f)
    (hs : s∈shortDomain td) (hs0 : 0<s) : (21/20)*c f t 0*s<gain f atG td q t s := by
  have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
  have hp := p_ge_one atG ht
  cases td
  · have hs' : s∈Ioc 0 (9/100:ℝ) := ⟨hs0,by simpa [shortDomain] using hs.2⟩
    have hr : 117/200≤ell f t 0/c f t 0 := (le_div_iff₀ hc).2 (B_ratio atG ht)
    have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
    have hh := mul_lt_mul_of_pos_left (SoleNegativeTGain.BT_strict hq0 hQU hr hs') hc
    simp only [gain,Bool.false_eq_true,↓reduceIte]
    rw [secantCharge_eq hc (short_small hs)]
    linarith
  · have hs' : s∈Ioc 0 (3/10:ℝ) := ⟨hs0,by simpa [shortDomain] using hs.2⟩
    simp only [gain,↓reduceIte]
    exact SoleNegativeTDSupport.TD_gain hQL hQU (by linarith) hc hs'

theorem correction_lower {f : Family} (atG : Bool) {q t : ℝ}
    (hQL : qLow≤q) (hQU : q≤qCap) (ht : t∈domain f) :
    SoleNegativeTContinuation.correction f atG t≤correction f atG q t := by
  have hp := p_ge_one atG ht
  have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
  by_cases hf : f=.ehMiddle ∨ f=.ehHigh
  · have hdom := correction_domain atG ht hf
    simpa only [SoleNegativeTContinuation.correction,ite_eq_left hf,correction] using
      SoleNegativeTDSupport.sorted_correction hQL hQU (by linarith) hc.le hdom.1 hdom.2
  · have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
    have hh := ActualSortedSupport.support_le_full hq0
      (show 0≤p (face f atG) t 0+c f t 0 by linarith)
    simp only [SoleNegativeTContinuation.correction,ite_eq_right hf,correction]
    linarith

private lemma r90_block (B : Block) (R : ℝ) (hu : |B.u|≤frameCap) (hv : |B.v|≤frameCap) :
    B.alpha*edgeWidth B.u+B.beta*edgeWidth B.v-blockSupport B R=
      B.increment R+3/2*(B.alpha+B.beta)-R*pairNorm B.alpha B.beta 0 := by
  rw [width_eq hu,width_eq hv]
  simp only [blockSupport,Block.increment]
  ring

private lemma r90_D (q p g d : ℝ) :
    p*edgeWidth d-ActualSortedSupport.support q (p*Real.cos d) (g+p*Real.sin d)=
      SoleNegativeTDSupport.increment q p g d+p-ActualSortedSupport.support q p g := by
  simp only [SoleNegativeTDSupport.increment]
  ring

private lemma r90_face_family (f : Family) (atG : Bool) : (face f atG).family=f := rfl
private lemma r90_face_td (f : Family) (atG : Bool) : (face f atG).td=true := rfl
private lemma r90_full (q f g : ℝ) :
    ActualSortedSupport.full q f g=Real.sqrt q*pairNorm f g 0-(f+g)/2 := by
  simp [ActualSortedSupport.full,pairNorm_zero]

/-- The decomposition identity after the three circle blocks and the D block have been
replaced by their increments. -/
private def r90_R0 (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool) (q M t s : ℝ) :
    Prop :=
  SoleNegativeTSplit.variableDemand C f td t s (x (face f atG) t 0) (SoleTScalarModel.e (face f atG) t 0)-
    ((blocks C ab f atG td t s 0).alpha*edgeWidth (blocks C ab f atG td t s 0).u+
      (blocks C ab f atG td t s 0).beta*edgeWidth (blocks C ab f atG td t s 0).v)-
    ((blocks C ab f atG td t s 1).alpha*edgeWidth (blocks C ab f atG td t s 1).u+
      (blocks C ab f atG td t s 1).beta*edgeWidth (blocks C ab f atG td t s 1).v)-
    ((blocks C ab f atG td t s 2).alpha*edgeWidth (blocks C ab f atG td t s 2).u+
      (blocks C ab f atG td t s 2).beta*edgeWidth (blocks C ab f atG td t s 2).v)-
    p (face f atG) t 0*edgeWidth (ordinaryDE C (deOwner f))+
    (3/2*((blocks C ab f atG td t s 0).alpha+(blocks C ab f atG td t s 0).beta)-
      Real.sqrt q*pairNorm (blocks C ab f atG td t s 0).alpha (blocks C ab f atG td t s 0).beta 0)+
    (3/2*((blocks C ab f atG td t s 1).alpha+(blocks C ab f atG td t s 1).beta)-
      Real.sqrt q*pairNorm (blocks C ab f atG td t s 1).alpha (blocks C ab f atG td t s 1).beta 0)+
    (3/2*((blocks C ab f atG td t s 2).alpha+(blocks C ab f atG td t s 2).beta)-
      Real.sqrt q*pairNorm (blocks C ab f atG td t s 2).alpha (blocks C ab f atG td t s 2).beta 0)+
    p (face f atG) t 0-ActualSortedSupport.support q (p (face f atG) t 0) (dCoefficient f td t s)+
    (7/12)*c f t 0*Real.tan s-
    k f t 0*sigma (Real.sqrt q) (g f t)*Real.sin (x (face f atG) t 0)-
    SolePositiveTEndpoint.eWork (face f atG) (Real.sqrt q) M t 0=
  SolePositiveTOrdinaryData.baseline (face f atG) (Real.sqrt q) (M+1/2) t 0+
    correction f atG q t+gain f atG td q t s

local macro "r90_unfold" : tactic => `(tactic|
  simp only [SoleNegativeTSplit.variableDemand,SoleNegativeTOriginalBlocks.blocks,SoleEStress.blocks,
    Matrix.cons_val,Fin.isValue,Fin.reduceEq,correction,gain,r90_full,FlatTStress.secantCharge,
    SolePositiveTOrdinaryData.baseline,SolePositiveTEndpoint.eWork,eTerm,
    SoleTScalarModel.primaryCoefficient,sigma,SoleEndpointSupport.highWork,
    SoleTScalarModel.first,SoleTScalarModel.second,Fin.sum_univ_four,
    btOwner,tdOwner,deOwner,ehOwner,SoleNegativeTSplit.btWeight,SoleNegativeTSplit.tdWeight,
    dCoefficient,ordinaryDE,ordinaryEH,nWeight,n,m,deWeight,ehWeight,p,lambda,tiltedE,isDE,
    r90_face_family,r90_face_td,edgeWidth_zero,↓reduceIte,Bool.false_eq_true,
    Real.cos_zero,Real.sin_zero,mul_zero,add_zero,mul_one,div_eq_mul_inv])

private lemma r90_R0_false {C : SignedCycle} {ab : Fin 4} {f : Family} (atG : Bool) (q M : ℝ)
    {t s : ℝ} (hab : ab=0 ∨ ab=2) (ht : t∈domain f) (hs : s∈shortDomain false)
    (hsource : tPrimary C false= -s) (hT : delta C.theta T=0) :
    r90_R0 C ab f atG false q M t s := by
  have hx := (split_angles (face f atG) ht (zero_mem ht)).2.1
  have he := (split_angles (face f atG) ht (zero_mem ht)).2.2
  have hWx := edgeWidth_positive_formula hx
  have hWe := edgeWidth_positive_formula he
  have hWs := edgeWidth_negative_formula (short_small hs)
  have hcos : Real.cos s≠0 := ne_of_gt (by linarith [(transport_trig (short_small hs)).1])
  have hδ : delta C.theta B= -s := by simpa [tPrimary] using hsource
  have hA : edgeWidth (if ab=0 then 0 else delta C.theta A)+
      edgeWidth (if ab=0 then delta C.theta A else 0)=edgeWidth (delta C.theta A)+1 := by
    rcases hab with rfl | rfl <;> simp [add_comm]
  have htan : Real.tan s=Real.sin s*(Real.cos s)⁻¹ := by
    rw [Real.tan_eq_sin_div_cos,div_eq_mul_inv]
  have hinv : Real.cos s*(Real.cos s)⁻¹=1 := mul_inv_cancel₀ hcos
  unfold r90_R0
  cases f <;> r90_unfold <;> simp only [hδ,hT,hWx,hWe,hWs,htan,edgeWidth_zero] <;>
    simp only [pairNorm_symm] <;>
    linear_combination (-(ell _ t 0))*hA+(c _ t 0*(1/2))*hinv

private lemma r90_R0_true {C : SignedCycle} {ab : Fin 4} {f : Family} (atG : Bool) (q M : ℝ)
    {t s : ℝ} (hab : ab=0 ∨ ab=2) (ht : t∈domain f) (hs : s∈shortDomain true)
    (hsource : tPrimary C true= -s) :
    r90_R0 C ab f atG true q M t s := by
  have hx := (split_angles (face f atG) ht (zero_mem ht)).2.1
  have he := (split_angles (face f atG) ht (zero_mem ht)).2.2
  have hWx := edgeWidth_positive_formula hx
  have hWe := edgeWidth_positive_formula he
  have hWs := edgeWidth_negative_formula (short_small hs)
  have hcos : Real.cos s≠0 := ne_of_gt (by linarith [(transport_trig (short_small hs)).1])
  have hδ : delta C.theta T= -s := by simpa [tPrimary] using hsource
  have hA : edgeWidth (if ab=0 then 0 else delta C.theta A)+
      edgeWidth (if ab=0 then delta C.theta A else 0)=edgeWidth (delta C.theta A)+1 := by
    rcases hab with rfl | rfl <;> simp [add_comm]
  have htan : Real.tan s=Real.sin s*(Real.cos s)⁻¹ := by
    rw [Real.tan_eq_sin_div_cos,div_eq_mul_inv]
  have hinv : Real.cos s*(Real.cos s)⁻¹=1 := mul_inv_cancel₀ hcos
  unfold r90_R0
  cases f <;> r90_unfold <;> simp only [hδ,hWx,hWe,hWs,htan] <;>
    simp only [pairNorm_symm] <;>
    linear_combination (-(ell _ t 0))*hA+(c _ t 0*(1/2))*hinv

theorem decomposition {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) (q M : ℝ)
    {t s : ℝ} (hab : ab=0 ∨ ab=2) (ht : t∈domain f) (hs : s∈shortDomain td)
    (hsource : tPrimary C td= -s) (hflat : td=false → delta C.theta T=0)
    (ha : ∀ i,|delta C.theta i|≤frameCap) :
    SoleNegativeTSplit.variableDemand C f td t s (x (face f atG) t 0) (SoleTScalarModel.e (face f atG) t 0)-
      anchorSupport C ab f atG td q t s+(7/12)*c f t 0*Real.tan s-
      k f t 0*sigma (Real.sqrt q) (g f t)*Real.sin (x (face f atG) t 0)-
      SolePositiveTEndpoint.eWork (face f atG) (Real.sqrt q) M t 0=
    SolePositiveTOrdinaryData.baseline (face f atG) (Real.sqrt q) (M+1/2) t 0+
      correction f atG q t+gain f atG td q t s+ordinary C ab f atG td q t s := by
  have hs0 := angles_small ab f atG td t s ha
  have hb0 := r90_block (blocks C ab f atG td t s 0) (Real.sqrt q) (hs0 0).1 (hs0 0).2
  have hb1 := r90_block (blocks C ab f atG td t s 1) (Real.sqrt q) (hs0 1).1 (hs0 1).2
  have hb2 := r90_block (blocks C ab f atG td t s 2) (Real.sqrt q) (hs0 2).1 (hs0 2).2
  have hD := r90_D q (p (face f atG) t 0) (dCoefficient f td t s) (ordinaryDE C (deOwner f))
  have hord : ordinary C ab f atG td q t s=
      (blocks C ab f atG td t s 0).increment (Real.sqrt q)+
      (blocks C ab f atG td t s 1).increment (Real.sqrt q)+
      (blocks C ab f atG td t s 2).increment (Real.sqrt q)+
      SoleNegativeTDSupport.increment q (p (face f atG) t 0) (dCoefficient f td t s)
        (ordinaryDE C (deOwner f)) := by
    simp only [ordinary,Fin.sum_univ_four,contribution,Fin.isValue,Fin.reduceEq,↓reduceIte]
  have hred : r90_R0 C ab f atG td q M t s := by
    cases td
    · exact r90_R0_false atG q M hab ht hs hsource (hflat rfl)
    · exact r90_R0_true atG q M hab ht hs hsource
  unfold r90_R0 at hred
  rw [hord]
  unfold anchorSupport
  linear_combination hb0+hb1+hb2+hD+hred

theorem value_lower {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (ht : t∈domain f) (hs : s∈shortDomain td)
    (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hsource : tPrimary C td= -s) (hcore : (C.point T).a=7/12)
    (hflat : td=false → delta C.theta T=0) :
    SoleNegativeTContinuation.baseline f atG q t+correction f atG q t+
      gain f atG td q t s+ordinary C ab f atG td q t s≤
      SoleNegativeTSplit.value C ab f td (Real.sqrt q) (axisCoordinate q) t s (x (face f atG) t 0) := by
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hx : x (face f atG) t 0∈Icc 0 t := by
    cases atG <;> simp [x,face] <;> exact (angle ht).1
  have he : t-x (face f atG) t 0=SoleTScalarModel.e (face f atG) t 0 := by
    cases atG <;> simp [x,SoleTScalarModel.e,face]
  have hwork := fixedWork_le atG td hab hQL ht hs hC hn hsource hcore hflat
  have hE := SolePositiveTEndpoint.E_support (face f atG) (Real.sqrt_nonneg q) ht (zero_mem ht)
    (hC.sorted E) (by simpa [Real.sq_sqrt hq0] using hC.contained E)
    (M:=axisCoordinate q)
  have hE' : eBound C f (Real.sqrt q) (axisCoordinate q) t (SoleTScalarModel.e (face f atG) t 0)≤
      SolePositiveTEndpoint.eWork (face f atG) (Real.sqrt q) (axisCoordinate q) t 0 := hE
  have hid := decomposition atG td q (axisCoordinate q) hab ht hs hsource hflat
    (fun i => hC.spread (next i) i)
  have haxis : axisCoordinate q+1/2=Real.sqrt (q-1/4) := by simp [axisCoordinate]
  rw [haxis] at hid
  rw [SoleNegativeTSplit.value_eq_stress td (Real.sqrt q) (axisCoordinate q) hab ht hx hn,he]
  dsimp only [SoleNegativeTSplit.stress,SoleNegativeTContinuation.baseline]
  linarith

theorem endpoint_positive {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qTrial)
    (ht : t∈domain f) (hs : s∈shortDomain td) (hs0 : 0<s)
    (hC : C.Necessary q) (hn : C.NormalAnchors) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤ePrimary C f)
    (hsource : tPrimary C td= -s) (htotal : delta C.theta G+ePrimary C f=t)
    (hcore : (C.point T).a=7/12) (hflat : td=false → delta C.theta T=0) :
    0<SoleNegativeTSplit.value C ab f td (Real.sqrt q) (axisCoordinate q) t s
      (x (face f atG) t 0) := by
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hs3 : s∈Icc 0 (3/10:ℝ) := by
    cases td <;> norm_num [shortDomain] at hs ⊢ <;> exact ⟨hs.1,by linarith [hs.2]⟩
  have hJ := correction_lower atG hQL hcap ht
  have hgain := gain_strict atG td hQL hcap ht hs hs0
  have hvalue := value_lower atG td hab hQL ht hs hC hn hsource hcore hflat
  rcases le_total s t with hst | hts
  · have hpure (i : Fin 4) (hi : Used f i) :
        -SoleNegativeTContinuation.baseline f atG q t-SoleNegativeTContinuation.correction f atG t-
          (21/20)*c f t 0*s≤oldV f atG (Real.sqrt q) t (t-s) i := by
      have hh := SoleNegativeTContinuation.negative_positive atG hQL hQU ht hs3 hst i hi
      dsimp [SoleNegativeTContinuation.interpolation] at hh
      linarith
    have hordinary := negative_original atG td hab hQL hcap ht hs hst ha hflat hvar hG hE hsource htotal hpure
    linarith
  · have hp := SoleNegativeTContinuation.positive_surplus_positive atG hQU ht hs3 hts
    have hordinary := positive_original atG td hab hQL hcap ht hs hts ha hflat hvar hG hE hsource htotal
    linarith

end SquaresInCircles.Eight.SoleNegativeTEndpoint
end
end
end

section
/-!
## Actual sole-E exclusions for both nonnegative T primary owners

This is the original-source join of the complete
scalar, ordinary-angle, and fixed-coordinate arguments. The selected
AB and T owners remain weak, including every zero-error tie. No G or T
tangent sign and no radial-kind premise is used. Sole EH permits either
E sign; sole DE retains exactly the nonpositive E sign its axis bound uses.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SolePositiveTExclusion
open Candidate SoleTScalarModel SolePositiveTSplitModel

def choose (de : Bool) (t : ℝ) : Family :=
  if de then if t≤7/20 then .deLow else .deHigh
  else if t≤1/5 then .ehLow else if t≤7/20 then .ehMiddle else .ehHigh

theorem choose_isDE (de : Bool) (t : ℝ) : isDE (choose de t)=de := by
  cases de <;> simp [choose] <;> split_ifs <;> rfl

theorem choose_mem (de : Bool) {t : ℝ} (ht : t∈Icc 0 frameCap) :
    t∈domain (choose de t) := by
  have h1 : 0 ≤ t := ht.1
  have h2 : t ≤ 7/10 := ht.2
  cases de <;> simp only [choose,Bool.false_eq_true,↓reduceIte] <;>
    split_ifs <;> norm_num [domain,left,right] <;> constructor <;> linarith

theorem original_false {C : SignedCycle} {ab : Fin 4} (de td : Bool) {q : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hE : 0≤ if de then delta C.theta D else delta C.theta E)
    (hT : 0≤tPrimary C td) (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td)
      (if de then 3 else 2) (if de then 0 else 1) i)) : False := by
  obtain ⟨z,hzd⟩ : ∃ z : ℝ,z=tPrimary C td := ⟨_,rfl⟩
  obtain ⟨t,htd⟩ : ∃ t : ℝ,t=delta C.theta G+(if de then delta C.theta D else delta C.theta E)+z :=
    ⟨_,rfl⟩
  obtain ⟨f,hfd⟩ : ∃ f : Family,f=choose de t := ⟨_,rfl⟩
  have hde : isDE f=de := by rw [hfd]; exact choose_isDE de t
  have hE' : 0 ≤ ePrimary C f := by simp only [ePrimary,hde]; exact hE
  have htotal : delta C.theta G+ePrimary C f+tPrimary C td=t := by
    rw [htd,hzd]
    simp only [ePrimary,hde]
  obtain ⟨ht0,hP,hN⟩ := SolePositiveTOriginalBlocks.original_budgets (s := ⟨f,td,false,0⟩)
    hab t z hvar hG hE' hT htotal
  have hP0 : 0 ≤ ∑i,(SolePositiveTOriginalBlocks.blocks C ab ⟨f,td,false,0⟩ t z i).P :=
    Finset.sum_nonneg (fun i _ =>
      (SolePositiveTOriginalBlocks.blocks C ab ⟨f,td,false,0⟩ t z i).P_nonneg)
  have htcap : t∈Icc 0 frameCap := ⟨ht0,by linarith⟩
  have ht : t∈domain f := hfd ▸ choose_mem de htcap
  have hEnn : 0 ≤ (if de then delta C.theta D else delta C.theta E) := hE
  have hz : z∈Icc 0 t := ⟨hzd ▸ hT,by rw [htd]; linarith⟩
  have hx : delta C.theta G∈Icc 0 (t-z) := ⟨hG,by rw [htd]; linarith⟩
  have hq0 : 0 ≤ q := by norm_num [qLow] at hQL; linarith
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt hq0
  have hcap : q ≤ qCap := hQU.trans uniform_radius_order.2.2.1.le
  have hRsq : (Real.sqrt q)^2 ≤ qCap := by rw [hR2]; exact hcap
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by rw [hR2]; exact hC.contained
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => (hC.contained i).trans hcap
  have ha : ∀ i,|delta C.theta i| ≤ frameCap := fun i => hC.spread (next i) i
  have hM : axisCoordinate q ≤ 283/200 := by
    have hm := Real.sqrt_le_sqrt (sub_le_sub_right hQU (1/4))
    have hu := SoleTScalarModel.axis_upper
    have hv : ((SoleTScalarModel.axisUpper:ℚ):ℝ)=1914558470771/1000000000000 := by
      norm_num [SoleTScalarModel.axisUpper]
    unfold axisCoordinate
    linarith
  have hconc := SolePositiveTSplitModel.concave ab td hR hRsq hM ht hz hC.sorted hcCap ha
  have h0 : 0 < SolePositiveTSplitModel.value C ab f td (Real.sqrt q) (axisCoordinate q) t z 0 := by
    have hh := SolePositiveTEndpoint.endpoint_positive (C:=C) (ab:=ab) ⟨f,td,false,0⟩
      hab hQL hQU ht hz hzd hC hn hvar hG hE' hT htotal
    simpa only [x,Bool.false_eq_true,↓reduceIte] using hh
  have h1 : 0 < SolePositiveTSplitModel.value C ab f td (Real.sqrt q) (axisCoordinate q) t z
      (t-z) := by
    have hh := SolePositiveTEndpoint.endpoint_positive (C:=C) (ab:=ab) ⟨f,td,true,0⟩
      hab hQL hQU ht hz hzd hC hn hvar hG hE' hT htotal
    simpa only [x,↓reduceIte] using hh
  have hpos := SolePositiveTSplitModel.positive_of_endpoints hconc hx h0 h1
  have hnec := SolePositiveTSplitSupport.necessary td hab hR ht hz hG hE'
    (by rw [hzd]; exact htotal) hC.sorted hc hn
    (SoleEndpointSupport.primary_le_axis hQL (hC.sorted E) (hC.contained E))
    (by intro h; apply hsign; rw [← hde]; exact h)
    (by simpa only [deOwner,ehOwner,hde] using hf)
  exact (not_lt_of_ge hnec) hpos

end SquaresInCircles.Eight.SolePositiveTExclusion
end
end
end

section
/-!
## No negative T primary in the sole-E families

A feasible secondary of T is selected on the same cycle (`reselect_TD`, `reselect_BT`); otherwise
the boundary condition gives the short flat primary of T used in the stress argument
(`original_flat_false`). No sign of the tangents of G and T is assumed and no point moves. The
sole-EH family allows either sign of E, and sole-DE keeps its hypothesis of a nonpositive E
(`all_TD_false`, `all_BT_false`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleNegativeTExclusion
open Candidate SoleTScalarModel SolePositiveTSplitModel
open SoleNegativeTCoefficients SoleNegativeTOrdinaryData
open NegativeSecondaryEExclusion

theorem original_flat_false {C : SignedCycle} {ab : Fin 4} (de td : Bool) {q s : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hE : 0≤ if de then delta C.theta D else delta C.theta E)
    (hs : s∈shortDomain td) (hs0 : 0<s) (hsource : tPrimary C td= -s)
    (hcore : (C.point T).a=7/12) (hflat : td=false → delta C.theta T=0)
    (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td)
      (if de then 3 else 2) (if de then 0 else 1) i)) : False := by
  let t := delta C.theta G+(if de then delta C.theta D else delta C.theta E)
  let f := SolePositiveTExclusion.choose de t
  have hde : isDE f=de := SolePositiveTExclusion.choose_isDE de t
  have hE' : 0≤ePrimary C f := by simpa [ePrimary,hde] using hE
  have htotal : delta C.theta G+ePrimary C f=t := by simp [t,ePrimary,hde]
  obtain ⟨ht0,hP,hN⟩ := SoleNegativeTOriginalBlocks.original_budgets hab f false td
    hvar hG hE' hs0.le hsource htotal
  have hP0 : 0≤∑i,(SoleNegativeTOriginalBlocks.blocks C ab f false td t s i).P :=
    Finset.sum_nonneg (fun i _ => (SoleNegativeTOriginalBlocks.blocks C ab f false td t s i).P_nonneg)
  have htcap : t∈Icc 0 frameCap := ⟨ht0,by linarith⟩
  have ht : t∈domain f := SolePositiveTExclusion.choose_mem de htcap
  have hx : delta C.theta G∈Icc 0 t := ⟨hG,by linarith⟩
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt hq0
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  have hRsq : (Real.sqrt q)^2≤qCap := by simpa only [hR2] using hcap
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by simpa only [hR2] using hC.contained
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => (hC.contained i).trans hcap
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hM : axisCoordinate q≤283/200 := by
    have hm := Real.sqrt_le_sqrt (sub_le_sub_right hQU (1/4))
    have hu : Real.sqrt (qTrial-1/4)<1914558470771/1000000000000 := by
      have h := SoleTScalarModel.axis_upper
      rw [show ((SoleTScalarModel.axisUpper:ℚ):ℝ)=1914558470771/1000000000000 by
        norm_num [SoleTScalarModel.axisUpper]] at h
      exact h
    simp only [axisCoordinate]
    linarith
  have hconc := SoleNegativeTSplit.concave (s := s) ab td hR hRsq hM ht hC.sorted hcCap ha
  have h0 : 0<SoleNegativeTSplit.value C ab f td (Real.sqrt q) (axisCoordinate q) t s 0 := by
    have hh := SoleNegativeTEndpoint.endpoint_positive false td hab hQL hQU ht hs hs0
      hC hn hvar hG hE' hsource htotal hcore hflat
    simpa only [x,face,Bool.false_eq_true,ite_false] using hh
  have h1 : 0<SoleNegativeTSplit.value C ab f td (Real.sqrt q) (axisCoordinate q) t s t := by
    have hh := SoleNegativeTEndpoint.endpoint_positive true td hab hQL hQU ht hs hs0
      hC hn hvar hG hE' hsource htotal hcore hflat
    simpa only [x,face,ite_true,sub_zero] using hh
  have hpos := SoleNegativeTSplit.positive_of_endpoints hconc hx h0 h1
  have hnec := SoleNegativeTSplit.necessary td hab hR ht (short_small hs) hG hE' htotal
    hC.sorted hc hn (SoleEndpointSupport.primary_le_axis hQL (hC.sorted E) (hC.contained E))
    (by intro h; apply hsign; simpa only [hde] using h)
    (by simpa only [deOwner,ehOwner,hde] using hf)
  exact (not_lt_of_ge hnec) hpos

theorem reselect_TD {C : SignedCycle} {ab td de eh : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 td de eh i)) (hT : C.Feasible T 0) :
    ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de eh i) := by
  intro i
  fin_cases i
  · simpa [CoreEStress.owners] using hf 0
  · simpa [CoreEStress.owners] using hf 1
  · simpa [CoreEStress.owners] using hf 2
  · simpa [CoreEStress.owners] using hf 3
  · simpa [CoreEStress.owners,T] using hT
  · simpa [CoreEStress.owners] using hf 5
  · simpa [CoreEStress.owners] using hf 6

theorem reselect_BT {C : SignedCycle} {ab bt de eh : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt 0 de eh i)) (hB : C.Feasible B 2) :
    ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de eh i) := by
  intro i
  fin_cases i
  · simpa [CoreEStress.owners] using hf 0
  · simpa [CoreEStress.owners] using hf 1
  · simpa [CoreEStress.owners] using hf 2
  · simpa [CoreEStress.owners,B] using hB
  · simpa [CoreEStress.owners] using hf 4
  · simpa [CoreEStress.owners] using hf 5
  · simpa [CoreEStress.owners] using hf 6

theorem negative_TD_false {C : SignedCycle} {ab : Fin 4} (de : Bool) {q : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hE : 0≤ if de then delta C.theta D else delta C.theta E)
    (hTb : (C.point T).Boundary q) (hT : delta C.theta T<0)
    (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2
      (if de then 3 else 2) (if de then 0 else 1) i)) : False := by
  let s := -delta C.theta T
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next T) T)⟩
  have hsource : delta C.theta T= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (delta C.theta B) 2 :=
    (BT_contact C 2).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) (-s) 2 := by
    rw [← hsource]
    exact (TD_contact C 2).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  obtain hsecondary | ⟨hcore,hflat,hy,hyu,hshort⟩ := NegativeTEntry.negative_TD_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core T) (hC.core D) hcap hn.D_nonpos hs hBT hTD
  · have hsame : C.Feasible T 0 := (TD_contact C 0).2 (by simpa [hsource] using hsecondary)
    exact SolePositiveExclusion.original_false de hQL hQU hC hn hvar hab hG hE hsign
      (reselect_TD hf hsame)
  · exact original_flat_false de true hQL hQU hC hn hvar hab hG hE
      (show s∈shortDomain true from ⟨hs.1.le,hshort.le⟩) hs.1 hsource hflat
      (by intro h; cases h) hsign hf

theorem negative_BT_false {C : SignedCycle} {ab : Fin 4} (de : Bool) {q : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hE : 0≤ if de then delta C.theta D else delta C.theta E)
    (hTb : (C.point T).Boundary q) (hB : delta C.theta B<0) (halign : delta C.theta T=0)
    (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0
      (if de then 3 else 2) (if de then 0 else 1) i)) : False := by
  by_cases hsecondary : C.Feasible B 2
  · exact SolePositiveExclusion.original_false de hQL hQU hC hn hvar hab hG hE hsign
      (reselect_BT hf hsecondary)
  let s := -delta C.theta B
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next B) B)⟩
  have hsource : delta C.theta B= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (-s) 3 := by
    rw [← hsource]
    exact (BT_contact C 3).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) 0 0 := by
    rw [← halign]
    exact (TD_contact C 0).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hnot : ¬quarterFeasible (C.point B) (C.point T) (-s) 2 := by
    intro hh
    exact hsecondary ((BT_contact C 2).2 (by simpa [hsource] using hh))
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  obtain ⟨hcore,hflat,hy,hyu,hshort⟩ := NegativeTEntry.negative_BT_aligned_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core D) hcap hn.B_nonpos hn.D_nonpos hs hBT hTD hnot
  exact original_flat_false de false hQL hQU hC hn hvar hab hG hE
    (show s∈shortDomain false from ⟨hs.1.le,hshort.le⟩) hs.1 hsource hflat
    (fun _ => halign) hsign hf

theorem all_TD_false {C : SignedCycle} {ab : Fin 4} (de : Bool) {q : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hE : 0≤ if de then delta C.theta D else delta C.theta E)
    (hTb : (C.point T).Boundary q) (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2
      (if de then 3 else 2) (if de then 0 else 1) i)) : False := by
  by_cases hT : 0≤delta C.theta T
  · exact SolePositiveTExclusion.original_false de true hQL hQU hC hn hvar hab hG hE hT hsign hf
  · exact negative_TD_false de hQL hQU hC hn hvar hab hG hE hTb (lt_of_not_ge hT) hsign hf

theorem all_BT_false {C : SignedCycle} {ab : Fin 4} (de : Bool) {q : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hE : 0≤ if de then delta C.theta D else delta C.theta E)
    (hTb : (C.point T).Boundary q) (halign : delta C.theta B<0 → delta C.theta T=0)
    (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0
      (if de then 3 else 2) (if de then 0 else 1) i)) : False := by
  by_cases hB : 0≤delta C.theta B
  · exact SolePositiveTExclusion.original_false de false hQL hQU hC hn hvar hab hG hE hB hsign hf
  · have hB' := lt_of_not_ge hB
    exact negative_BT_false de hQL hQU hC hn hvar hab hG hE hTb hB' (halign hB') hsign hf

end SquaresInCircles.Eight.SoleNegativeTExclusion
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleAllTExclusion
open Candidate SignedCycle PositiveGAOuterSoleReduction

theorem original {q : ℝ} (I : BoundaryInput q) (de : Bool)
    (hQL : qLow≤q) (hQU : q≤qTrial)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0≤delta I.cycle.theta G) (hT : TRegime I)
    (hE : 0≤ if de then delta I.cycle.theta D else delta I.cycle.theta E)
    (hsign : de=true → (I.cycle.point E).y≤0)
    (hDE : I.cycle.Feasible D (if de then 3 else 2))
    (hEH : I.cycle.Feasible E (if de then 0 else 1)) : False := by
  have hab : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  have hf := reselect_E (CoreESignedExclusion.original_owners I hHG hGA) hDE hEH
  rcases hT with ⟨hBT,hTD⟩ | ⟨hBT,hTD⟩ | ⟨hBT,hTD,halign⟩
  · rw [hBT,hTD] at hf
    exact SolePositiveExclusion.original_false de hQL hQU I.necessary I.anchors_normal
      I.positive_variation.le hab hG hE hsign hf
  · rw [hBT,hTD] at hf
    exact SoleNegativeTExclusion.all_TD_false de hQL hQU I.necessary I.anchors_normal
      I.positive_variation.le hab hG hE (I.radial T) hsign hf
  · rw [hBT,hTD] at hf
    exact SoleNegativeTExclusion.all_BT_false de hQL hQU I.necessary I.anchors_normal
      I.positive_variation.le hab hG hE (I.radial T) halign hsign hf

theorem sole_EH_false {q : ℝ} (I : BoundaryInput q)
    (hQL : qLow≤q) (hQU : q≤qTrial)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0≤delta I.cycle.theta G) (hT : TRegime I)
    (hDE : I.cycle.Feasible D 2) (hEH : I.cycle.Feasible E 1)
    (hE : 0≤delta I.cycle.theta E) : False :=
  original I false hQL hQU hHG hGA hG hT hE (by intro h; cases h) hDE hEH

theorem sole_DE_nonpos_false {q : ℝ} (I : BoundaryInput q)
    (hQL : qLow≤q) (hQU : q≤qTrial)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0≤delta I.cycle.theta G) (hT : TRegime I)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 0)
    (hD : 0≤delta I.cycle.theta D) (hEy : (I.cycle.point E).y≤0) : False :=
  original I true hQL hQU hHG hGA hG hT hD (fun _ => hEy) hDE hEH

end SquaresInCircles.Eight.SoleAllTExclusion
end
end
end
