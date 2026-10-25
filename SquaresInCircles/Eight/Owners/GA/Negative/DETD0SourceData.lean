module

public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3PositivePure
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeAConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.DEHighLateData
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowSeparated
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2OriginalStress
public import SquaresInCircles.Eight.Owners.GA.Secant.DPositiveEndpoint

/-!
# Eight squares: negative core DE3 with actual BT2 and arbitrary original TD0

Unlike positive-BT3, the BT2 error is not selected and stays in B's
ordinary signed block. The equal B/T weights eliminate T's coordinate
without a radial or tangent assumption. The negative DE3 is selected
and D retains its actual original TD0 error with secant support.
-/

section
/-!
## The high-total D cost is paid at every remaining negative angle

The negative curvature bound is integrated backwards from the original
cap. The resulting slope depends on the actual removed DE magnitude.
The secant and tilted alternatives in gamma are both bounded before the
maximum is taken. The support tie and both zero-angle endpoints remain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighSlopes
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope

lemma negative_derivative {p q s w : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : (2/3)*q≤p)
    (hs : s∈Icc 0 frameCap) (hw : w∈Icc 0 (frameCap-s)) :
    (2/3+(36/125)*s)*q<Vd R p q w := by
  have hq := hp.trans_le hpq
  have hratio : q≤2*p := by linarith
  have hwf : w∈Icc 0 frameCap := ⟨hw.1,by linarith [hw.2,hs.1]⟩
  have hd (t : ℝ) (ht : t∈Icc 0 frameCap) :
      HasDerivAt (fun t => -Vd R p q t) (-NegativeDEHighShape.Vdd p q t) t :=
    (Vd_hasDerivAt (R:=R) hp hq ht).fun_neg
  have hg := derivative_reserve
    (f:=fun t => -Vd R p q t) (df:=fun t => -NegativeDEHighShape.Vdd p q t)
    (k:=(36/125)*q)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t (Ioo_subset_Icc_self ht))
    (fun t ht => by
      have hh := NegativeDEHighShape.second_whole hp hpq hratio (Ioo_subset_Icc_self ht)
      linarith)
    hwf (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hwf.2
  have he := Vd_lower hp hpq hqp
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hremaining := mul_le_mul_of_nonneg_left
    (show s≤frameCap-w by linarith [hw.2]) (show 0≤(36/125)*q by positivity)
  have he' : (2/3)*q<Vd R p q frameCap := he
  linarith

def secantFirst (s : ℝ) : ℝ := Real.sin s/Real.cos s^2
def secantSecond (s : ℝ) : ℝ := (1+Real.sin s^2)/Real.cos s^3

theorem secantFirst_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt secantFirst (secantSecond s) s := by
  have hc := NegativeESecant.cos_pos hs
  have hd := (Real.hasDerivAt_sin s).div ((Real.hasDerivAt_cos s).pow 2)
    (pow_ne_zero 2 hc.ne')
  convert hd using 1
  · rfl
  · dsimp [secantSecond]
    field_simp [hc.ne']
    nlinarith [Real.sin_sq_add_cos_sq s]

def secantReserve (s : ℝ) : ℝ :=
  (431/500)*(2/3+(36/125)*s)-SecantD.slope*Explicit.sec s

theorem secantReserve_concave : ConcaveOn ℝ (Icc 0 frameCap) secantReserve := by
  have hd (s : ℝ) (hs : s∈Icc 0 frameCap) :
      HasDerivAt secantReserve
        ((431/500)*(36/125)-SecantD.slope*secantFirst s) s := by
    have h1 : HasDerivAt (fun s : ℝ => (431/500)*(2/3+(36/125)*s)) ((431/500)*((36/125)*1)) s :=
      (((hasDerivAt_id' s).const_mul (36/125)).const_add (2/3)).const_mul (431/500)
    have h2 : HasDerivAt (fun s => SecantD.slope*NegativeELargeA.secant s)
        (SecantD.slope*(Real.sin s/Real.cos s^2)) s :=
      (NegativeELargeA.secant_hasDerivAt hs).const_mul SecantD.slope
    have he : secantReserve=fun s =>
        (431/500)*(2/3+(36/125)*s)-SecantD.slope*NegativeELargeA.secant s := rfl
    rw [he]
    convert h1.fun_sub h2 using 1
    simp only [secantFirst]
    ring
  have hdd (s : ℝ) (hs : s∈Icc 0 frameCap) :
      HasDerivAt (fun s => (431/500)*(36/125)-SecantD.slope*secantFirst s)
        (-SecantD.slope*secantSecond s) s :=
    (((secantFirst_hasDerivAt hs).const_mul SecantD.slope).const_sub
      ((431/500)*(36/125))).congr_deriv (by ring)
  apply concave_of_deriv2 (fun s hs => hd s hs) (fun s hs => hdd s hs)
  intro s hs
  have hc := NegativeESecant.cos_pos hs
  have hpos : 0<secantSecond s := by
    unfold secantSecond
    positivity
  simp only [SecantD.slope]
  linarith

theorem secantReserve_positive {s : ℝ} (hs : s∈Icc 0 frameCap) : 0<secantReserve s := by
  have h0 : 0<secantReserve 0 := by
    norm_num [secantReserve,SecantD.slope,Explicit.sec,NegativeELargeA.secant]
  have h1 : 0<secantReserve frameCap := by
    have hh := (NegativeELargeA.secant_range
      (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).2
    dsimp [secantReserve,SecantD.slope,frameCap,SecantD.qUpper] at *
    linarith
  exact concave_gt_of_endpoints secantReserve_concave hs h0 h1

lemma gamma_below_slope {θ z s : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap) (j : Fin 3) :
    Explicit.gamma .high θ z s<(2/3+(36/125)*s)*Explicit.q .high θ j := by
  have hq := (Explicit.high_q_bounds hθ j).1
  have hfactor : 0<2/3+(36/125)*s := by linarith [hs.1]
  have hqmul := mul_lt_mul_of_pos_left hq hfactor
  have hsec := secantReserve_positive hs
  have hc := Explicit.high_c_ratio hθ hz j
  have hcmul := mul_lt_mul_of_pos_left hc (by norm_num [SecantD.slope] : 0<SecantD.slope)
  have hsq := mul_nonneg hs.1 (show 0≤Explicit.q .high θ j by linarith)
  have hleft : SecantD.slope*Explicit.sec s<
      (2/3+(36/125)*s)*Explicit.q .high θ j := by
    dsimp [secantReserve] at hsec
    nlinarith only [hqmul,hsec]
  have hright : SecantD.slope*Explicit.c .high θ z<
      (2/3+(36/125)*s)*Explicit.q .high θ j := by
    dsimp [SecantD.slope] at hcmul
    nlinarith only [hcmul,hsq,hq]
  rw [Explicit.gamma,mul_max_of_nonneg _ _ (by norm_num [SecantD.slope])]
  exact max_lt hleft hright

/-- The derivative bound retains the actual original DE magnitude s. -/
theorem gamma_derivative {θ z s w : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap)
    (hw : w∈Icc 0 (frameCap-s)) (j : Fin 3) :
    Explicit.gamma .high θ z s<Vd R (Explicit.p .high θ j) (Explicit.q .high θ j) w := by
  have hp := Explicit.high_pairs hθ j
  exact (gamma_below_slope hθ hz hs j).trans
    (negative_derivative hp.1 hp.2.1 hp.2.2.le hs hw)

theorem gamma_growth {θ z s x y : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap)
    (hx : x∈Icc 0 (frameCap-s)) (hy : y∈Icc 0 (frameCap-s))
    (hxy : x≤y) (j : Fin 3) :
    Explicit.gamma .high θ z s*(y-x)≤Explicit.V .high θ j y-Explicit.V .high θ j x := by
  have hp := Explicit.high_pairs hθ j
  have hd (w : ℝ) (hw : w∈Icc 0 (frameCap-s)) :
      HasDerivAt (Explicit.V .high θ j)
        (Vd R (Explicit.p .high θ j) (Explicit.q .high θ j) w) w :=
    V_hasDerivAt (R:=R) hp.1 (hp.1.trans_le hp.2.1)
      (show w∈Icc 0 frameCap from ⟨hw.1,by linarith [hw.2,hs.1]⟩)
  exact derivative_reserve
    (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
    (fun w hw => hd w (Ioo_subset_Icc_self hw))
    (fun w hw => (gamma_derivative hθ hz hs (Ioo_subset_Icc_self hw) j).le)
    hx hy hxy

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighSlopes
end
end
end

section
/-!
## High-total concentration for the DE3 / BT3 stress

Both signed mass caps are kept. Ordinary separated blocks use the whole or the shortened slope
reserve according to the sign of their surplus. The distinguished TD0 block uses the
secant-dependent `gamma` and the remaining-angle comparison, also when both signs are allocated to
that block. Every concentration alternative thus reduces to a pure signed surplus (`sum_to_pure`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighConcentration
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope

lemma ordinary_separated {θ s P N : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hs : s∈Icc 0 frameCap) (hP : 0≤P) (hN : 0≤N)
    (hPb : P≤frameCap-θ) (hNb : N≤frameCap-s)
    (hbalance : N-P=θ-s) (i j : Fin 3) :
    (if s≤θ then Explicit.V .high θ j (θ-s) else Explicit.U .high θ i (s-θ))≤
      Explicit.U .high θ i P+Explicit.V .high θ j N := by
  have hi := Explicit.high_pairs hθ i
  have hj := Explicit.high_pairs hθ j
  have hip : Explicit.q .high θ i≤2*Explicit.p .high θ i := by linarith [hi.1,hi.2.2]
  have hqj := hj.1.trans_le hj.2.1
  have hPcap : P∈Icc 0 frameCap := ⟨hP,by linarith [hθ.1]⟩
  have hNcap : N∈Icc 0 frameCap := ⟨hN,by linarith [hs.1]⟩
  have hPshort : P∈Icc 0 (8/15:ℝ) := by
    dsimp [frameCap] at hPb
    exact ⟨hP,by linarith [hθ.1]⟩
  have hratio := Explicit.high_spread hθ i j
  by_cases hst : s≤θ
  · have hPN : P≤N := by linarith
    have hdiff : N-P∈Icc 0 frameCap := ⟨by linarith,by linarith [hNcap.2]⟩
    have hv := V_growth hj.1 hj.2.1 hj.2.2.le hdiff hNcap (by linarith)
    have hu := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
      hi.1 hi.2.1 hip hPcap
    have hpay := mul_nonneg
      (show 0≤(2/3)*Explicit.q .high θ j-(109/200)*Explicit.q .high θ i by
        nlinarith [hqj.le]) hP
    rw [hbalance] at hv
    simp only [ite_eq_left hst]
    dsimp [Explicit.U,Explicit.V]
    nlinarith
  · have hNP : N≤P := by linarith
    have hNshort : N∈Icc 0 (8/15:ℝ) := ⟨hN,hNP.trans hPshort.2⟩
    have hdiff : P-N∈Icc 0 (8/15:ℝ) := ⟨by linarith,by linarith [hPshort.2]⟩
    have hsurplus : P-N=s-θ := by linarith
    have hv := NegativeDEPositiveTD.OrdinarySlope.negative_short_growth hj.1 hj.2.1 hj.2.2.le
      (by norm_num : (0:ℝ)∈Icc 0 (8/15:ℝ)) hNshort hN
    have hu := NegativeDEPositiveTD.OrdinarySlope.positive_short_growth hi.1 hi.2.1 hip
      hdiff hPshort (by linarith)
    have hpay := mul_nonneg
      (show 0≤(39/50)*Explicit.q .high θ j-(16/25)*Explicit.q .high θ i by
        nlinarith [hqj.le]) hN
    simp only [V_zero,sub_zero] at hv
    rw [hsurplus] at hu
    simp only [ite_eq_right hst]
    dsimp [Explicit.U,Explicit.V]
    nlinarith

lemma D_separated {θ z s P N : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap) (hP : 0≤P) (hN : 0≤N)
    (_hPb : P≤frameCap-θ) (hNb : N≤frameCap-s)
    (hbalance : N-P=θ-s) (j : Fin 3) :
    (if s≤θ then Explicit.V .high θ j (θ-s)
      else -Explicit.gamma .high θ z s*(s-θ))≤
        -Explicit.gamma .high θ z s*P+Explicit.V .high θ j N := by
  by_cases hst : s≤θ
  · have hdiff : N-P∈Icc 0 (frameCap-s) := ⟨by linarith,by linarith⟩
    have hg := HighSlopes.gamma_growth hθ hz hs hdiff ⟨hN,hNb⟩ (by linarith) j
    rw [show N-(N-P)=P by ring,hbalance] at hg
    simp only [hst,↓reduceIte]
    linarith
  · have hg := HighSlopes.gamma_growth hθ hz hs
      (show (0:ℝ)∈Icc 0 (frameCap-s) from ⟨le_rfl,by linarith [hs.2]⟩)
      ⟨hN,hNb⟩ hN j
    have h0 : Explicit.V .high θ j 0=0 := by simp [Explicit.V,V_zero]
    rw [h0,sub_zero,sub_zero] at hg
    have hsurplus : s-θ=P-N := by linarith
    simp only [hst,↓reduceIte,hsurplus]
    linarith

lemma separated_lower {θ z s : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap) (i j : Fin 4) :
    Blocks.pure .high θ z s i j≤
      Blocks.positive .high θ z s (frameCap-θ) i+
        Blocks.negative .high θ (frameCap-s) j := by
  have ht := Explicit.frame_domain .high hθ
  have hP : 0≤frameCap-θ := sub_nonneg.mpr ht.2
  have hN : 0≤frameCap-s := sub_nonneg.mpr hs.2
  have hbalance : frameCap-s-(frameCap-θ)=θ-s := by ring
  have hpure : Blocks.pure .high θ z s i j=if s≤θ then Blocks.negative .high θ (θ-s) j
      else Blocks.positive .high θ z s (s-θ) i := rfl
  rw [hpure]
  by_cases hi : i=3
  · subst i
    have hh := D_separated hθ hz hs hP hN le_rfl le_rfl hbalance (Blocks.ordinaryIndex j)
    rw [Blocks.positive_D,Blocks.positive_D,Blocks.negative_to_ordinary,
      Blocks.negative_to_ordinary]
    exact hh
  · have hi3 : i.val≠3 := fun h => hi (Fin.ext h)
    obtain ⟨r,hr⟩ : ∃r : Fin 3,r.castSucc=i :=
      ⟨⟨i.val,by have := i.isLt; omega⟩,Fin.ext rfl⟩
    subst i
    have hh := ordinary_separated hθ hs hP hN le_rfl le_rfl hbalance r (Blocks.ordinaryIndex j)
    rw [Blocks.positive_ordinary,Blocks.positive_ordinary,Blocks.negative_to_ordinary,
      Blocks.negative_to_ordinary]
    exact hh

theorem saturated_lower {θ z s : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap) (i j : Fin 4) :
    Blocks.pure .high θ z s i j≤Blocks.saturated .high θ z s i j := by
  by_cases hij : i=j
  · subst j
    by_cases hi : i=3
    · subst i
      have he : Blocks.saturated .high θ z s 3 3=
          Blocks.block .high θ z s (frameCap-θ) (frameCap-s) 3 := by
        simp only [Blocks.saturated,ChargedHybridConcentration.saturated,Blocks.block,
          ↓reduceIte]
      rw [he,Blocks.block_D]
      exact separated_lower hθ hz hs 3 3
    · have hi3 : i.val≠3 := fun h => hi (Fin.ext h)
      obtain ⟨r,hr⟩ : ∃r : Fin 3,r.castSucc=i :=
        ⟨⟨i.val,by have := i.isLt; omega⟩,Fin.ext rfl⟩
      subst i
      exact SameBlock.ordinary_saturated_lower .high hθ hs r
  · have he : Blocks.saturated .high θ z s i j=
        Blocks.positive .high θ z s (frameCap-θ) i+Blocks.negative .high θ (frameCap-s) j := by
      simp only [Blocks.saturated,ChargedHybridConcentration.saturated,hij,↓reduceIte]
      rfl
    rw [he]
    exact separated_lower hθ hz hs i j

/-- Every high-total allocation has a pure lower bound. The indices are scalar allocations, not
geometric witnesses. -/
theorem sum_to_pure {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,Blocks.pure .high θ z s i j≤∑k,Blocks.block .high θ z s (P k) (N k) k := by
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .high P N hθ hs hP hN hPb hNb hbalance
  rw [min_eq_left (saturated_lower hθ hz hs i j)] at hij
  exact ⟨i,j,hij⟩

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighConcentration
end
end
end

section
/-!
## Original source stress and both signed budgets for negative DE3 / BT3

Only the actual BT3 argument, the
selected A arguments, and the negative DE3 argument are removed. The
original EH0 argument remains at H and the original TD0 argument remains
as the distinguished D singleton. The E tangent coefficient cancels
only after the true flat-core identity and nonzero original cosine.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks PairedE
open NegativePrimary (erase)

abbrev aTotal := LowA.aTotal
abbrev selectedA := NegativeELargeA.Source.selectedA
abbrev magnitude := NegativeDEPositiveTD.Source.magnitude
abbrev deCorrection := NegativeDEPositiveTD.Source.deCorrection

def total (C : SignedCycle) (ga ab : Bool) : ℝ := aTotal C ga ab+delta C.theta B
def owners (hg ga ab : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,3,0,3,0]
def tilted (m eta z : ℝ) : ℝ := m*(Real.cos z+eta*Real.sin z)
def weights (C : SignedCycle) (k l m eta : ℝ) : Vertex→ℝ :=
  ![k,l,l,m,tilted m eta (delta C.theta B),1/Real.cos (delta C.theta D),1]
def stress (C : SignedCycle) (hg ga ab : Bool) (k l m eta : ℝ) : ℝ :=
  ∑i,weights C k l m eta i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab i))

def blocks (C : SignedCycle) (hg ga ab : Bool) (k l m : ℝ) : Fin 4→Block :=
  ![⟨k,1,erase (!hg) (delta C.theta H),delta C.theta E⟩,
    ⟨k,l,erase hg (delta C.theta H),erase ga (delta C.theta G)⟩,
    ⟨l,m,erase ab (delta C.theta A),0⟩,
    ⟨k,1,delta C.theta T,0⟩]

def actualBlocks (C : SignedCycle) (hg ga ab : Bool) (k l m eta : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 2) (C.point B).reflect,
    SecantD.actualIncrement (1/Real.cos (delta C.theta D))
      (tilted m eta (delta C.theta B)) (delta C.theta T) (C.point D)]

def tReserve (C : SignedCycle) (m eta : ℝ) : ℝ :=
  m*Real.sin (delta C.theta B)*(fullSupport 1 eta-((C.point T).a+eta*(C.point T).y))
def base (C : SignedCycle) (k l m eta : ℝ) : ℝ :=
  k+2*l+m*edgeWidth (delta C.theta B)+tilted m eta (delta C.theta B)+
    1/Real.cos (delta C.theta D)+1-m*fullSupport 1 eta*Real.sin (delta C.theta B)-
    fullSupport 1 k-fullSupport k l-fullSupport l m-
    PositiveBT3.sortedSupport (1/Real.cos (delta C.theta D)) (tilted m eta (delta C.theta B))+
      deCorrection C

theorem decomposition (C : SignedCycle) (hg ga ab : Bool) (k l m eta : ℝ)
    (hflat : (C.point E).a=7/12) (hcos : Real.cos (delta C.theta D)≠0) :
    stress C hg ga ab k l m eta=base C k l m eta+
      (∑i,actualBlocks C hg ga ab k l m eta i)+
      l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+tReserve C m eta := by
  have hsymm : ∀ a b : ℝ,fullSupport a b=fullSupport b a := by
    intro a b
    simp only [fullSupport,add_comm (a^2) (b^2),add_comm a b]
  have hf : (C.point 6).a=7/12 := hflat
  have hinv : (Real.cos (C.theta 6-C.theta 5))⁻¹*Real.cos (C.theta 6-C.theta 5)=1 :=
    inv_mul_cancel₀ hcos
  cases hg <;> cases ga <;> cases ab <;>
    simp [stress,weights,owners,blocks,actualBlocks,base,tReserve,
      deCorrection,NegativeDEPositiveTD.Source.deCorrection,tilted,
      PositiveTD.actualPairIncrement,SecantD.actualIncrement,pairF,pairG,
      primaryGain,erase,hf,SignedCycle.edge,zeroProjection,quarterProjection,
      Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,SignedPoint.reflect,hsymm l k,hsymm m l] <;>
    linear_combination (C.point 6).y*hinv

theorem sum_parts (C : SignedCycle) (hg ga ab : Bool) (k l m : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab k l m i).u+f (blocks C hg ga ab k l m i).v))=
      (∑i,f (delta C.theta i))-selectedA C ga ab f-f (delta C.theta B)-f (delta C.theta D) := by
  cases hg <;> cases ga <;> cases ab <;>
    simp [blocks,erase,selectedA,NegativeELargeA.Source.selectedA,selected,
      Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

structure Budgets (C : SignedCycle) (hg ga ab : Bool) (k l m : ℝ) : Prop where
  total_domain : total C ga ab∈Icc 0 frameCap
  a_domain : aTotal C ga ab∈Icc 0 (total C ga ab)
  bt_domain : delta C.theta B∈Icc 0 (total C ga ab)
  de_domain : magnitude C∈Icc 0 frameCap
  positive_bound : (∑i,(blocks C hg ga ab k l m i).P)≤frameCap-total C ga ab
  negative_bound : (∑i,(blocks C hg ga ab k l m i).N)≤frameCap-magnitude C
  balance : (∑i,(blocks C hg ga ab k l m i).N)-(∑i,(blocks C hg ga ab k l m i).P)=
    total C ga ab-magnitude C

theorem budgets {C : SignedCycle} (hg ga ab : Bool) (k l m : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0) : Budgets C hg ga ab k l m := by
  have hp := sum_parts C hg ga ab k l m positivePart positivePart_zero
  have hn := sum_parts C hg ga ab k l m negativePart negativePart_zero
  have hA := NegativeELargeA.Source.selectedA_signed C ga ab
  have hAP := NegativeELargeA.Source.selectedA_nonnegative C ga ab positivePart positivePart_nonneg
  have hAN := NegativeELargeA.Source.selectedA_nonnegative C ga ab negativePart negativePart_nonneg
  have hzP : positivePart (delta C.theta B)=delta C.theta B := max_eq_left hz
  have hzN : negativePart (delta C.theta B)=0 := max_eq_right (by linarith)
  have hsP : positivePart (delta C.theta D)=0 := max_eq_right hs
  have hsN : negativePart (delta C.theta D)=magnitude C := max_eq_left (neg_nonneg.mpr hs)
  have hP : (∑i,(blocks C hg ga ab k l m i).P)=
      positiveVariation C.theta-selectedA C ga ab positivePart-delta C.theta B := by
    simpa only [Block.P,hzP,hsP,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab k l m i).N)=
      negativeVariation C.theta-selectedA C ga ab negativePart-magnitude C := by
    simpa only [Block.N,hzN,hsN,sub_zero,negativeVariation] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l m i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l m i).N_nonneg)
  have heq := variations_equal C.theta
  have hs0 : 0≤ magnitude C := neg_nonneg.mpr hs
  change selectedA C ga ab positivePart-selectedA C ga ab negativePart=aTotal C ga ab at hA
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [total]; exact ⟨add_nonneg ha hz,by linarith⟩
  · dsimp [total]; exact ⟨ha,by linarith⟩
  · dsimp [total]; exact ⟨hz,by linarith⟩
  · exact ⟨hs0,by linarith⟩
  · dsimp [total]; linarith
  · linarith
  · dsimp [total]; linarith

theorem block_coefficients {C : SignedCycle} (hg ga ab : Bool) {k l m : ℝ}
    (hk : k≤1) (hl : k≤l) (i : Fin 4) :
    (blocks C hg ga ab k l m i).p=(![k,k,min l m,k] : Fin 4→ℝ) i ∧
    (blocks C hg ga ab k l m i).q=(![1,l,max l m,1] : Fin 4→ℝ) i := by
  fin_cases i <;> simp [blocks,Block.p,Block.q,min_eq_left hk,max_eq_right hk,
    min_eq_left hl,max_eq_right hl]

theorem block_budgets {C : SignedCycle} (hg ga ab : Bool) (k l m : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0) (i : Fin 4) :
    (blocks C hg ga ab k l m i).P≤frameCap ∧ (blocks C hg ga ab k l m i).N≤frameCap := by
  have hb := budgets hg ga ab k l m hvar ha hz hs
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l m j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l m j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.total_domain.1],
    by linarith [hb.negative_bound,hb.de_domain.1]⟩

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Source
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDETD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks PairedE
open NegativePrimary (erase)

abbrev aTotal := NegativeDEPositiveBT.Source.aTotal
abbrev magnitude := NegativeDEPositiveBT.Source.magnitude
abbrev deCorrection := NegativeDEPositiveBT.Source.deCorrection

def owners (hg : Fin 4) (ga ab : Bool) : Vertex→Fin 4 :=
  ![hg,if ga then 3 else 2,if ab then 2 else 0,2,0,3,0]

def weights (C : SignedCycle) (k l m : ℝ) : Vertex→ℝ :=
  ![k,l,l,m,m,1/Real.cos (delta C.theta D),1]

def stress (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l m : ℝ) : ℝ :=
  ∑i,weights C k l m i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab i))

/-- The B block keeps the true BT2 error, and D keeps TD0. -/
def blocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l m : ℝ) : Fin 4→Block :=
  ![⟨k,1,if hg=0 then 0 else delta C.theta H,delta C.theta E⟩,
    ⟨k,l,if hg=0 then delta C.theta H else 0,erase ga (delta C.theta G)⟩,
    ⟨l,m,erase ab (delta C.theta A),delta C.theta B⟩,
    ⟨k,1,delta C.theta T,0⟩]

def actualBlocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l m : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 2) (C.point B).reflect,
    SecantD.actualIncrement (1/Real.cos (delta C.theta D)) m
      (delta C.theta T) (C.point D)]

def base (C : SignedCycle) (k l m : ℝ) : ℝ :=
  k+2*l+2*m+1/Real.cos (delta C.theta D)+1-
    fullSupport 1 k-fullSupport k l-fullSupport l m-
    PositiveBT3.sortedSupport (1/Real.cos (delta C.theta D)) m+
    deCorrection C

theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab : Bool)
    (hhg : hg=0∨hg=2) (k l m : ℝ)
    (hflat : (C.point E).a=7/12) (hcos : Real.cos (delta C.theta D)≠0) :
    stress C hg ga ab k l m=base C k l m+
      (∑i,actualBlocks C hg ga ab k l m i)+
      l*PairedE.primaryGain (C.point A) ga ab
        (delta C.theta G) (delta C.theta A) := by
  have hsymm : ∀ a b : ℝ,fullSupport a b=fullSupport b a := by
    intro a b
    simp only [fullSupport,add_comm (a^2) (b^2),add_comm a b]
  have hf : (C.point 6).a=7/12 := hflat
  have hinv : (Real.cos (C.theta 6-C.theta 5))⁻¹*Real.cos (C.theta 6-C.theta 5)=1 :=
    inv_mul_cancel₀ hcos
  cases ga <;> cases ab <;> rcases hhg with rfl|rfl <;>
    simp [stress,weights,owners,blocks,actualBlocks,base,
      deCorrection,NegativeDEPositiveTD.Source.deCorrection,
      PositiveTD.actualPairIncrement,SecantD.actualIncrement,
      pairF,pairG,PairedE.primaryGain,erase,hf,SignedCycle.edge,
      zeroProjection,quarterProjection,Fin.sum_univ_succ,
      word,delta,next,H,G,A,B,T,D,E,SignedPoint.reflect,hsymm l k,hsymm m l] <;>
    linear_combination (C.point 6).y*hinv

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l m : ℝ) (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab k l m i).u+
      f (blocks C hg ga ab k l m i).v))=
    (∑i,f (delta C.theta i))-NegativeELargeA.Source.selectedA C ga ab f-
      f (delta C.theta D) := by
  cases ga <;> cases ab <;> by_cases hhg : hg=0 <;>
    simp [blocks,erase,NegativeELargeA.Source.selectedA,selected,hhg,
      Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

structure Budgets (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l m : ℝ) : Prop where
  a_domain : aTotal C ga ab∈Icc 0 frameCap
  de_domain : magnitude C∈Icc 0 frameCap
  positive_bound : (∑i,(blocks C hg ga ab k l m i).P)≤frameCap-aTotal C ga ab
  negative_bound : (∑i,(blocks C hg ga ab k l m i).N)≤frameCap-magnitude C
  balance : (∑i,(blocks C hg ga ab k l m i).N)-
    (∑i,(blocks C hg ga ab k l m i).P)=aTotal C ga ab-magnitude C

theorem budgets {C : SignedCycle} (hg : Fin 4) (ga ab : Bool) (k l m : ℝ)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta D≤0) :
    Budgets C hg ga ab k l m := by
  have hp := sum_parts C hg ga ab k l m positivePart positivePart_zero
  have hn := sum_parts C hg ga ab k l m negativePart negativePart_zero
  have hA := NegativeELargeA.Source.selectedA_signed C ga ab
  have hAP := NegativeELargeA.Source.selectedA_nonnegative C ga ab
    positivePart positivePart_nonneg
  have hAN := NegativeELargeA.Source.selectedA_nonnegative C ga ab
    negativePart negativePart_nonneg
  have hsP : positivePart (delta C.theta D)=0 := max_eq_right hs
  have hsN : negativePart (delta C.theta D)=magnitude C := max_eq_left (neg_nonneg.mpr hs)
  have hP : (∑i,(blocks C hg ga ab k l m i).P)=
      positiveVariation C.theta-NegativeELargeA.Source.selectedA C ga ab positivePart := by
    simpa only [Block.P,hsP,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab k l m i).N)=
      negativeVariation C.theta-NegativeELargeA.Source.selectedA C ga ab negativePart-
        magnitude C := by
    simpa only [Block.N,hsN,negativeVariation] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l m i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l m i).N_nonneg)
  have heq := variations_equal C.theta
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact ⟨ha,by linarith⟩
  · exact ⟨neg_nonneg.mpr hs,by linarith⟩
  · linarith
  · linarith
  · linarith

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (ga ab : Bool)
    (k l m : ℝ) (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta D≤0) (i : Fin 4) :
    (blocks C hg ga ab k l m i).P≤frameCap ∧
    (blocks C hg ga ab k l m i).N≤frameCap := by
  have hb := budgets hg ga ab k l m hvar ha hs
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l m j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l m j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.a_domain.1],
    by linarith [hb.negative_bound,hb.de_domain.1]⟩

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (ga ab : Bool)
    {k l m : ℝ} (hk : k≤1) (hl : k≤l) (i : Fin 3) :
    (blocks C hg ga ab k l m i.castSucc).p =
      (![k,k,min l m] : Fin 3→ℝ) i ∧
    (blocks C hg ga ab k l m i.castSucc).q =
      (![1,l,max l m] : Fin 3→ℝ) i := by
  fin_cases i <;>
    simp [blocks,Block.p,Block.q,min_eq_left hk,max_eq_right hk,
      min_eq_left hl,max_eq_right hl]

end SquaresInCircles.Eight.GlobalGA.NegativeDETD0
end
end
end
