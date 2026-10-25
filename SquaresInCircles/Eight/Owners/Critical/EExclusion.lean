module

public import SquaresInCircles.Eight.Owners.Critical.EWeightBounds
public import SquaresInCircles.Eight.Owners.Exceptional.PositiveTSupport
public import SquaresInCircles.Eight.Owners.Exceptional.ELowExclusion
public import SquaresInCircles.Eight.Owners.Exceptional.ELowEnvelope

/-!
# Eight squares: sharp exclusion of positive G error at an original positive-E contact

Every coefficient is selected from the actual
position-minimizing circle chain at the fixed geometric stationary
radius. The original points remain contained at their original common
radius. The E endpoint is nonnegative by the exact radial identity;
the G endpoint is strictly stronger. Concavity then forces the original
G error to be zero, including weak-owner ties and a nonzero EH0 error.
-/

section
/-!
## The complete critical ordinary-angle envelope

Continuous concentration covers all original signed
ordinary errors. The only surviving lower envelope is the actual pure
B charge. H retains both of its original angular arguments, so this
does not assume an aligned EH frame. All pure, same-block and separated
allocations are proved from the coefficient conditions.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.CriticalEEnvelope
open Candidate CriticalECoefficients CriticalEPureCharges
open ExceptionalContactStress ExceptionalContactBlocks PositiveAngularEnvelope
open OrdinaryAngleConcavity OrdinaryAngleConcentration SingleAngleConcavity

theorem AB_data {t k l c eta x e : ℝ} (h : Bounds t k l c eta) :
    small k l c eta x e 1=l ∧ large k l c eta x e 1=k ∧
    small k l c eta x e 2=l ∧ large k l c eta x e 2=c := by
  have ho := h.order
  simp [small,large,ExceptionalContactBlocks.alpha,ExceptionalContactBlocks.beta,min_eq_left ho.2.1,max_eq_right ho.2.1,
    min_eq_left ho.2.2.1,max_eq_right ho.2.2.1]

theorem wide_data {t k l c eta x e : ℝ} (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) {i : Fin 4} (hi : i=0 ∨ i=3) :
    SoleLowChargeBounds.base≤ small k l c eta x e i ∧
    large k l c eta x e i∈Icc 1 (21/20:ℝ) := by
  obtain ⟨hx0,hx1⟩ := h.tilt_bounds hx
  obtain ⟨he0,he1⟩ := h.tilt_bounds he
  have hkpos := h.order.1
  have hn0 := mul_le_mul_of_nonneg_left hx0 hkpos.le
  have hn1 := mul_lt_mul_of_pos_left hx1 hkpos
  have hn : k*tilt eta x≤21/20 := by nlinarith [h.k_upper]
  rcases hi with rfl | rfl
  · change SoleLowChargeBounds.base≤ min (tilt eta e) (k*tilt eta x) ∧
      max (tilt eta e) (k*tilt eta x)∈Icc 1 (21/20:ℝ)
    exact ⟨le_min (by dsimp [SoleLowChargeBounds.base]; linarith)
      (by dsimp [SoleLowChargeBounds.base]; linarith [h.k_lower]),
      he0.trans (le_max_left _ _),max_le he1.le hn⟩
  · change SoleLowChargeBounds.base≤ min 1 c ∧ max 1 c∈Icc 1 (21/20:ℝ)
    exact ⟨le_min (by norm_num [SoleLowChargeBounds.base])
      (by dsimp [SoleLowChargeBounds.base]; linarith [h.c_lower]),
      le_max_left _ _,max_le (by norm_num) (by linarith [h.c_upper])⟩

theorem coefficient_conditions {t k l c eta x e : ℝ} (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    0<small k l c eta x e i ∧ large k l c eta x e i≤2*small k l c eta x e i ∧
    large k l c eta x e i≤21/20 := by
  have ho := h.order
  have hp := small_pos ho.1 h.ell_pos (by linarith [h.c_lower])
    (by linarith [(h.tilt_bounds hx).1]) (by linarith [(h.tilt_bounds he).1]) i
  refine ⟨hp,?_⟩
  fin_cases i <;> dsimp only [Fin.reduceFinMk]
  · have hh := wide_data h hx he (Or.inl rfl)
    dsimp [SoleLowChargeBounds.base] at hh
    constructor <;> linarith [hh.1,hh.2.2]
  · obtain ⟨ha,hA,_,_⟩ := AB_data (x := x) (e := e) h
    rw [ha,hA]
    exact ⟨ho.2.2.2.2.2.1,by linarith [h.k_upper]⟩
  · obtain ⟨_,_,hb,hB⟩ := AB_data (x := x) (e := e) h
    rw [hb,hB]
    exact ⟨ho.2.2.2.2.1,by linarith [h.c_upper]⟩
  · have hh := wide_data h hx he (Or.inr rfl)
    dsimp [SoleLowChargeBounds.base] at hh
    constructor <;> linarith [hh.1,hh.2.2]

theorem pure_dominates {R t k l c eta x e : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    V R l c t≤pure (single i) R (small k l c eta x e i)
      (large k l c eta x e i) (nu k l c eta x e i) t ∧
    V R l c frameCap≤pure (single i) R (small k l c eta x e i)
      (large k l c eta x e i) (nu k l c eta x e i) frameCap := by
  have hR2 : R≤2 := by norm_num [qCap] at hQU; nlinarith
  fin_cases i <;> dsimp only [Fin.reduceFinMk]
  · have hw := wide_data h hx he (Or.inl rfl)
    exact wide_dominates hR hQL hQU hw.1 (small_le_large _ _ _ _ _ _ 0) hw.2 hw.2.2 h
  · obtain ⟨ha,hA,_,_⟩ := AB_data (x := x) (e := e) h
    rw [ha,hA]
    exact ⟨A_ge_B ⟨hR,hR2⟩ h,A_ge_B_at_cap ⟨hR,hR2⟩ h⟩
  · obtain ⟨_,_,hb,hB⟩ := AB_data (x := x) (e := e) h
    rw [hb,hB]
    exact ⟨le_rfl,le_rfl⟩
  · have hw := wide_data h hx he (Or.inr rfl)
    exact wide_dominates hR hQL hQU hw.1 (small_le_large _ _ _ _ _ _ 3) hw.2 hw.2.2 h

theorem same_block_dominates {R t k l c eta x e : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) (hi : single i=false) :
    V R l c t≤M R (small k l c eta x e i) (large k l c eta x e i) t := by
  by_cases hB : i=2
  · subst i
    obtain ⟨_,_,hb,hB⟩ := AB_data (x := x) (e := e) h
    rw [hb,hB]
    have hc : 0≤c := by linarith [h.c_lower]
    have hratio : PositiveStressCoefficients.ratio t*c≤l := by
      have hm := mul_le_mul_of_nonneg_right h.angle_upper hc
      dsimp [PositiveStressCoefficients.ratio]
      linarith [h.ell_c_lower]
    have hh := CorrelatedSameBlock.negative_surplus (R := R) hc hratio h.angle
      (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,h.angle.1⟩)
    have hid : mixedBlock R l c (frameCap-t) frameCap=M R l c t := by
      simpa only [show t+(frameCap-t)=frameCap by ring] using mixedBlock_saturated R l c t
    simpa only [sub_zero,hid] using hh
  · have hiw : i=0 ∨ i=3 := by fin_cases i <;> simp_all [single]
    have hw := wide_data h hx he hiw
    have hp := (coefficient_conditions h hx he i).1
    have hpq := small_le_large k l c eta x e i
    have hratio : large k l c eta x e i≤(3/2)*small k l c eta x e i := by
      dsimp [SoleLowChargeBounds.base] at hw
      linarith [hw.1,hw.2.2]
    have hM := M_ge_V (R := R) hp.le (hp.trans_le hpq).le hratio h.angle
    have hV := (pure_dominates hR hQL hQU h hx he i).1
    simp only [SingleAngleConcavity.pure,hi,Bool.false_eq_true,↓reduceIte] at hV
    exact hV.trans hM

theorem separated_dominates {R t k l c eta x e : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i j : Fin 4) :
    V R l c t<U R (small k l c eta x e i) (large k l c eta x e i) (frameCap-t)+
      pure (single j) R (small k l c eta x e j) (large k l c eta x e j)
        (nu k l c eta x e j) frameCap := by
  have hi := coefficient_conditions h hx he i
  have hlen : 0≤frameCap-t := sub_nonneg.mpr h.angle.2
  have hU := OrdinaryPositiveEnvelope.U_lower hR hQU hi.1 (small_le_large _ _ _ _ _ _ i) hi.2.1
    (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [h.angle.1]⟩)
  have hUscale := mul_le_mul_of_nonneg_right hi.2.2 hlen
  have hcap := (pure_dominates hR hQL hQU h hx he j).2
  have hgap := ExceptionalSmallGap.scaled_gap hR hQL hQU
    (show ExceptionalSmallGap.scale≤c by dsimp [ExceptionalSmallGap.scale]; linarith [h.c_lower])
    h.order.2.2.1 h.order.2.2.2.1 h.short
  dsimp only [ExceptionalSmallGap.scale] at hgap
  generalize frameCap=F at hU hUscale hcap hgap hlen ⊢
  linarith [hU,hUscale,hcap,hgap,hlen]

theorem ordinary_lower {R t k l c eta x e : ℝ} (P N : Fin 4 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t+∑i,P i)
    (hsingle : ∀ i,single i=true → P i=0 ∨ N i=0) :
    V R l c t≤∑i,F (single i) R (small k l c eta x e i) (large k l c eta x e i)
      (nu k l c eta x e i) (P i) (N i) := by
  apply SingleAngleConcentration.lower_from_endpoints single R (small k l c eta x e)
    (large k l c eta x e) (nu k l c eta x e) P N hR hQU
    (fun i => (coefficient_conditions h hx he i).1) (small_le_large _ _ _ _ _ _)
    (fun i => (coefficient_conditions h hx he i).2.1) (fun i => (nu_between _ _ _ _ _ _ i).1)
    hP hN h.angle hbudget hbalance hsingle
  · intro i; exact (pure_dominates hR hQL hQU h hx he i).1
  · intro i hi; exact same_block_dominates hR hQL hQU h hx he i hi
  · intro i j _; exact (separated_dominates hR hQL hQU h hx he i j).le

theorem original_increment {C : SignedCycle} {ab : Fin 4} {R t k l c eta x e : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (h : Bounds t k l c eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t) :
    V R l c t≤ExceptionalContactSupport.increment C ab R k l c eta x e := by
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab k l c eta t x e hvar hG hD htotal
  have hlow := ordinary_lower (fun i => (blocks C ab k l c eta x e i).P)
    (fun i => (blocks C ab k l c eta x e i).N) hR hQL hQU h hx he
    (fun i => (blocks C ab k l c eta x e i).P_nonneg)
    (fun i => (blocks C ab k l c eta x e i).N_nonneg) hP hN (single_parts C ab _ _ _ _ _ _)
  exact hlow.trans (sum_minorant hab ht0 (fun i => (coefficient_conditions h hx he i).1.le) ha hP hN)

end SquaresInCircles.Eight.CriticalEEnvelope
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalEExclusion
open Candidate Stationary.FiveCornerGeometry ExceptionalContactStress ExceptionalContactSupport

def K (q t : ℝ) : ℝ := CriticalEFamily.k q t (minimizingPosition q t)
def L (q t : ℝ) : ℝ := CriticalEFamily.ell q t (minimizingPosition q t)
def Cc (q t : ℝ) : ℝ := CriticalEFamily.c q t (minimizingPosition q t)
def Eta (q t : ℝ) : ℝ := CriticalEFamily.eta q (minimizingPosition q t)

theorem coefficient_bounds {q t : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    CriticalECoefficients.Bounds t (K q t) (L q t) (Cc q t) (Eta q t) := by
  exact CriticalEWeightBounds.minimizing_bounds
    (by simpa [CriticalEPolynomials.qLower,CriticalEPolynomials.qUpper,qLow,qTrial] using hq) ht

theorem scalar_endpoints {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hq : d.q∈Icc qLow qTrial) {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) :
    0≤atE (Real.sqrt d.q) (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t+
      OrdinaryAngleConcavity.V (Real.sqrt d.q) (L d.q t) (Cc d.q t) t ∧
    0<atG (Real.sqrt d.q) (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t+
      OrdinaryAngleConcavity.V (Real.sqrt d.q) (L d.q t) (Cc d.q t) t := by
  have hb := coefficient_bounds hq ht
  have hE := CriticalEFamily.minimizing_endpoint hd (CriticalEPosition.angle_mem ht)
  change 0≤atE (Real.sqrt d.q) (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t+
    OrdinaryAngleConcavity.V (Real.sqrt d.q) (L d.q t) (Cc d.q t) t at hE
  have hR := Real.sqrt_nonneg d.q
  have hR2 := Real.sq_sqrt (show 0≤d.q from le_trans (by norm_num [qLow]) hq.1)
  have hG := E_lt_G (l := L d.q t) (c := Cc d.q t) hR
    (show K d.q t∈Ico 0 1 from ⟨by linarith [hb.k_lower],by linarith [hb.k_upper]⟩)
    (hb.tilt_bounds (show t∈Icc 0 t from ⟨hb.angle.1,le_rfl⟩)).1
    (hb.contactScalar_lt hR (by rw [hR2]; exact hq.1))
  exact ⟨hE,by linarith⟩

theorem fixed_endpoints {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hq : d.q∈Icc qLow qTrial) {C : SignedCycle} {ab : Fin 4} {t : ℝ}
    (hab : ab=0 ∨ ab=2) (ht : t∈Icc (1/10:ℝ) (4/25))
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained d.q)
    (hn : C.NormalAnchors) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t) (hcontact : Contact C) :
    0≤value C ab (Real.sqrt d.q) (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t 0 ∧
    0<value C ab (Real.sqrt d.q) (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t t := by
  have hb := coefficient_bounds hq ht
  have hR := Real.sqrt_nonneg d.q
  have hR2 := Real.sq_sqrt (show 0≤d.q from le_trans (by norm_num [qLow]) hq.1)
  have hQL : qLow≤(Real.sqrt d.q)^2 := by rw [hR2]; exact hq.1
  have hQU : (Real.sqrt d.q)^2≤qCap := by rw [hR2]; exact hq.2.trans uniform_radius_order.2.2.1.le
  have hc' : ∀ i,(C.point i).Contained ((Real.sqrt d.q)^2) := by rw [hR2]; exact hc
  have hz : (0:ℝ)∈Icc 0 t := ⟨le_rfl,hb.angle.1⟩
  have ht' : t∈Icc 0 t := ⟨hb.angle.1,le_rfl⟩
  have hL0 := CriticalEEnvelope.original_increment hab hR hQL hQU hb hz ht' ha hvar hG hD htotal
  have hL1 := CriticalEEnvelope.original_increment hab hR hQL hQU hb ht' hz ha hvar hG hD htotal
  have hv0 := value_lower (k := K d.q t) (l := L d.q t) (c := Cc d.q t) hab hR
    (by linarith [hb.eta_lower] : 0≤Eta d.q t) hb.angle hz hs hc' hn ha hcontact
  have hv1 := value_lower (k := K d.q t) (l := L d.q t) (c := Cc d.q t) hab hR
    (by linarith [hb.eta_lower] : 0≤Eta d.q t) hb.angle ht' hs hc' hn ha hcontact
  rw [sub_zero,baseline_at_E hb.angle] at hv0
  rw [sub_self,baseline_at_G hb.angle] at hv1
  obtain ⟨hE,hGG⟩ := scalar_endpoints hd hq ht
  constructor <;> linarith

/-- The full original critical-strip conclusion. q is still the
original common squared radius; only a support upper bound uses d.q. -/
theorem original_G_zero {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (ht : delta C.theta G+delta C.theta D∈Icc (1/10:ℝ) (4/25))
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) : delta C.theta G=0 := by
  by_contra hne
  have hGpos : 0<delta C.theta G := lt_of_le_of_ne hG (Ne.symm hne)
  obtain ⟨t,htotal⟩ : ∃ t,delta C.theta G+delta C.theta D=t := ⟨_,rfl⟩
  have ht' : t∈Icc (1/10:ℝ) (4/25) := htotal ▸ ht
  have hb := coefficient_bounds hsharp ht'
  have hx : delta C.theta G∈Ioc 0 t := ⟨hGpos,by linarith⟩
  have hR := Real.sqrt_nonneg d.q
  have hR2 := Real.sq_sqrt (show 0≤d.q from le_trans (by norm_num [qLow]) hsharp.1)
  have hcap : d.q≤qCap := hsharp.2.trans uniform_radius_order.2.2.1.le
  have hc : ∀ i,(C.point i).Contained d.q := fun i => (hC.contained i).trans hq
  have hc' : ∀ i,(C.point i).Contained ((Real.sqrt d.q)^2) := by rw [hR2]; exact hc
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => (hc i).trans hcap
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hconc := ExceptionalContactStress.concave ab (l := L d.q t) (c := Cc d.q t) hR
    (by rw [hR2]; exact hcap)
    (show K d.q t∈Icc (431/500:ℝ) 1 by constructor <;> linarith [hb.k_lower,hb.k_upper])
    (show Eta d.q t∈Icc (1/4:ℝ) (327/1000) by
      constructor <;> linarith [hb.eta_lower,hb.eta_upper])
    hb.angle hC.sorted hcCap ha hEy
  obtain ⟨h0,h1⟩ := fixed_endpoints hd hsharp hab ht' hC.sorted hc hn ha hvar hG hD htotal
    hcontact
  have hpos := ExceptionalContactCurvature.positive_of_positive_right hconc hx h0 h1
  have hnec := ExceptionalContactStress.necessary (k := K d.q t) (l := L d.q t) (c := Cc d.q t)
    (eta := Eta d.q t) hab hR (by linarith [hb.k_lower]) hb.ell_pos.le (by linarith [hb.c_lower])
    (by linarith [hb.eta_lower]) hb.angle hG hD htotal hC.sorted hc' hn hcontact hf
  exact (not_lt_of_ge hnec) hpos

end SquaresInCircles.Eight.CriticalEExclusion

namespace SquaresInCircles.Eight.ExceptionalEComplete
open Candidate ExceptionalContactStress

/-- The entire total-angle domain is covered by the sharp critical
family and the proved rational-radius outside intervals. -/
theorem original_G_zero {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) : delta C.theta G=0 := by
  by_cases ht : delta C.theta G+delta C.theta D∈Icc (1/10:ℝ) (4/25)
  · exact CriticalEExclusion.original_G_zero hd hsharp hq hC hn hvar hab hG hD ht hEy hcontact hf
  · have hout : delta C.theta G+delta C.theta D≤1/10 ∨ 4/25≤delta C.theta G+delta C.theta D := by
      by_cases hl : delta C.theta G+delta C.theta D≤1/10
      · exact Or.inl hl
      · exact Or.inr (by by_contra! hh; exact ht ⟨(lt_of_not_ge hl).le,hh.le⟩)
    exact (ExceptionalEOutside.original_false hQL (hq.trans hsharp.2) hC hn hvar hab hG hD
      hout hEy hcontact hf).elim

end SquaresInCircles.Eight.ExceptionalEComplete
end
end
end
