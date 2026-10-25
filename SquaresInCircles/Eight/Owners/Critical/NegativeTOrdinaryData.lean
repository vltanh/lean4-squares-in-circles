module

public import SquaresInCircles.Eight.Owners.Critical.NegativeTCurvature
public import SquaresInCircles.Eight.Owners.Critical.NegativeTGain
public import SquaresInCircles.Eight.Owners.OccupiedSignedConcentration
public import SquaresInCircles.Eight.Owners.Sole.NegativeTGrowth

/-!
# Eight squares: the three actual critical ordinary blocks with negative T

D has no ordinary angle in either negative-primary
row. H retains both HG and the original EH angle; A has its actual
single AB angle; B is mixed only for TD2. In the aligned BT3 row its
larger force coefficient is the actual secant coefficient, while its
single negative coefficient remains l.
-/

section
/-!
## Strict negative-T gain on the critical strip

For a tilt `t ∈ [1/10, 4/25]`, a negative T primary of angle `s` gains strictly: its secant charge
plus the signed ordinary envelope `lowerEnvelope` exceeds the endpoint value `V`, up to
`s = 3/10` for TD (`TD_gain`) and up to the short angle for BT (`BT_gain`). Endpoint certificates
and the curvature on the whole interval cover every negative primary. The envelope keeps the
smaller of the A and B charges when `s ≤ t`, and the uniform cost `gamma` of a positive surplus
when `s ≥ t`; the coefficients and the radius come from the same critical supporting chain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalNegativeTContinuation
open Candidate CriticalEExclusion CriticalECoefficients CriticalNegativeTGain
open CriticalNegativeTCurvature FlatTStress PositiveAngularEnvelope
open OrdinaryAngleConcavity SingleAngleConcavity

def gamma : ℝ := (109/200)*(21/20)

def lowerEnvelope (R k l c t s : ℝ) : ℝ :=
  if s≤t then min (Vnu R l k l (t-s)) (V R l c (t-s)) else -gamma*(s-t)

theorem radius_bounds {q : ℝ} (hq : q∈Icc qLow qTrial) :
    0≤Real.sqrt q ∧ qLow≤(Real.sqrt q)^2 ∧ (Real.sqrt q)^2≤qCap ∧ Real.sqrt q≤2 := by
  have hq0 : 0≤q := by norm_num [qLow] at hq; linarith [hq.1]
  have he := Real.sq_sqrt hq0
  have hcap := hq.2.trans uniform_radius_order.2.2.1.le
  refine ⟨Real.sqrt_nonneg q,by simpa only [he] using hq.1,
    by simpa only [he] using hcap,?_⟩
  norm_num [qCap] at hcap
  nlinarith [Real.sqrt_nonneg q]

private theorem r51_sub_const {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) (b : ℝ) :
    ConcaveOn ℝ s (fun x => f x-b) := by
  have h := hf.add_const (-b)
  convert h using 1

theorem TD_negative_gain {q t s : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hs : s∈Ioc 0 t) :
    V (Real.sqrt q) (L q t) (Cc q t) t<
      secantCharge (Real.sqrt q) (Cc q t) 1 s+
        min (Vnu (Real.sqrt q) (L q t) (K q t) (L q t) (t-s))
          (V (Real.sqrt q) (L q t) (Cc q t) (t-s)) := by
  have h := coefficient_bounds hq ht
  have hr := radius_bounds hq
  have ho := h.order
  have hA := CriticalEPureCharges.A_ge_B ⟨hr.1,hr.2.2.2⟩ h
  have hG := TD_endpoint hq ht
  have hconcA := TD_concave hr.1 hr.2.1 hr.2.2.1 h ho.2.1 ho.2.2.2.2.2.1 (le_refl _)
  have hconcB := TD_concave hr.1 hr.2.1 hr.2.2.1 h ho.2.2.1 ho.2.2.2.2.1 ho.2.2.1
  have hzero : secantCharge (Real.sqrt q) (Cc q t) 1 0=0 := by simp [secantCharge]
  have hleftA : 0≤pairValue (Real.sqrt q) (Cc q t) 1 (L q t) (K q t) (L q t) t 0-
      V (Real.sqrt q) (L q t) (Cc q t) t := by simpa [pairValue,hzero] using sub_nonneg.mpr hA
  have hrightA : 0<pairValue (Real.sqrt q) (Cc q t) 1 (L q t) (K q t) (L q t) t t-
      V (Real.sqrt q) (L q t) (Cc q t) t := by simpa [pairValue] using sub_pos.mpr hG
  have hleftB : 0≤pairValue (Real.sqrt q) (Cc q t) 1 (L q t) (Cc q t) (Cc q t) t 0-
      V (Real.sqrt q) (L q t) (Cc q t) t := by simp [pairValue,hzero]
  have hrightB : 0<pairValue (Real.sqrt q) (Cc q t) 1 (L q t) (Cc q t) (Cc q t) t t-
      V (Real.sqrt q) (L q t) (Cc q t) t := by simpa [pairValue] using sub_pos.mpr hG
  have hsa := ExceptionalContactCurvature.positive_of_positive_right
    (r51_sub_const hconcA (V (Real.sqrt q) (L q t) (Cc q t) t)) hs hleftA hrightA
  have hsb := ExceptionalContactCurvature.positive_of_positive_right
    (r51_sub_const hconcB (V (Real.sqrt q) (L q t) (Cc q t) t)) hs hleftB hrightB
  dsimp [pairValue] at hsa hsb
  rw [add_min]
  exact lt_min (by linarith) (by linarith)

theorem TD_positive_gain {q t s : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hs : s∈Icc t (3/10:ℝ)) :
    V (Real.sqrt q) (L q t) (Cc q t) t<
      secantCharge (Real.sqrt q) (Cc q t) 1 s-gamma*(s-t) := by
  have h := coefficient_bounds hq ht
  have hG := TD_endpoint hq ht
  have hd := TD_late_growth hq h hs
  have hlen : 0≤ s-t := sub_nonneg.mpr hs.1
  dsimp [gamma]
  nlinarith

theorem BT_negative_gain {q t s : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hs : s∈Ioc 0 CriticalNegativeTPolynomials.shortAngle) :
    V (Real.sqrt q) (L q t) (Cc q t) t<
      secantCharge (Real.sqrt q) (Cc q t) (L q t) s+
        min (Vnu (Real.sqrt q) (L q t) (K q t) (L q t) (t-s))
          (V (Real.sqrt q) (L q t) (Cc q t) (t-s)) := by
  have h := coefficient_bounds hq ht
  have hr := radius_bounds hq
  have ho := h.order
  have hA := CriticalEPureCharges.A_ge_B ⟨hr.1,hr.2.2.2⟩ h
  have hG := BT_endpoints hq ht
  have hconcA := BT_concave hr.1 hr.2.1 hr.2.2.1 h ho.2.1 ho.2.2.2.2.2.1 (le_refl _)
  have hconcB := BT_concave hr.1 hr.2.1 hr.2.2.1 h ho.2.2.1 ho.2.2.2.2.1 ho.2.2.1
  have hzero : secantCharge (Real.sqrt q) (Cc q t) (L q t) 0=0 := by simp [secantCharge]
  have hleftA : 0≤pairValue (Real.sqrt q) (Cc q t) (L q t) (L q t) (K q t) (L q t) t 0-
      V (Real.sqrt q) (L q t) (Cc q t) t := by simpa [pairValue,hzero] using sub_nonneg.mpr hA
  have hrightA : 0<pairValue (Real.sqrt q) (Cc q t) (L q t) (L q t) (K q t) (L q t) t CriticalNegativeTPolynomials.shortAngle-
      V (Real.sqrt q) (L q t) (Cc q t) t := by dsimp [pairValue]; linarith [hG.2]
  have hleftB : 0≤pairValue (Real.sqrt q) (Cc q t) (L q t) (L q t) (Cc q t) (Cc q t) t 0-
      V (Real.sqrt q) (L q t) (Cc q t) t := by simp [pairValue,hzero]
  have hrightB : 0<pairValue (Real.sqrt q) (Cc q t) (L q t) (L q t) (Cc q t) (Cc q t) t CriticalNegativeTPolynomials.shortAngle-
      V (Real.sqrt q) (L q t) (Cc q t) t := by
    simp only [pairValue,Vnu_larger]
    linarith [hG.1]
  have hsa := ExceptionalContactCurvature.positive_of_positive_right
    (r51_sub_const hconcA (V (Real.sqrt q) (L q t) (Cc q t) t)) hs hleftA hrightA
  have hsb := ExceptionalContactCurvature.positive_of_positive_right
    (r51_sub_const hconcB (V (Real.sqrt q) (L q t) (Cc q t) t)) hs hleftB hrightB
  dsimp [pairValue] at hsa hsb
  rw [add_min]
  exact lt_min (by linarith) (by linarith)

theorem TD_gain {q t s : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hs : s∈Ioc 0 (3/10:ℝ)) :
    V (Real.sqrt q) (L q t) (Cc q t) t<
      secantCharge (Real.sqrt q) (Cc q t) 1 s+
        lowerEnvelope (Real.sqrt q) (K q t) (L q t) (Cc q t) t s := by
  by_cases hst : s≤t
  · simpa [lowerEnvelope,hst] using TD_negative_gain hq ht ⟨hs.1,hst⟩
  · simpa [lowerEnvelope,hst,sub_eq_add_neg] using
      TD_positive_gain hq ht ⟨(lt_of_not_ge hst).le,hs.2⟩

theorem BT_gain {q t s : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hs : s∈Ioc 0 CriticalNegativeTPolynomials.shortAngle) :
    V (Real.sqrt q) (L q t) (Cc q t) t<
      secantCharge (Real.sqrt q) (Cc q t) (L q t) s+
        lowerEnvelope (Real.sqrt q) (K q t) (L q t) (Cc q t) t s := by
  have hst : s≤t := by dsimp [CriticalNegativeTPolynomials.shortAngle] at hs; linarith [hs.2,ht.1]
  simpa [lowerEnvelope,hst] using BT_negative_gain hq ht hs

end SquaresInCircles.Eight.CriticalNegativeTContinuation
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalNegativeTOrdinaryData
open Candidate CriticalECoefficients ExceptionalContactStress
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity CriticalNegativeTContinuation

def shortDomain (td : Bool) : Set ℝ := if td then Icc 0 (3/10) else Icc 0 (9/100)
def bWeight (td : Bool) (c s : ℝ) : ℝ := if td then c else c/Real.cos s
def tWeight (td : Bool) (c s : ℝ) : ℝ := if td then c/Real.cos s else c
def alpha (_k l _c eta _x e _s : ℝ) (_td : Bool) : Fin 3 → ℝ := ![tilt eta e,l,l]
def beta (k _l c eta x _e s : ℝ) (td : Bool) : Fin 3 → ℝ :=
  ![k*tilt eta x,k,bWeight td c s]
def small (k l c eta x e s : ℝ) (td : Bool) (i : Fin 3) : ℝ :=
  min (alpha k l c eta x e s td i) (beta k l c eta x e s td i)
def large (k l c eta x e s : ℝ) (td : Bool) (i : Fin 3) : ℝ :=
  max (alpha k l c eta x e s td i) (beta k l c eta x e s td i)
def single (td : Bool) : Fin 3 → Bool := ![false,true,!td]
def nu (k l c eta x e s : ℝ) (td : Bool) : Fin 3 → ℝ :=
  ![large k l c eta x e s td 0,l,if td then c else l]

theorem short_small {td : Bool} {s : ℝ} (hs : s∈shortDomain td) : s∈Icc 0 frameCap := by
  cases td <;> norm_num [shortDomain,frameCap] at hs ⊢ <;> exact ⟨hs.1,by linarith [hs.2]⟩

theorem b_bounds {t k l c eta s : ℝ} {td : Bool}
    (h : Bounds t k l c eta) (hs : s∈shortDomain td) :
    c≤bWeight td c s ∧ bWeight td c s≤(101/100)*c ∧
      l≤bWeight td c s ∧ bWeight td c s≤2*l ∧ bWeight td c s≤21/20 := by
  have hc : 0<c := by linarith [h.c_lower]
  have ho := h.order
  cases td
  · have hs' : s∈Icc 0 (9/100:ℝ) := by simpa [shortDomain] using hs
    have hb := trig_bracket (l := 0) (u := (9/100:ℝ))
      (by norm_num) (by linarith [Real.pi_gt_three]) hs'
    have hcos : (100/101:ℝ)<Real.cos s := by norm_num at hb; linarith [hb.2.2.1]
    have hcos0 : 0<Real.cos s := by linarith
    have hlo : c≤c/Real.cos s := (le_div_iff₀ hcos0).2
      (by nlinarith [Real.cos_le_one s])
    have hhi : c/Real.cos s≤(101/100)*c := (div_le_iff₀ hcos0).2
      (by nlinarith [mul_pos hc (show 0<Real.cos s-100/101 by linarith)])
    simp only [bWeight,Bool.false_eq_true,ite_false]
    refine ⟨hlo,hhi,ho.2.2.1.trans hlo,?_,?_⟩ <;>
      nlinarith [h.ell_c_lower,h.c_upper]
  · simp only [bWeight,ite_true]
    exact ⟨le_rfl,by linarith,ho.2.2.1,ho.2.2.2.2.1,by linarith [h.c_upper]⟩

theorem wide_data {t k l c eta x e s : ℝ} (td : Bool) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    SoleLowChargeBounds.base≤ small k l c eta x e s td 0 ∧
      large k l c eta x e s td 0∈Icc 1 (21/20:ℝ) := by
  simpa only [small,large,alpha,beta,ExceptionalContactBlocks.small,
    ExceptionalContactBlocks.large,ExceptionalContactBlocks.alpha,
    ExceptionalContactBlocks.beta,Matrix.cons_val_zero] using
      CriticalEEnvelope.wide_data h hx he (Or.inl rfl)

theorem AB_data {t k l c eta x e s : ℝ} {td : Bool}
    (h : Bounds t k l c eta) (hs : s∈shortDomain td) :
    small k l c eta x e s td 1=l ∧ large k l c eta x e s td 1=k ∧
      small k l c eta x e s td 2=l ∧ large k l c eta x e s td 2=bWeight td c s := by
  have hk := h.order.2.1
  have hb := (b_bounds h hs).2.2.1
  simp [small,large,alpha,beta,min_eq_left hk,max_eq_right hk,
    min_eq_left hb,max_eq_right hb]

theorem conditions {t k l c eta x e s : ℝ} {td : Bool} (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td) (i : Fin 3) :
    0<small k l c eta x e s td i ∧
      small k l c eta x e s td i≤nu k l c eta x e s td i ∧
      nu k l c eta x e s td i≤large k l c eta x e s td i ∧
      large k l c eta x e s td i≤2*small k l c eta x e s td i ∧
      large k l c eta x e s td i≤21/20 := by
  have ho := h.order
  obtain ⟨ha,hA,hb,hB⟩ := AB_data (x := x) (e := e) h hs
  fin_cases i <;> dsimp only [Fin.reduceFinMk]
  · have hh := wide_data (s := s) td h hx he
    have hp : 0<small k l c eta x e s td 0 := by
      dsimp [SoleLowChargeBounds.base] at hh; linarith [hh.1]
    have hn : nu k l c eta x e s td 0=large k l c eta x e s td 0 := rfl
    rw [hn]
    exact ⟨hp,min_le_max,le_rfl,by dsimp [SoleLowChargeBounds.base] at hh; linarith [hh.1,hh.2.2],
      hh.2.2⟩
  · have hn : nu k l c eta x e s td 1=l := rfl
    rw [ha,hA,hn]
    exact ⟨h.ell_pos,le_rfl,ho.2.1,ho.2.2.2.2.2.1,by linarith [h.k_upper]⟩
  · rw [hb,hB]
    have hh := b_bounds h hs
    cases td
    · have hn : nu k l c eta x e s false 2=l := rfl
      rw [hn]
      exact ⟨h.ell_pos,le_rfl,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2⟩
    · have hn : nu k l c eta x e s true 2=c := rfl
      rw [hn]
      exact ⟨h.ell_pos,ho.2.2.1,hh.1,hh.2.2.2.1,hh.2.2.2.2⟩

theorem smaller_lower {t k l c eta x e s : ℝ} {td : Bool} (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td) (i : Fin 3) :
    (2331/4000:ℝ)<small k l c eta x e s td i := by
  obtain ⟨ha,_,hb,_⟩ := AB_data (x := x) (e := e) h hs
  fin_cases i <;> dsimp only [Fin.reduceFinMk]
  · have hh := (wide_data (s := s) td h hx he).1
    dsimp [SoleLowChargeBounds.base] at hh
    linarith
  · rw [ha]; nlinarith [h.ell_c_lower,h.c_lower]
  · rw [hb]; nlinarith [h.ell_c_lower,h.c_lower]

theorem mixed_indices {td : Bool} {i : Fin 3} (hi : single td i=false) :
    i=0 ∨ (i=2 ∧ td=true) := by
  fin_cases i <;> cases td <;> simp_all [single]

theorem mixed_ratio {t k l c eta x e s : ℝ} {td : Bool} (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td)
    (i : Fin 3) (hi : single td i=false) :
    (63/100)*large k l c eta x e s td i≤ small k l c eta x e s td i := by
  rcases mixed_indices hi with rfl | ⟨rfl,rfl⟩
  · have hh := wide_data (s := s) td h hx he
    dsimp [SoleLowChargeBounds.base] at hh
    linarith [hh.1,hh.2.2]
  · obtain ⟨_,_,hb,hB⟩ := AB_data (x := x) (e := e) h hs
    rw [hb,hB]
    simpa [bWeight] using h.ell_c_lower.le

def data {R t k l c eta x e s : ℝ} {td : Bool}
    (hR : 0≤R) (hQ : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td) :
    OccupiedSignedConcentration.Data (Fin 3) where
  U := fun i => U R (small k l c eta x e s td i) (large k l c eta x e s td i)
  V := fun i => pure (single td i) R (small k l c eta x e s td i)
    (large k l c eta x e s td i) (nu k l c eta x e s td i)
  F := fun i => F (single td i) R (small k l c eta x e s td i)
    (large k l c eta x e s td i) (nu k l c eta x e s td i)
  single := single td
  U_zero := fun _ => U_zero _ _ _
  V_zero := fun _ => pure_zero _ _ _ _ _
  F_left := fun _ N => F_zero_left _ _ _ _ _ N
  F_right := fun _ P => F_zero_right _ _ _ _ _ P
  U_concave := fun i => U_concave hR hQ (conditions h hx he hs i).1
    min_le_max (conditions h hx he hs i).2.2.2.1
  V_concave := fun i => pure_concave hR hQ (conditions h hx he hs i).1
    min_le_max (conditions h hx he hs i).2.2.2.1 (conditions h hx he hs i).2.1
  F_concave_P := fun i _ hN => F_concave_P hR hQ (conditions h hx he hs i).1
    min_le_max (conditions h hx he hs i).2.2.2.1 hN
  F_concave_N := fun i _ hP => F_concave_N hR hQ (conditions h hx he hs i).1
    min_le_max (conditions h hx he hs i).2.2.2.1 (conditions h hx he hs i).2.1 hP

theorem positive_lower {R t k l c eta x e s v : ℝ} {td : Bool}
    (hR : 0≤R) (hQ : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td)
    (hv : v∈Icc 0 frameCap) (i : Fin 3) :
    -gamma*v≤U R (small k l c eta x e s td i) (large k l c eta x e s td i) v := by
  have hc := conditions h hx he hs i
  have hh := OrdinaryPositiveEnvelope.U_lower (q := large k l c eta x e s td i) hR hQ hc.1
    min_le_max hc.2.2.2.1 hv
  have hm := mul_le_mul_of_nonneg_right hc.2.2.2.2 hv.1
  dsimp [gamma]
  nlinarith

theorem negative_linear {R t k l c eta x e s v : ℝ} {td : Bool}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td)
    (hv : v∈Icc 0 frameCap) (i : Fin 3) :
    gamma*v≤pure (single td i) R (small k l c eta x e s td i)
      (large k l c eta x e s td i) (nu k l c eta x e s td i) v := by
  have hc := conditions h hx he hs i
  have hp := smaller_lower h hx he hs i
  have hratio : gamma≤(87/70)*small k l c eta x e s td i := by dsimp [gamma]; linarith
  have hscaled := mul_le_mul_of_nonneg_right hratio hv.1
  cases hm : single td i
  · have hh := SoleNegativeTGrowth.radius_chord (q := large k l c eta x e s td i)
      (ν := large k l c eta x e s td i) hR hQL hQU hc.1 min_le_max hc.2.2.2.1
      min_le_max (le_refl _) hv
    simpa [SingleAngleConcavity.pure,hm] using hscaled.trans hh
  · have hh := SoleNegativeTGrowth.radius_chord (q := large k l c eta x e s td i) hR hQL hQU
      hc.1 min_le_max hc.2.2.2.1 hc.2.1 hc.2.2.1 hv
    simpa [SingleAngleConcavity.pure,hm] using hscaled.trans hh

end SquaresInCircles.Eight.CriticalNegativeTOrdinaryData
end
end
end
