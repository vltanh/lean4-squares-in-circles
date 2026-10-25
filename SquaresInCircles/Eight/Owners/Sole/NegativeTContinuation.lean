module

public import SquaresInCircles.Eight.Owners.Sole.NegativeTOrdinaryData
public import SquaresInCircles.Eight.Owners.Sole.NegativeTScalar

/-!
# Eight squares: continuous negative-primary interpolation from the 34 endpoint scalars

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
