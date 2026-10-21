module

public import SquaresInCircles.Eight.TableFree.OrdinaryAngleConcentration
public import SquaresInCircles.Eight.TableFree.ActualOrdinaryBlocks

/-!
# Retaining the actual coefficient of a single negative ordinary angle

Uncompiled source. A one-angle anchor has its own negative coefficient,
which can be strictly smaller than the larger force coefficient. Its
negative curvature is controlled on the whole interval by the intrinsic
zero curvature. The two-angle anchors retain the existing mixed block.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SingleAngleConcavity
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryAngleConcentration ActualOrdinaryBlocks

def Vnu (R p q nu s : ℝ) : ℝ :=
  nu*(Real.cos s-1)-R*(pairNorm p q (-s)-pairNorm p q 0)

def VnuDeriv (R p q nu s : ℝ) : ℝ :=
  -nu*Real.sin s+R*normD1 p q (-s)

@[simp] theorem Vnu_zero (R p q nu : ℝ) : Vnu R p q nu 0=0 := by simp [Vnu]
@[simp] theorem Vnu_larger (R p q s : ℝ) : Vnu R p q q s=V R p q s := rfl

theorem Vnu_ge_V {R p q nu s : ℝ} (hnu : nu≤q) :
    V R p q s≤Vnu R p q nu s := by
  have hh := mul_le_mul_of_nonpos_right hnu
    (show Real.cos s-1≤0 by linarith [Real.cos_le_one s])
  dsimp [V,Vnu]
  linarith

theorem Vnu_hasDerivAt {R p q nu s : ℝ} (hp : 0<p) (hq : 0<q)
    (hs : s∈Icc 0 frameCap) : HasDerivAt (Vnu R p q nu) (VnuDeriv R p q nu s) s := by
  have hn := (pairNorm_hasDerivAt hp hq
    (by rw [abs_neg,abs_of_nonneg hs.1]; exact hs.2)).comp s (hasDerivAt_id s).neg
  have hh := (((Real.hasDerivAt_cos s).sub_const 1).const_mul nu).sub
    ((hn.sub_const (pairNorm p q 0)).const_mul R)
  convert hh using 1
  · rfl
  · dsimp [VnuDeriv]
    ring

theorem VnuDeriv_hasDerivAt {R p q nu s : ℝ} (hp : 0<p) (hq : 0<q)
    (hs : s∈Icc 0 frameCap) :
    HasDerivAt (VnuDeriv R p q nu) (curvature R p q (-s)-nu*Real.cos s) s := by
  have hn := (normD1_hasDerivAt hp hq
    (by rw [abs_neg,abs_of_nonneg hs.1]; exact hs.2)).comp s (hasDerivAt_id s).neg
  convert ((Real.hasDerivAt_sin s).const_mul (-nu)).add (hn.const_mul R) using 1
  · rfl
  · dsimp [curvature]
    ring

/-- The coefficient is only required to dominate the smaller force
coefficient. No absent second ordinary angle is introduced. -/
theorem Vnu_second_lt {R p q nu s : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hnu : p≤nu)
    (hs : s∈Icc 0 frameCap) :
    curvature R p q (-s)-nu*Real.cos s< -(7/2500)*p := by
  have hc := (curvature_constant_bounds hR hQ hp hpq hqp).1
  have hm := curvature_negative_upper hR hp (hp.trans_le hpq)
    (show -s∈Icc (-frameCap) 0 by constructor <;> linarith [hs.1,hs.2])
  have hcos := (transport_trig hs).1
  have hnucos := mul_le_mul_of_nonneg_right hnu (show 0≤Real.cos s by linarith)
  have hpcos := mul_lt_mul_of_pos_left hcos hp
  linarith

theorem Vnu_concave {R p q nu : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hnu : p≤nu) :
    ConcaveOn ℝ (Icc 0 frameCap) (Vnu R p q nu) := by
  apply concave_of_deriv2
    (fun s hs => Vnu_hasDerivAt hp (hp.trans_le hpq) hs)
    (fun s hs => VnuDeriv_hasDerivAt hp (hp.trans_le hpq) hs)
  intro s hs
  linarith [Vnu_second_lt hR hQ hp hpq hqp hnu hs]

def pure (single : Bool) (R p q nu N : ℝ) : ℝ :=
  if single then Vnu R p q nu N else V R p q N

def F (single : Bool) (R p q nu P N : ℝ) : ℝ :=
  if single then U R p q P+Vnu R p q nu N else mixedBlock R p q P N

@[simp] theorem pure_zero (single : Bool) (R p q nu : ℝ) : pure single R p q nu 0=0 := by
  cases single <;> simp [pure]
@[simp] theorem F_zero_left (single : Bool) (R p q nu N : ℝ) :
    F single R p q nu 0 N=pure single R p q nu N := by cases single <;> simp [F,pure]
@[simp] theorem F_zero_right (single : Bool) (R p q nu P : ℝ) :
    F single R p q nu P 0=U R p q P := by cases single <;> simp [F]
@[simp] theorem F_zero (single : Bool) (R p q nu : ℝ) : F single R p q nu 0 0=0 := by simp

theorem pure_concave {single : Bool} {R p q nu : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hnu : p≤nu) : ConcaveOn ℝ (Icc 0 frameCap) (pure single R p q nu) := by
  cases single
  · exact V_concave hR hQ hp hpq hqp
  · exact Vnu_concave hR hQ hp hpq hqp hnu

theorem F_concave_P {single : Bool} {R p q nu N : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hN : N∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun P => F single R p q nu P N) := by
  cases single
  · exact mixedBlock_concave_positive hR hQ hp hpq hqp hN
  · exact (U_concave hR hQ hp hpq hqp).add_const (Vnu R p q nu N)

theorem F_concave_N {single : Bool} {R p q nu P : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hnu : p≤nu) (hP : P∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (F single R p q nu P) := by
  cases single
  · exact mixedBlock_concave_negative hR hQ hp hpq hqp hP
  · exact (Vnu_concave hR hQ hp hpq hqp hnu).const_add (U R p q P)

/-- For one actual angle, its positive and negative parts cannot coexist.
The true negative coefficient is retained exactly; only its positive
coefficient is bounded below by the smaller pair coefficient. -/
theorem single_minorant {R p q nu d : ℝ} (hpnu : p≤nu)
    (hd : |d|≤frameCap) :
    F true R p q nu (positivePart d) (negativePart d)≤
      nu*psi d-R*(pairNorm p q d-pairNorm p q 0) := by
  by_cases hd0 : 0≤d
  · have hP : positivePart d=d := max_eq_left hd0
    have hN : negativePart d=0 := max_eq_right (by linarith)
    have hphi := sub_nonneg.mpr (one_le_phi ⟨hd0,(le_abs_self d).trans hd⟩)
    have hm := mul_le_mul_of_nonneg_right hpnu hphi
    rw [hP,hN,F_zero_right,psi_positive ⟨hd0,(le_abs_self d).trans hd⟩]
    dsimp [U]
    linarith
  · have hn : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hP : positivePart d=0 := max_eq_right (le_of_lt (lt_of_not_ge hd0))
    have hN : negativePart d= -d := max_eq_left hn.1
    rw [hP,hN,F_zero_left]
    have hpsi := psi_negative hn
    simp only [neg_neg] at hpsi
    simp [pure,Vnu,hpsi]

end SquaresInCircles.Eight.TableFree.SingleAngleConcavity
