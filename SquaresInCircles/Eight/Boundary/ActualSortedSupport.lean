module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Boundary.ActualOrdinaryBlocks
public import SquaresInCircles.Eight.Owners.GA.ClippedCircle
public import SquaresInCircles.Eight.Words.Core.ECharge

/-!
# Eight squares: supports on the sorted half of the disk

For a level `q` and a direction `(f, g)` with `f + g ≥ 0`, `f a + g b` is at most
`support q f g` on the states `b ≤ a`, `a + b + 1 ≥ 0` of the disk
`(a + 1/2)² + (b + 1/2)² ≤ q` (`raw_support`, and `actual_negative_support` for a sorted signed
point with `y ≤ 0`): the support is the value `(f + g) · corner q` at the diagonal point
`(corner q, corner q)` when `f ≤ g`, and the support `full q f g = √q √(f² + g²) - (f + g)/2` of
the whole disk otherwise. The disk is clipped only by the half-plane `b ≤ a`, and a point of the
circle with `b ≤ corner q ≤ a` attains the support (`point`). For `qLow ≤ q ≤ qCap`,
`1/2 < corner q < 9/10` (`corner_bounds`), the support is `9/10`-Lipschitz in `g`
(`second_lipschitz_nine_tenths`), and the full support exceeds the diagonal one by at least
`(8/25)(g - f)²` when `f, g ≥ 0` and `√(f² + g²) ≤ 307/200` (`full_gap`).
-/

section
/-!
## Ordinary blocks with the primary errors of E

The frame errors `delta C.theta` of a signed cycle form four ordinary blocks (`blocks`), as in
`ActualOrdinaryBlocks`, except that a primary error of E, on the axis `de = 3` of D–E or
`eh = 1` of E–H (`primaryDE`, `primaryEH`), leaves its block and enters the charge of E, the
pair deficit of `CoreECharge` (`charge`). For E on the core, with the total `eTotal` of the two
primary errors in `[0, frameCap]`, that charge is at least `PositiveScalarTransfer.J eTotal`
(`charge_lower`). Only the sign of the total is used: the two errors may have opposite signs,
and with `eTotal ≥ 0` the positive and the negative parts of the blocks satisfy the closed
budgets of `block_budgets`.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ActualCoreEBlocks
open Candidate PositiveAngularEnvelope ActualOrdinaryBlocks

def primaryDE (C : SignedCycle) (de : Fin 4) : ℝ :=
  if de=3 then delta C.theta D else 0
def primaryEH (C : SignedCycle) (eh : Fin 4) : ℝ :=
  if eh=1 then delta C.theta E else 0
def ordinaryDE (C : SignedCycle) (de : Fin 4) : ℝ :=
  if de=2 then delta C.theta D else 0
def ordinaryEH (C : SignedCycle) (eh : Fin 4) : ℝ :=
  if eh=0 then delta C.theta E else 0
def eTotal (C : SignedCycle) (de eh : Fin 4) : ℝ :=
  primaryDE C de+primaryEH C eh

def blocks (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t : ℝ) : Fin 4 → Block :=
  ![⟨n,1,delta C.theta H,ordinaryEH C eh⟩,
    ⟨l,k,if ab=0 then 0 else delta C.theta A,0⟩,
    ⟨l,b,if ab=0 then delta C.theta A else 0,if bt=2 then delta C.theta B else 0⟩,
    ⟨1,t,ordinaryDE C de,if td=0 then delta C.theta T else 0⟩]

def charge (C : SignedCycle) (de eh : Fin 4) : ℝ :=
  CoreECharge.pairDeficit (C.point E).a (-(C.point E).y)
    (primaryDE C de) (primaryEH C eh)

theorem block_coefficients (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t : ℝ) (i : Fin 4) :
    (blocks C ab bt td de eh n k l b t i).p=
        (ActualOrdinaryBlocks.blocks C ab bt td n k l b t i).p ∧
      (blocks C ab bt td de eh n k l b t i).q=
        (ActualOrdinaryBlocks.blocks C ab bt td n k l b t i).q := by
  fin_cases i <;> simp [blocks,ActualOrdinaryBlocks.blocks,Block.p,Block.q]

theorem primary_small {C : SignedCycle} {de eh : Fin 4}
    (hs : ∀ i,|delta C.theta i|≤frameCap) :
    |primaryDE C de|≤frameCap ∧ |primaryEH C eh|≤frameCap := by
  constructor
  · by_cases hd : de=3
    · simpa [primaryDE,hd] using hs D
    · simp [primaryDE,hd,frameCap]; norm_num
  · by_cases he : eh=1
    · simpa [primaryEH,he] using hs E
    · simp [primaryEH,he,frameCap]; norm_num

theorem ordinary_small {C : SignedCycle} {de eh : Fin 4}
    (hs : ∀ i,|delta C.theta i|≤frameCap) :
    |ordinaryDE C de|≤frameCap ∧ |ordinaryEH C eh|≤frameCap := by
  constructor
  · by_cases hd : de=2
    · simpa [ordinaryDE,hd] using hs D
    · simp [ordinaryDE,hd,frameCap]; norm_num
  · by_cases he : eh=0
    · simpa [ordinaryEH,he] using hs E
    · simp [ordinaryEH,he,frameCap]; norm_num

theorem charge_lower {C : SignedCycle} {q : ℝ} {de eh : Fin 4}
    (hC : C.Necessary q) (hcore : (C.point E).Core)
    (he : eTotal C de eh∈Icc 0 frameCap) :
    PositiveScalarTransfer.J (eTotal C de eh)≤charge C de eh := by
  have hs := primary_small (C := C) (de := de) (eh := eh)
    (fun i => hC.spread (next i) i)
  exact CoreECharge.actual_core_pair_signed (hC.sorted E) hcore hs.1 hs.2 he

theorem sum_parts (C : SignedCycle) {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (n k l b t : ℝ) (f : ℝ → ℝ) (hf0 : f 0=0) :
    (∑ i,(f (blocks C ab bt td de eh n k l b t i).u+
      f (blocks C ab bt td de eh n k l b t i).v))=
      (∑ j,f (delta C.theta j))-f (delta C.theta G)-
        (if bt=3 then f (delta C.theta B) else 0)-
        (if td=2 then f (delta C.theta T) else 0)-
        f (primaryDE C de)-f (primaryEH C eh) := by
  rcases hab with rfl | rfl <;> rcases hbt with rfl | rfl <;>
    rcases htd with rfl | rfl <;> rcases hde with rfl | rfl <;>
    rcases heh with rfl | rfl <;>
    simp [blocks,ordinaryDE,ordinaryEH,primaryDE,primaryEH,
      Fin.sum_univ_succ,H,G,A,B,T,D,E,hf0] <;> ring

/-- The budgets of the blocks when the primary errors of E have a nonnegative total, whatever
their signs: `removed` lies in `[0, frameCap]`, `eTotal` in `[0, frameCap - removed]`, the
positive parts of the blocks add up to at most `frameCap - removed - eTotal`, and the negative
parts to `removed + eTotal` plus the positive parts. -/
theorem block_budgets {C : SignedCycle} {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (n k l b t : ℝ) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G)
    (hBT : bt=3 → 0≤delta C.theta B) (hTD : td=2 → 0≤delta C.theta T)
    (he : 0≤eTotal C de eh) :
    removed C bt td∈Icc 0 frameCap ∧
      eTotal C de eh∈Icc 0 (frameCap-removed C bt td) ∧
      (∑ i,(blocks C ab bt td de eh n k l b t i).P)≤
        frameCap-removed C bt td-eTotal C de eh ∧
      (∑ i,(blocks C ab bt td de eh n k l b t i).N)=
        removed C bt td+eTotal C de eh+
          ∑ i,(blocks C ab bt td de eh n k l b t i).P := by
  let Bs := blocks C ab bt td de eh n k l b t
  have hp := sum_parts C hab hbt htd hde heh n k l b t
    positivePart positivePart_zero
  have hn := sum_parts C hab hbt htd hde heh n k l b t
    negativePart negativePart_zero
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hG
  have hNG : negativePart (delta C.theta G)=0 :=
    max_eq_right (by linarith : -delta C.theta G≤0)
  have hPB : (if bt=3 then positivePart (delta C.theta B) else 0)=
      (if bt=3 then delta C.theta B else 0) := by
    by_cases hb : bt=3
    · simp [hb,positivePart,max_eq_left (hBT hb)]
    · simp [hb]
  have hPT : (if td=2 then positivePart (delta C.theta T) else 0)=
      (if td=2 then delta C.theta T else 0) := by
    by_cases ht : td=2
    · simp [ht,positivePart,max_eq_left (hTD ht)]
    · simp [ht]
  have hNB : (if bt=3 then negativePart (delta C.theta B) else 0)=0 := by
    by_cases hb : bt=3
    · simp [hb,negativePart,max_eq_right (by linarith [hBT hb] : -delta C.theta B≤0)]
    · simp [hb]
  have hNT : (if td=2 then negativePart (delta C.theta T) else 0)=0 := by
    by_cases ht : td=2
    · simp [ht,negativePart,max_eq_right (by linarith [hTD ht] : -delta C.theta T≤0)]
    · simp [ht]
  have hd : 0≤removed C bt td := by
    have hb : 0≤(if bt=3 then delta C.theta B else 0) := by
      split_ifs with h
      · exact hBT h
      · rfl
    have ht : 0≤(if td=2 then delta C.theta T else 0) := by
      split_ifs with h
      · exact hTD h
      · rfl
    dsimp [removed]
    linarith
  have hp' : (∑ i,(Bs i).P)=positiveVariation C.theta-removed C bt td-
      positivePart (primaryDE C de)-positivePart (primaryEH C eh) := by
    change (∑ i,(positivePart (Bs i).u+positivePart (Bs i).v))=_
    rw [hp,hPG,hPB,hPT]
    dsimp [positiveVariation,removed]
    ring
  have hn' : (∑ i,(Bs i).N)=negativeVariation C.theta-
      negativePart (primaryDE C de)-negativePart (primaryEH C eh) := by
    change (∑ i,(negativePart (Bs i).u+negativePart (Bs i).v))=_
    rw [hn,hNG,hNB,hNT]
    simp [negativeVariation]
  have hde := positive_sub_negative (primaryDE C de)
  have heh := positive_sub_negative (primaryEH C eh)
  have hnd := negativePart_nonneg (primaryDE C de)
  have hnh := negativePart_nonneg (primaryEH C eh)
  have htotal := variations_equal C.theta
  have hP0 : 0≤∑ i,(Bs i).P := Finset.sum_nonneg fun i _ => (Bs i).P_nonneg
  have hbound : (∑ i,(Bs i).P)≤frameCap-removed C bt td-eTotal C de eh := by
    dsimp [eTotal]
    linarith
  refine ⟨⟨hd,by linarith⟩,⟨he,by linarith⟩,hbound,?_⟩
  dsimp [eTotal]
  linarith

end SquaresInCircles.Eight.ActualCoreEBlocks
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ActualSortedSupport
open GlobalGA PositiveAngularEnvelope

def corner (q : ℝ) : ℝ := Real.sqrt (q/2)-1/2
def full (q f g : ℝ) : ℝ := Real.sqrt q*Real.sqrt (f^2+g^2)-(f+g)/2
def diagonal (q f g : ℝ) : ℝ := (f+g)*corner q
def support (q f g : ℝ) : ℝ := if f≤g then diagonal q f g else full q f g

theorem corner_circle {q : ℝ} (hq : 0≤q) :
    2*(corner q+1/2)^2=q := by
  have hh := Real.sq_sqrt (show 0≤q/2 by positivity)
  dsimp [corner]
  nlinarith

theorem r38_corner_half_nonneg (q : ℝ) : 0≤corner q+1/2 := by
  have h : corner q+1/2=Real.sqrt (q/2) := by unfold corner; ring
  rw [h]; positivity

theorem corner_bounds {q : ℝ} (hL : qLow≤q) (hQ : q≤qCap) :
    1/2<corner q ∧ corner q<9/10 := by
  have hq : 0≤q := by norm_num [qLow] at hL; linarith
  have hh := corner_circle hq
  have hs := Real.sqrt_nonneg (q/2)
  norm_num [qLow,qCap] at hL hQ
  dsimp [corner] at *
  constructor <;> nlinarith

theorem raw_full {q a b f g : ℝ} (hq : 0≤q)
    (hc : (a+1/2)^2+(b+1/2)^2≤q) : f*a+g*b≤full q f g := by
  have hcircle : normSq (a+1/2,b+1/2)≤(Real.sqrt q)^2 := by
    rw [Real.sq_sqrt hq]
    exact hc
  have hh := dot_le_radius (v:=(f,g)) (p:=(a+1/2,b+1/2))
    (Real.sqrt_nonneg q) hcircle
  dsimp [dot,vectorLength,normSq,full] at *
  linarith

theorem raw_support {q a b f g : ℝ} (hq : 0≤q)
    (hc : (a+1/2)^2+(b+1/2)^2≤q) (hs : b≤a)
    (_hcorner : 0≤a+b+1) (hfg : 0≤f+g) :
    f*a+g*b≤ support q f g := by
  unfold support
  split_ifs with he
  · have hsum : a+b≤2*corner q := by
      have hd : 0≤2*corner q+1 := by linarith [r38_corner_half_nonneg q]
      have h1 : (a+b+1)^2≤(2*corner q+1)^2 := by
        linarith only [hc,corner_circle hq,sq_nonneg (a-b)]
      linarith only [le_of_pow_le_pow_left₀ two_ne_zero hd h1]
    have hfirst := mul_le_mul_of_nonneg_left hsum hfg
    have hsecond := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hs)
    dsimp [diagonal]
    nlinarith
  · exact raw_full hq hc

theorem actual_negative_support {q f g : ℝ} {P : SignedPoint}
    (hq : 0≤q) (hs : P.Sorted) (hy : P.y≤0)
    (hc : P.Contained q) (hfg : 0≤f+g) :
    f*P.a+g*(-P.y)≤ support q f g := by
  apply raw_support hq
  · simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hy] using hc
  · simpa [abs_of_nonpos hy] using hs.2
  · linarith [hs.1]
  · exact hfg

theorem support_le_full {q f g : ℝ} (hq : 0≤q) (_hfg : 0≤f+g) :
    support q f g≤full q f g := by
  unfold support
  split_ifs with he
  · have hh := raw_full (a:=corner q) (b:=corner q) (f:=f) (g:=g) hq
      (show (corner q+1/2)^2+(corner q+1/2)^2≤q by
        nlinarith [corner_circle hq])
    simpa only [diagonal,add_mul] using hh
  · exact le_rfl

structure Point (q f g : ℝ) where
  a : ℝ
  b : ℝ
  circle : (a+1/2)^2+(b+1/2)^2=q
  sorted : b≤a
  corners_nonneg : 0≤a+1/2 ∧ 0≤b+1/2
  primary_lower : corner q≤a
  tangent_upper : b≤corner q
  supports : support q f g=f*a+g*b

def point {q f g : ℝ} (hq : 0≤q) (_hsum : 0≤f+g) (hg : 0<g) :
    Point q f g := by
  classical
  by_cases hfg : f≤g
  · exact {
      a := corner q
      b := corner q
      circle := by linarith only [corner_circle hq]
      sorted := le_rfl
      corners_nonneg := ⟨r38_corner_half_nonneg q,r38_corner_half_nonneg q⟩
      primary_lower := le_rfl
      tangent_upper := le_rfl
      supports := by simp [support,hfg,diagonal]; ring }
  · have hf : 0<f := hg.trans (lt_of_not_ge hfg)
    let N := Real.sqrt (f^2+g^2)
    have hN : 0<N := Real.sqrt_pos.mpr (by positivity)
    have hN2 : N^2=f^2+g^2 := Real.sq_sqrt (by positivity)
    let a := Real.sqrt q*f/N-1/2
    let b := Real.sqrt q*g/N-1/2
    have ha : a+1/2=Real.sqrt q*f/N := by dsimp [a]; ring
    have hb : b+1/2=Real.sqrt q*g/N := by dsimp [b]; ring
    have ha0 : 0≤a+1/2 := by rw [ha]; positivity
    have hb0 : 0≤b+1/2 := by rw [hb]; positivity
    have hsort : b≤a := by
      dsimp [a,b]
      have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (lt_of_not_ge hfg).le (Real.sqrt_nonneg q)) hN.le
      linarith only [hh]
    have hc : (a+1/2)^2+(b+1/2)^2=q := by
      have hfg : 0<f^2+g^2 := by positivity
      rw [ha,hb,div_pow,div_pow,mul_pow,mul_pow,Real.sq_sqrt hq,hN2,← add_div,
        ← mul_add,mul_div_assoc,div_self hfg.ne',mul_one]
    have hcompare := mul_nonneg (sub_nonneg.mpr hsort)
      (show 0≤a+b+1 by linarith only [ha0,hb0])
    have hd0 : 0≤corner q+1/2 := r38_corner_half_nonneg q
    have hcc := corner_circle hq
    have hda : corner q≤a := by
      have h1 : (corner q+1/2)^2≤(a+1/2)^2 := by linarith only [hc,hcc,hcompare]
      linarith only [le_of_pow_le_pow_left₀ two_ne_zero ha0 h1]
    have hbd : b≤corner q := by
      have h1 : (b+1/2)^2≤(corner q+1/2)^2 := by linarith only [hc,hcc,hcompare]
      linarith only [le_of_pow_le_pow_left₀ two_ne_zero hd0 h1]
    have heq : support q f g=f*a+g*b := by
      rw [support,ite_eq_right hfg]
      change Real.sqrt q*N-(f+g)/2=f*a+g*b
      have key : f*(a+1/2)+g*(b+1/2)=Real.sqrt q*N := by
        rw [ha,hb]
        have h1 : f*(Real.sqrt q*f/N)+g*(Real.sqrt q*g/N)=Real.sqrt q*(f^2+g^2)/N := by ring
        rw [h1,← hN2,pow_two,mul_div_assoc,mul_div_cancel_right₀ _ hN.ne']
      linear_combination -key
    exact ⟨a,b,hc,hsort,⟨ha0,hb0⟩,hda,hbd,heq⟩

theorem second_lipschitz {q f g₁ g₂ : ℝ}
    (hq : 0≤q) (hfg₁ : 0≤f+g₁) (hfg₂ : 0≤f+g₂)
    (hg₂ : 0<g₂) (hgg : g₁≤g₂) :
    support q f g₂-support q f g₁≤corner q*(g₂-g₁) := by
  let K := point hq hfg₂ hg₂
  have hbase := raw_support (f:=f) (g:=g₁) hq K.circle.le K.sorted
    (by linarith [K.corners_nonneg.1,K.corners_nonneg.2]) hfg₁
  have hslope := mul_le_mul_of_nonneg_right K.tangent_upper (sub_nonneg.mpr hgg)
  rw [K.supports]
  nlinarith

theorem second_lipschitz_nine_tenths {q f g₁ g₂ : ℝ}
    (hL : qLow≤q) (hQ : q≤qCap)
    (hfg₁ : 0≤f+g₁) (hfg₂ : 0≤f+g₂) (hg₂ : 0<g₂) (hgg : g₁≤g₂) :
    support q f g₂-support q f g₁≤(9/10)*(g₂-g₁) := by
  have hq : 0≤q := by norm_num [qLow] at hL; linarith
  exact (second_lipschitz hq hfg₁ hfg₂ hg₂ hgg).trans
    (mul_le_mul_of_nonneg_right (corner_bounds hL hQ).2.le (sub_nonneg.mpr hgg))

theorem full_diagonal {q f g : ℝ} (hq : 0≤q) (he : f=g) (hsum : 0≤f+g) :
    full q f g=diagonal q f g := by
  have hN := Real.sqrt_nonneg (f^2+g^2)
  have hN2 := Real.sq_sqrt (show 0≤f^2+g^2 by positivity)
  have hR := Real.sqrt_nonneg q
  have hd : 0≤corner q+1/2 := r38_corner_half_nonneg q
  have hp : 0≤Real.sqrt q*Real.sqrt (f^2+g^2) := mul_nonneg hR hN
  have hq' : 0≤(f+g)*(corner q+1/2) := mul_nonneg hsum hd
  have hsq : (Real.sqrt q*Real.sqrt (f^2+g^2))^2=
      ((f+g)*(corner q+1/2))^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hq,hN2,he]
    linear_combination (-2*g^2)*corner_circle hq
  have hh : Real.sqrt q*Real.sqrt (f^2+g^2)=(f+g)*(corner q+1/2) :=
    (sq_eq_sq₀ hp hq').mp hsq
  dsimp only [full,diagonal]
  linear_combination hh

theorem full_gap {q f g : ℝ} (hL : qLow≤q) (_hQ : q≤qCap)
    (hf : 0≤f) (hg : 0≤g)
    (hN : Real.sqrt (f^2+g^2)≤307/200) :
    (8/25)*(g-f)^2≤full q f g-diagonal q f g := by
  have hq : 0≤q := by norm_num [qLow] at hL; linarith
  let A := Real.sqrt (f^2+g^2)
  let B := (f+g)/Real.sqrt 2
  have hA : 0≤A := Real.sqrt_nonneg _
  have hB : 0≤B := by dsimp [B]; positivity
  have hA2 : A^2=f^2+g^2 := Real.sq_sqrt (by positivity)
  have htwo : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have htwoPos : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hB2 : 2*B^2=(f+g)^2 := by
    dsimp only [B]
    rw [div_pow,htwo]
    ring
  have hBA : B≤A := by
    have h1 : B^2≤A^2 := by linarith [sq_nonneg (f-g)]
    exact le_of_pow_le_pow_left₀ two_ne_zero hA h1
  have hsum : A+B≤307/100 := by
    have hN' : A≤307/200 := hN
    linarith
  have hfactor : 2*(A-B)*(A+B)=(g-f)^2 := by linear_combination 2*hA2-hB2
  have hroot : (19787/10000:ℝ)≤Real.sqrt q := by
    have hL' : 19577/5000≤q := hL
    exact (Real.le_sqrt (by norm_num) hq).mpr (by norm_num; linarith)
  have hprod := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hBA)
  have hres : (8/25)*(g-f)^2≤Real.sqrt q*(A-B) := by
    have hh := mul_le_mul_of_nonneg_right hroot (sub_nonneg.mpr hBA)
    linarith
  have hcorner : Real.sqrt q/Real.sqrt 2=corner q+1/2 := by
    rw [show corner q+1/2=Real.sqrt (q/2) by unfold corner; ring,
      Real.sqrt_div' q (by norm_num : (0:ℝ)≤2)]
  have hid : full q f g-diagonal q f g=Real.sqrt q*(A-B) := by
    have hRB : Real.sqrt q*B=(f+g)*(corner q+1/2) := by
      dsimp [B]
      calc
        Real.sqrt q*((f+g)/Real.sqrt 2)=(f+g)*(Real.sqrt q/Real.sqrt 2) := by ring
        _=(f+g)*(corner q+1/2) := by rw [hcorner]
    change Real.sqrt q*A-(f+g)/2-(f+g)*corner q=Real.sqrt q*(A-B)
    linear_combination hRB
  rw [hid]
  exact hres

end SquaresInCircles.Eight.ActualSortedSupport
end
end
end
