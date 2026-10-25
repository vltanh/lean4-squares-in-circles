module

public import SquaresInCircles.Eight.TableFree.GlobalGAClippedCircle

/-!
# Sorted-circle supports at the actual common radius

Uncompiled source. The clipping is only by the sorting half-plane. Its
explicit support point is an auxiliary scalar point, not a replacement
for any source square. In particular all radius parameters below are
the unchanged common ceiling of the input cycle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ActualSortedSupport
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

theorem corner_nonneg {q : ℝ} (hq : 1/2≤q) : 0≤corner q := by
  have hh := corner_circle (by linarith : 0≤q)
  have hs := Real.sqrt_nonneg (q/2)
  dsimp [corner] at *
  nlinarith

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
    (hcorner : 0≤a+b+1) (hfg : 0≤f+g) :
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

theorem actual_support {q f g : ℝ} {P : SignedPoint}
    (hq : 0≤q) (hs : P.Sorted) (hy : 0≤P.y)
    (hc : P.Contained q) (hfg : 0≤f+g) :
    f*P.a+g*P.y≤ support q f g := by
  apply raw_support hq
  · simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hy] using hc
  · simpa [abs_of_nonneg hy] using hs.2
  · linarith [hs.1]
  · exact hfg

theorem actual_negative_support {q f g : ℝ} {P : SignedPoint}
    (hq : 0≤q) (hs : P.Sorted) (hy : P.y≤0)
    (hc : P.Contained q) (hfg : 0≤f+g) :
    f*P.a+g*(-P.y)≤ support q f g := by
  apply raw_support hq
  · simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hy] using hc
  · simpa [abs_of_nonpos hy] using hs.2
  · linarith [hs.1]
  · exact hfg

theorem support_le_full {q f g : ℝ} (hq : 0≤q) (hfg : 0≤f+g) :
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

def point {q f g : ℝ} (hq : 0≤q) (hsum : 0≤f+g) (hg : 0<g) :
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
      rw [support,if_neg hfg]
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

theorem full_gap {q f g : ℝ} (hL : qLow≤q) (hQ : q≤qCap)
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

end SquaresInCircles.Eight.TableFree.ActualSortedSupport
