module

public import SquaresInCircles.Eight.Owners.GA.DMinorant
public import SquaresInCircles.Eight.Owners.GA.Positive.TDData

/-!
# Eight squares: the positive-BT3 two-angle sorted-D scalar

The support keeps both sorting constraints, including the tangent-zero
branch. The actual TD0 error remains the first D argument throughout.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

abbrev L : ℝ := 1/6
abbrev K : ℝ := 1673/2500
abbrev Cmax : ℝ := 5821/5000
abbrev slope : ℝ := 13/20

def sortedSupport (f g : ℝ) : ℝ :=
  if f≤g then diagonalSupport f g
  else if (axial+1/2)*g≤f/2 then f*axial else fullSupport f g
def forceA (c x y : ℝ) : ℝ := c*Real.sin x+Real.cos y
def forceB (c x y : ℝ) : ℝ := c*Real.cos x+Real.sin y
def D (c x y : ℝ) : ℝ :=
  c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*GlobalGA.Secondary.diagonal-
    sortedSupport (forceA c x y) (forceB c x y)
def vstar (n : ℝ) : ℝ := V R K 1 n
def positiveTotal (x y : ℝ) : ℝ := positivePart x+positivePart y
def negativeTotal (x y : ℝ) : ℝ := negativePart x+negativePart y
def SignedDomain (x y : ℝ) : Prop :=
  positiveTotal x y≤frameCap ∧ negativeTotal x y≤frameCap

def lowK (δ : ℝ) : ℝ := 2933/5000+(1239/2500)*δ
def lowM (δ : ℝ) : ℝ := Cmax-(4437/5000)*δ
def tilted (m u : ℝ) : ℝ := m*(Real.cos u+PositiveTD.eta*Real.sin u)

theorem signed_domain_angles {x y : ℝ} (hxy : SignedDomain x y) :
    |x|≤frameCap ∧ |y|≤frameCap := by
  have hx0 : 0≤positivePart x := le_max_right _ _
  have hy0 : 0≤positivePart y := le_max_right _ _
  have hnx0 : 0≤negativePart x := le_max_right _ _
  have hny0 : 0≤negativePart y := le_max_right _ _
  have hxp : x≤positivePart x := le_max_left _ _
  have hyp : y≤positivePart y := le_max_left _ _
  have hxn : -x≤negativePart x := le_max_left _ _
  have hyn : -y≤negativePart y := le_max_left _ _
  dsimp [SignedDomain,positiveTotal,negativeTotal] at hxy
  exact ⟨abs_le.mpr ⟨by linarith [hxy.2],by linarith [hxy.1]⟩,
    abs_le.mpr ⟨by linarith [hxy.2],by linarith [hxy.1]⟩⟩

theorem signed_trig {x : ℝ} (hx : |x|≤frameCap) :
    (478/625:ℝ)<Real.cos x ∧ |Real.sin x|<6443/10000 := by
  have ha : |x|∈Icc 0 frameCap := ⟨abs_nonneg x,hx⟩
  have hh := transport_trig ha
  have hc : Real.cos |x|=Real.cos x := Real.cos_abs x
  have hs : Real.sin |x|=|Real.sin x| := by
    by_cases hx0 : 0≤x
    · rw [abs_of_nonneg hx0,abs_of_nonneg (transport_trig ⟨hx0,by simpa [abs_of_nonneg hx0] using hx⟩).2.2.1]
    · have hn : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
      have hsin : Real.sin x≤0 := by
        have hh := (transport_trig hn).2.2.1
        rw [Real.sin_neg] at hh
        linarith
      rw [abs_of_neg (lt_of_not_ge hx0),Real.sin_neg,abs_of_nonpos hsin]
  rw [hc] at hh
  exact ⟨by linarith [hh.1],by rw [← hs]; exact hh.2.2.2.1⟩

theorem force_positive {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hx : |x|≤frameCap) (hy : |y|≤frameCap) :
    0<forceA c x y ∧ 0<forceB c x y := by
  obtain ⟨hcx,hsx⟩ := signed_trig hx
  obtain ⟨hcy,hsy⟩ := signed_trig hy
  have hsxl : -(6443/10000:ℝ)<Real.sin x := (neg_lt_of_abs_lt hsx)
  have hsyl : -(6443/10000:ℝ)<Real.sin y := (neg_lt_of_abs_lt hsy)
  have hcp := mul_le_mul_of_nonneg_right hc.2 (by norm_num : (0:ℝ)≤6443/10000)
  have hsprod := mul_lt_mul_of_pos_left hsxl (by linarith [hc.1] : 0<c)
  have hcprod := mul_le_mul_of_nonneg_right hc.1 (by linarith : 0≤Real.cos x)
  dsimp [forceA,forceB,Cmax] at *
  constructor <;> nlinarith

theorem force_norm (c x y : ℝ) :
    Real.sqrt ((forceA c x y)^2+(forceB c x y)^2)=pairNorm 1 c (x+y) := by
  have he : (forceA c x y)^2+(forceB c x y)^2=1+c^2+2*c*Real.sin (x+y) := by
    dsimp [forceA,forceB]
    rw [Real.sin_add]
    nlinarith [Real.sin_sq_add_cos_sq x,Real.sin_sq_add_cos_sq y,
      congrArg (fun v : ℝ => c^2*v) (Real.sin_sq_add_cos_sq x)]
  rw [he]
  simp [pairNorm]

@[simp] theorem D_zero {c : ℝ} (hc : 1≤c) : D c 0 0=0 := by
  simp [D,forceA,forceB,sortedSupport,diagonalSupport,hc,edgeWidth,pairWidth]

theorem sortedSupport_le_clipped {f g : ℝ} (_hf : 0≤f) (_hg : 0≤g) :
    sortedSupport f g≤clippedSupport f g := by
  dsimp [sortedSupport,clippedSupport]
  split_ifs with hfg haxis
  · exact le_rfl
  · have hh := raw_full_support (a:=axial) (b:=0) (f:=f) (g:=g)
      (by nlinarith [axial_circle])
    simpa using hh
  · exact le_rfl

theorem one_angle_lower {c n : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) : vstar n≤D c 0 (-n) := by
  have hp := force_positive (x:=0) (y:=-n) hc (by norm_num [frameCap])
    (by rw [abs_neg,abs_of_nonneg hn.1]; exact hn.2)
  have hsup := sortedSupport_le_clipped hp.1.le hp.2.le
  have hminor := PositiveTD.negative_D_support_minorant
    (k:=K) (c:=c) (by norm_num [K])
    (by constructor <;> dsimp [Cmax,K] at hc ⊢ <;> linarith [hc.1,hc.2]) hn
  have hA : forceA c 0 (-n)=Real.cos (-n) := by simp [forceA]
  have hB : forceB c 0 (-n)=c+Real.sin (-n) := by simp [forceB]
  have h1 : clippedSupport 1 c=diagonalSupport 1 c := by
    simp [clippedSupport,hc.1]
  rw [hA,hB] at hsup
  unfold PositiveTD.dSupportIncrement at hminor
  rw [h1] at hminor
  dsimp only [vstar,D]
  rw [hA,hB,edgeWidth_zero]
  simp only [diagonalSupport] at hminor
  linarith

end SquaresInCircles.Eight.GlobalGA.PositiveBT3
