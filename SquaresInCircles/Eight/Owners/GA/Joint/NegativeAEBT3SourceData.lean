module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3PolynomialData
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2Coefficients

/-!
# Eight squares: original joint-negative BT3/TD0 blocks and signed budgets

The TD0 error remains an independent signed argument at D. When the
actual D block is ordinary, the fifth zero block is the distinguished
separated block for the uniform concentration theorem. Otherwise D
itself is distinguished. Both choices retain the actual signed sums.
-/

section
/-!
## The three continuous BT3 weight families

The high-family inequality m > k follows from the derivative of c-kf
and its single far endpoint. The varying tilt is differentiated before
any coefficient bound is applied; no interval sampling is used.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Explicit
open Candidate Secondary
open Certificate (Row)

def highEta (z : ℝ) : ℝ := 4973/20000+(7/25)*z
def highF (z : ℝ) : ℝ := Real.cos z+highEta z*Real.sin z
def highFirst (z : ℝ) : ℝ := -(18/25)*Real.sin z+highEta z*Real.cos z
def highSecond (z : ℝ) : ℝ := -(11/25)*Real.cos z-highEta z*Real.sin z

theorem k_high (r : Row) (hr : r≠.low) (z : ℝ) :
    k r z=JointNegativeAETD2.Explicit.k .full z := by
  cases r <;> simp [k,Certificate.k,JointNegativeAETD2.Explicit.k] at *
theorem f_high (r : Row) (hr : r≠.low) (z : ℝ) : f r z=highF z := by
  cases r <;> simp [f,eta,Certificate.eta,tilt,highF,highEta] at *

theorem high_derivative (z : ℝ) : HasDerivAt highF (highFirst z) z := by
  have he := ((hasDerivAt_id z).const_mul (7/25:ℝ)).const_add (4973/20000:ℝ)
  convert (Real.hasDerivAt_cos z).add (he.mul (Real.hasDerivAt_sin z)) using 1
  · rfl
  · dsimp [highFirst,highEta]; ring
theorem highFirst_derivative (z : ℝ) : HasDerivAt highFirst (highSecond z) z := by
  have he := ((hasDerivAt_id z).const_mul (7/25:ℝ)).const_add (4973/20000:ℝ)
  convert ((Real.hasDerivAt_sin z).const_mul (-(18/25:ℝ))).add
    (he.mul (Real.hasDerivAt_cos z)) using 1
  · rfl
  · dsimp [highSecond,highEta]; ring

theorem high_eta_bounds {z : ℝ} (hz : z∈Icc (3/20:ℝ) frameCap) :
    highEta z∈Icc (0:ℝ) (8893/20000) := by
  dsimp [highEta,frameCap] at *
  constructor <;> linarith [hz.1,hz.2]

theorem high_second_negative {z : ℝ} (hz : z∈Icc (3/20:ℝ) frameCap) : highSecond z<0 := by
  have ht := transport_trig (show z∈Icc 0 frameCap from ⟨by linarith [hz.1],hz.2⟩)
  have hh := mul_nonneg (high_eta_bounds hz).1 ht.2.2.1
  dsimp [highSecond]
  linarith [ht.1]

theorem high_F_lower {z : ℝ} (hz : z∈Icc (3/20:ℝ) frameCap) : (103/100:ℝ)<highF z := by
  have hc : ConcaveOn ℝ (Icc (3/20:ℝ) frameCap) highF :=
    concave_of_deriv2 (fun x _ => high_derivative x)
      (fun x _ => highFirst_derivative x) (fun x hx => (high_second_negative hx).le)
  have h1 : (103/100:ℝ)<highF (3/20) := by
    have ht := NegativeAPositiveTD.NegativeSlope.rational_taylor (t:=3/20) (by norm_num)
    norm_num [NegativeAPositiveTD.NegativeSlope.sinLo,NegativeAPositiveTD.NegativeSlope.cosLo,NegativeAPositiveTD.NegativeSlope.sinHi,NegativeAPositiveTD.NegativeSlope.cosHi,PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
    dsimp [highF,highEta]
    nlinarith [ht.1,ht.2.2.1]
  have h2 : (103/100:ℝ)<highF frameCap := by
    have ht := NegativeAPositiveTD.NegativeSlope.rational_taylor (t:=7/10) (by norm_num)
    norm_num [NegativeAPositiveTD.NegativeSlope.sinLo,NegativeAPositiveTD.NegativeSlope.cosLo,NegativeAPositiveTD.NegativeSlope.sinHi,NegativeAPositiveTD.NegativeSlope.cosHi,PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
    dsimp [highF,highEta,frameCap]
    nlinarith [ht.1,ht.2.2.1]
  exact concave_gt_of_endpoints hc hz h1 h2

theorem high_F_upper {z : ℝ} (hz : z∈Icc (3/20:ℝ) frameCap) : highF z<219/200 := by
  have he := high_eta_bounds hz
  have he2 := pow_le_pow_left₀ he.1 he.2 2
  have hh := Real.sin_sq_add_cos_sq z
  have hs := sq_nonneg (highEta z*Real.cos z-Real.sin z)
  have hpos := high_F_lower hz
  dsimp [highF] at ⊢ hpos
  nlinarith

theorem high_first_lower {z : ℝ} (hz : z∈Icc (3/20:ℝ) frameCap) : -(1/8:ℝ)<highFirst z := by
  have hm : AntitoneOn highFirst (Icc (3/20:ℝ) frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => (highFirst_derivative x).continuousAt.continuousWithinAt)
      (fun x _ => highFirst_derivative x)
    intro x hx
    exact (high_second_negative (Ioo_subset_Icc_self hx)).le
  have hh := hm hz (show frameCap∈Icc (3/20:ℝ) frameCap by norm_num [frameCap]) hz.2
  have ht := NegativeAPositiveTD.NegativeSlope.rational_taylor (t:=7/10) (by norm_num)
  norm_num [NegativeAPositiveTD.NegativeSlope.sinLo,NegativeAPositiveTD.NegativeSlope.cosLo,NegativeAPositiveTD.NegativeSlope.sinHi,NegativeAPositiveTD.NegativeSlope.cosHi,PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
  have hend : -(1/8:ℝ)<highFirst frameCap := by
    dsimp [highFirst,highEta,frameCap]
    nlinarith [ht.2.1,ht.2.2.1]
  exact hend.trans_le hh

theorem low_F_bounds {z : ℝ} (hz : z∈Icc (0:ℝ) (3/20)) :
    1≤f .low z ∧ f .low z<21/20 := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hsin := Real.sin_ge_sub_cube hz.1
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hprod : 0≤z*((6373/20000:ℝ)-z/2-(6373/20000)*z^2/6) := by
    apply mul_nonneg hz.1
    nlinarith
  have hf : f .low z=Real.cos z+(6373/20000)*Real.sin z := by
    simp [f,tilt,eta,Certificate.eta]
  rw [hf]
  have hlo : 1≤Real.cos z+(6373/20000)*Real.sin z := by
    nlinarith
  refine ⟨hlo,?_⟩
  have hh := Real.sin_sq_add_cos_sq z
  have hs := sq_nonneg ((6373/20000:ℝ)*Real.cos z-Real.sin z)
  nlinarith

theorem c_derivative (r : Row) (z : ℝ) :
    HasDerivAt (c r) (match r with
      | .low=>-13/5+(28/5)*z
      | .middle=>-61/50+(86/25)*(z-1/4)
      | .high=>-67/100+(24/25)*(z-1/4)) z := by
  have hh := CenteredMonomialBounds.aeval_hasDerivAt (Certificate.c r) z
  refine hh.congr_deriv ?_
  cases r <;> simp [Certificate.c,Polynomial.derivative_sq] <;> ring

theorem c_antitone (r : Row) :
    AntitoneOn (c r) (Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun z _ => (c_derivative r z).continuousAt.continuousWithinAt)
    (fun z _ => c_derivative r z)
  intro z hz
  cases r <;> norm_num [Certificate.left,Certificate.right] at hz ⊢ <;> linarith [hz.2]

theorem c_ranges (r : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    c r z∈Icc (match r with | .low=>1053/1000 | .middle=>1 | .high=>7957/10000)
      (match r with | .low=>69/50 | .middle=>712/625 | .high=>1) := by
  have hab : (Certificate.left r:ℝ)≤Certificate.right r := by cases r <;> norm_num [Certificate.left,Certificate.right]
  have hlo := c_antitone r hz ⟨hab,le_rfl⟩ hz.2
  have hhi := c_antitone r ⟨le_rfl,hab⟩ hz hz.1
  cases r <;> norm_num [c,Certificate.c,Certificate.left,Certificate.right] at hlo hhi ⊢ <;> exact ⟨hlo,hhi⟩

theorem high_k_monotone : MonotoneOn (k .high) (Icc (3/20:ℝ) frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun z _ => (CenteredMonomialBounds.aeval_hasDerivAt (Certificate.k .high) z).continuousAt.continuousWithinAt)
    (fun z _ => CenteredMonomialBounds.aeval_hasDerivAt (Certificate.k .high) z)
  intro z hz
  have hh := JointNegativeAETD2.Explicit.high_k_derivative_positive (Ioo_subset_Icc_self hz)
  change 0≤aeval z (JointNegativeAETD2.Certificate.k .full).derivative
  linarith

theorem high_gap_positive {z : ℝ} (hz : z∈Icc (1/4:ℝ) frameCap) :
    0<c .high z-k .high z*highF z := by
  have hm : AntitoneOn (fun z => c .high z-k .high z*highF z) (Icc (1/4:ℝ) frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro x hx
      exact ((c_derivative .high x).sub
        ((CenteredMonomialBounds.aeval_hasDerivAt (Certificate.k .high) x).mul (high_derivative x))).continuousAt.continuousWithinAt
    · intro x hx
      exact (c_derivative .high x).sub
        ((CenteredMonomialBounds.aeval_hasDerivAt (Certificate.k .high) x).mul (high_derivative x))
    · intro x hx
      have hx' : x∈Icc (3/20:ℝ) frameCap := ⟨by linarith [hx.1],hx.2.le⟩
      have hk := JointNegativeAETD2.Explicit.high_k_ranges hx'
      have hkd := JointNegativeAETD2.Explicit.high_k_derivative_positive hx'
      have hf := high_F_lower hx'
      have hfd := high_first_lower hx'
      have hkd' : 0≤aeval x (Certificate.k .high).derivative := by
        change 0≤aeval x (JointNegativeAETD2.Certificate.k .full).derivative
        linarith
      have hk1 : aeval x (Certificate.k .high)<751/1000 := hk.2
      have hk0 : 0≤aeval x (Certificate.k .high) := by
        have h' : (13/20:ℝ)<aeval x (Certificate.k .high) := hk.1
        linarith
      have hprod := mul_nonneg hkd' (show 0≤highF x by linarith)
      have hfirst := mul_le_mul_of_nonneg_left hfd.le hk0
      have hx2 : x<7/10 := hx.2
      show -67/100+24/25*(x-1/4)-(aeval x (Certificate.k .high).derivative*highF x+
        aeval x (Certificate.k .high)*highFirst x)≤0
      linarith
  have hh := hm hz (show frameCap∈Icc (1/4:ℝ) frameCap by norm_num [frameCap]) hz.2
  have hright : (61/10000:ℝ)<c .high frameCap-k .high frameCap*highF frameCap := by
    have ht := NegativeAPositiveTD.NegativeSlope.rational_taylor (t:=7/10) (by norm_num)
    have hk := JointNegativeAETD2.Explicit.high_k_ranges
      (show frameCap∈Icc (3/20:ℝ) (7/10) by norm_num [frameCap])
    have hf := high_F_lower (show frameCap∈Icc (3/20:ℝ) frameCap by norm_num [frameCap])
    have hk2 : k .high frameCap<751/1000 := hk.2
    have hprod := mul_le_mul_of_nonneg_right hk2.le (show 0≤highF frameCap by linarith)
    have hupper : highF frameCap<10513/10000 := by
      norm_num [NegativeAPositiveTD.NegativeSlope.sinLo,NegativeAPositiveTD.NegativeSlope.cosLo,NegativeAPositiveTD.NegativeSlope.sinHi,NegativeAPositiveTD.NegativeSlope.cosHi,PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
      dsimp [highF,highEta,frameCap]
      nlinarith [ht.2.1,ht.2.2.2]
    have hcv : c .high frameCap=1-(67/100)*(7/10-1/4)+(12/25)*(7/10-1/4)^2 := by
      simp [c,Certificate.c,frameCap]
    rw [hcv]
    nlinarith
  linarith

structure Ranges (r : Row) (z : ℝ) : Prop where
  k_domain : k r z∈Icc (13/20:ℝ) (751/1000)
  c_domain : c r z∈Icc (7/10:ℝ) (7/5)
  eta_domain : eta r z∈Icc (0:ℝ) (9/20)
  f_domain : f r z∈Icc (1:ℝ) (219/200)
  k_le_m : k r z≤ m r z
  m_le_c : m r z≤c r z
  diagonal_cut : 1≤c r z → z≤3/10 ∧ k r z≤1673/2500
  later_c : 3/20≤z → c r z≤6/5

theorem ranges (r : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) : Ranges r z := by
  have hz' := frame_domain r hz
  have hcap : frameCap=7/10 := rfl
  rw [hcap] at hz'
  cases r
  · have hzl : z∈Icc (0:ℝ) (3/20) := by simpa [Certificate.left,Certificate.right] using hz
    have hc : c .low z∈Icc (1053/1000:ℝ) (69/50) := c_ranges .low hz
    have hk : k .low z=13/20 := by
      simp [k,Certificate.k,JointNegativeAETD2.Certificate.k]
    have he : eta .low z=6373/20000 := by simp [eta,Certificate.eta]
    have hf := low_F_bounds hzl
    have hf0 : 0<f .low z := by linarith [hf.1]
    refine ⟨?_,⟨by linarith [hc.1],by linarith [hc.2]⟩,?_,⟨hf.1,by linarith [hf.2]⟩,?_,?_,?_,?_⟩
    · rw [hk]; norm_num
    · rw [he]; norm_num
    · apply (le_div_iff₀ hf0).2
      rw [hk]
      linarith [hc.1,hf.2]
    · apply (div_le_iff₀ hf0).2
      nlinarith [hc.1,mul_nonneg (show 0≤c .low z by linarith [hc.1]) (sub_nonneg.mpr hf.1)]
    · intro _
      refine ⟨by linarith [hzl.2],?_⟩
      rw [hk]; norm_num
    · intro hlater
      have heq : z=3/20 := le_antisymm hzl.2 hlater
      norm_num [heq,c,Certificate.c]
  · have hzm : z∈Icc (3/20:ℝ) (1/4) := by simpa [Certificate.left,Certificate.right] using hz
    have hzf : z∈Icc (3/20:ℝ) frameCap := ⟨hzm.1,by norm_num [frameCap]; linarith [hzm.2]⟩
    have hc : c .middle z∈Icc (1:ℝ) (712/625) := c_ranges .middle hz
    have hkk := JointNegativeAETD2.Explicit.high_k_ranges (show z∈Icc (3/20:ℝ) (7/10) from ⟨hzm.1,hz'.2⟩)
    rw [← k_high .middle (by decide)] at hkk
    have hfeq := f_high .middle (by decide) z
    have hfl := high_F_lower hzf
    have hfu := high_F_upper hzf
    have hf0 : 0<f .middle z := by rw [hfeq]; linarith
    refine ⟨⟨hkk.1.le,hkk.2.le⟩,⟨by linarith [hc.1],by linarith [hc.2]⟩,?_,
      ⟨by rw [hfeq]; linarith,by rw [hfeq]; linarith⟩,?_,?_,?_,?_⟩
    · simp only [eta,Certificate.eta]
      simp
      constructor <;> linarith [hzm.1,hzm.2]
    · apply (le_div_iff₀ hf0).2
      rw [hfeq]
      have hprod := mul_le_mul hkk.2.le hfu.le (by linarith) (by norm_num : (0:ℝ)≤751/1000)
      linarith [hc.1]
    · apply (div_le_iff₀ hf0).2
      rw [hfeq]
      nlinarith [hc.1,mul_nonneg (show 0≤c .middle z by linarith [hc.1]) (show 0≤highF z-1 by linarith)]
    · intro _
      refine ⟨by linarith [hzm.2],?_⟩
      have hh := high_k_monotone hzf
        (show (1/4:ℝ)∈Icc (3/20:ℝ) frameCap by norm_num [frameCap]) hzm.2
      have hk1 : k .high (1/4)≤1673/2500 := by
        norm_num [k,Certificate.k,JointNegativeAETD2.Certificate.k]
      have hkm : k .middle z=k .high z := by
        rw [k_high .middle (by decide),k_high .high (by decide)]
      linarith
    · intro _
      linarith [hc.2]
  · have hzh : z∈Icc (1/4:ℝ) (7/10) := by simpa [Certificate.left,Certificate.right] using hz
    have hzf : z∈Icc (3/20:ℝ) frameCap := ⟨by linarith [hzh.1],by norm_num [frameCap]; linarith [hzh.2]⟩
    have hc : c .high z∈Icc (7957/10000:ℝ) 1 := c_ranges .high hz
    have hkk := JointNegativeAETD2.Explicit.high_k_ranges (show z∈Icc (3/20:ℝ) (7/10) from ⟨by linarith [hzh.1],hz'.2⟩)
    rw [← k_high .high (by decide)] at hkk
    have hfeq := f_high .high (by decide) z
    have hfl := high_F_lower hzf
    have hfu := high_F_upper hzf
    have hf0 : 0<f .high z := by rw [hfeq]; linarith
    refine ⟨⟨hkk.1.le,hkk.2.le⟩,⟨by linarith [hc.1],by linarith [hc.2]⟩,?_,
      ⟨by rw [hfeq]; linarith,by rw [hfeq]; linarith⟩,?_,?_,?_,?_⟩
    · simp only [eta,Certificate.eta]
      simp
      constructor <;> linarith [hzh.1,hzh.2]
    · apply (le_div_iff₀ hf0).2
      have hgap := high_gap_positive (show z∈Icc (1/4:ℝ) frameCap from ⟨hzh.1,hzf.2⟩)
      rw [hfeq]
      linarith
    · apply (div_le_iff₀ hf0).2
      rw [hfeq]
      nlinarith [hc.1,mul_nonneg (show 0≤c .high z by linarith [hc.1]) (show 0≤highF z-1 by linarith)]
    · intro hdiag
      have hcut : z≤1/4 := by
        have hu : 0≤(z-1/4)*(7/10-z) := mul_nonneg (by linarith [hzh.1]) (by linarith [hzh.2])
        have hcv : c .high z=1-(67/100)*(z-1/4)+(12/25)*(z-1/4)^2 := by
          simp [c,Certificate.c]
        rw [hcv] at hdiag
        nlinarith
      refine ⟨by linarith,?_⟩
      have hh := high_k_monotone hzf
        (show (1/4:ℝ)∈Icc (3/20:ℝ) frameCap by norm_num [frameCap]) hcut
      have hk1 : k .high (1/4)≤1673/2500 := by
        norm_num [k,Certificate.k,JointNegativeAETD2.Certificate.k]
      linarith
    · intro _
      linarith [hc.2]

theorem D_branch (r : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    (Certificate.diagonalD r=true → 1≤c r z) ∧
      (Certificate.diagonalD r=false → c r z≤1) := by
  have hc := c_ranges r hz
  cases r <;> simp [Certificate.diagonalD] <;> linarith [hc.1,hc.2]

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Explicit
end
end
end

section
/-!
## The owners, the secant weights and the two signed budgets

`atG` selects GA3 rather than AB2; `atH` selects EH1 rather than DE3. Three fixed arguments are
deleted from the analytic blocks; the cycle, its points and its witnesses stay as they are. When
DE3 is selected the D block is identically zero; keeping that zero summand gives the same
four-index concentration statement in all cases.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open Certificate (Row)

abbrev sec := SecantNormCurvature.secant
def aError (C : SignedCycle) (atG : Bool) : ℝ := if atG then delta C.theta G else delta C.theta A
def eError (C : SignedCycle) (atH : Bool) : ℝ := if atH then delta C.theta E else delta C.theta D
def lambdaG (atG : Bool) (r : ℝ) : ℝ := if atG then sec r else 1
def lambdaB (atG : Bool) (r : ℝ) : ℝ := if atG then 1 else sec r
def lambdaH (atH : Bool) (s : ℝ) : ℝ := if atH then sec s else 1
def lambdaD (atH : Bool) (s : ℝ) : ℝ := if atH then 1 else sec s
def owners (hg : Fin 4) (atG atH : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,2,2,if atH then 2 else 3,if atH then 1 else 0]
def weights (atG atH : Bool) (k c r s z : ℝ) : Vertex→ℝ :=
  ![k,lambdaG atG r,lambdaB atG r,tilted c z,c,lambdaD atH s,lambdaH atH s]
def pWeights (atG _atH : Bool) (k m r _s : ℝ) : Fin 4→ℝ := ![k,k,min (lambdaB atG r) m,k]
def qWeights (atG atH : Bool) (_k m r s : ℝ) : Fin 4→ℝ :=
  ![lambdaH atH s,lambdaG atG r,max (lambdaB atG r) m,1]
def blocks (C : SignedCycle) (hg : Fin 4) (atG atH : Bool) (k c r s : ℝ) : Fin 4→Block :=
  ![⟨k,lambdaH atH s,if hg=0 then 0 else delta C.theta H,if atH then 0 else delta C.theta E⟩,
    ⟨k,lambdaG atG r,if hg=0 then delta C.theta H else 0,if atG then 0 else delta C.theta G⟩,
    ⟨lambdaB atG r,tilted c (delta C.theta T),if atG then delta C.theta A else 0,delta C.theta B⟩,
    ⟨k,1,if atH then delta C.theta D else 0,0⟩]

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (atG atH : Bool) (k c r s : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg atG atH k c r s i).u+f (blocks C hg atG atH k c r s i).v))=
      (∑v,f (delta C.theta v))-f (delta C.theta T)-f (aError C atG)-f (eError C atH) := by
  cases atG <;> cases atH <;> by_cases hhg : hg=0 <;>
    simp [blocks,aError,eError,hhg,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

structure Budget (C : SignedCycle) (hg : Fin 4) (atG atH : Bool) (k c r s : ℝ) : Prop where
  total_domain : r+s∈Icc 0 frameCap
  td_domain : delta C.theta T∈Icc 0 frameCap
  positive_eq : (∑i,(blocks C hg atG atH k c r s i).P)=positiveVariation C.theta-delta C.theta T
  negative_eq : (∑i,(blocks C hg atG atH k c r s i).N)=negativeVariation C.theta-r-s
  positive_bound : (∑i,(blocks C hg atG atH k c r s i).P)≤frameCap-delta C.theta T
  negative_bound : (∑i,(blocks C hg atG atH k c r s i).N)≤frameCap-(r+s)
  balance : (∑i,(blocks C hg atG atH k c r s i).N)-
    (∑i,(blocks C hg atG atH k c r s i).P)=delta C.theta T-(r+s)

theorem budgets {C : SignedCycle} {r s : ℝ} (hg : Fin 4) (atG atH : Bool) (k c : ℝ)
    (hr : 0≤r) (hs : 0≤ s) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T) :
    Budget C hg atG atH k c r s := by
  have hp := sum_parts C hg atG atH k c r s positivePart positivePart_zero
  have hn := sum_parts C hg atG atH k c r s negativePart negativePart_zero
  have hpz : positivePart (delta C.theta T)=delta C.theta T := max_eq_left hz
  have hnz : negativePart (delta C.theta T)=0 := max_eq_right (by linarith)
  have hpa : positivePart (aError C atG)=0 := by rw [ha]; exact max_eq_right (by linarith)
  have hpe : positivePart (eError C atH)=0 := by rw [he]; exact max_eq_right (by linarith)
  have hna : negativePart (aError C atG)=r := by
    rw [ha]; simpa [negativePart] using max_eq_left hr
  have hne : negativePart (eError C atH)=s := by
    rw [he]; simpa [negativePart] using max_eq_left hs
  have hP : (∑i,(blocks C hg atG atH k c r s i).P)=positiveVariation C.theta-delta C.theta T := by
    simpa only [Block.P,positiveVariation,hpz,hpa,hpe,sub_zero] using hp
  have hN : (∑i,(blocks C hg atG atH k c r s i).N)=negativeVariation C.theta-r-s := by
    simpa only [Block.N,negativeVariation,hnz,hna,hne,sub_zero] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _=>(blocks C hg atG atH k c r s i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _=>(blocks C hg atG atH k c r s i).N_nonneg)
  have hvariation := variations_equal C.theta
  exact ⟨⟨add_nonneg hr hs,by linarith⟩,⟨hz,by linarith⟩,hP,hN,
    by linarith,by linarith,by linarith⟩

theorem block_budgets {C : SignedCycle} {r s : ℝ} (hg : Fin 4) (atG atH : Bool) (k c : ℝ)
    (hr : 0≤r) (hs : 0≤ s) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T) (i : Fin 4) :
    (blocks C hg atG atH k c r s i).P≤frameCap ∧ (blocks C hg atG atH k c r s i).N≤frameCap := by
  have hb := budgets hg atG atH k c hr hs ha he hvar hz
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _=>(blocks C hg atG atH k c r s j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _=>(blocks C hg atG atH k c r s j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound],by linarith [hb.negative_bound]⟩

theorem secant_short {x : ℝ} (hx : x∈Icc (0:ℝ) (19/50)) :
    sec x∈Icc (1:ℝ) (539/500) := by
  have ht := trig_bracket (l:=0) (u:=(19/50:ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hx
  have hc : (500/539:ℝ)<Real.cos x := by norm_num at ht; linarith [ht.2.2.1]
  have hcos : 0<Real.cos x := by linarith
  refine ⟨SecantNormCurvature.secant_ge_one hcos,?_⟩
  show 1/Real.cos x≤539/500
  apply (div_le_iff₀ hcos).2
  nlinarith

theorem lambda_bounds (atG atH : Bool) {r s : ℝ}
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) :
    lambdaG atG r∈Icc (1:ℝ) (539/500) ∧ lambdaB atG r∈Icc (1:ℝ) (539/500) ∧
      lambdaH atH s∈Icc (1:ℝ) (539/500) ∧ 0<lambdaD atH s := by
  have hA := secant_short hr
  have hE := SecantNormCurvature.secant_ge_one
    (show 0<Real.cos s by linarith [(transport_trig hs).1])
  have h1 : (1:ℝ)∈Icc (1:ℝ) (539/500) := ⟨le_rfl,by norm_num⟩
  cases atG <;> cases atH <;>
    simp only [lambdaG,lambdaB,lambdaH,lambdaD,Bool.false_eq_true,↓reduceIte]
  · exact ⟨h1,hA,h1,lt_of_lt_of_le one_pos hE⟩
  · exact ⟨h1,hA,secant_short ⟨hs.1,by linarith [hH rfl]⟩,one_pos⟩
  · exact ⟨hA,h1,h1,lt_of_lt_of_le one_pos hE⟩
  · exact ⟨hA,h1,secant_short ⟨hs.1,by linarith [hH rfl]⟩,one_pos⟩

theorem pair_domain (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (i : Fin 4) :
    0<pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i ∧
      pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i≤
        qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i ∧
      qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i≤
        (17/10)*pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i := by
  have hc := Explicit.ranges f hz
  have hl := lambda_bounds atG atH hr hs hH
  have hk : 0<Explicit.k f z := by linarith [hc.1.1]
  have hm : 0<Explicit.m f z := hk.trans_le hc.2.2.2.1
  have hcap : Explicit.m f z≤69/50 := hc.2.2.2.2.1.trans hc.2.2.2.2.2.1
  rcases i with ⟨_|_|_|_|n,hi⟩
  · show 0<Explicit.k f z ∧ Explicit.k f z≤lambdaH atH s ∧ lambdaH atH s≤(17/10)*Explicit.k f z
    exact ⟨hk,by linarith [hc.1.2,hl.2.2.1.1],by linarith [hc.1.1,hl.2.2.1.2]⟩
  · show 0<Explicit.k f z ∧ Explicit.k f z≤lambdaG atG r ∧ lambdaG atG r≤(17/10)*Explicit.k f z
    exact ⟨hk,by linarith [hc.1.2,hl.1.1],by linarith [hc.1.1,hl.1.2]⟩
  · show 0 < min (lambdaB atG r) (Explicit.m f z) ∧
      min (lambdaB atG r) (Explicit.m f z) ≤ max (lambdaB atG r) (Explicit.m f z) ∧
      max (lambdaB atG r) (Explicit.m f z) ≤ (17/10)*min (lambdaB atG r) (Explicit.m f z)
    refine ⟨lt_min (by linarith [hl.2.1.1]) hm,min_le_max,?_⟩
    rcases le_total (lambdaB atG r) (Explicit.m f z) with hh|hh
    · rw [min_eq_left hh,max_eq_right hh]
      linarith [hl.2.1.1]
    · rw [min_eq_right hh,max_eq_left hh]
      linarith [hl.2.1.2,hc.2.2.2.1,hc.1.1]
  · show 0<Explicit.k f z ∧ Explicit.k f z≤1 ∧ (1:ℝ)≤(17/10)*Explicit.k f z
    exact ⟨hk,by linarith [hc.1.2],by linarith [hc.1.1]⟩
  · omega

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (atG atH : Bool) {k c r s : ℝ}
    (hk : k≤1) (hG : k≤lambdaG atG r) (hH : k≤lambdaH atH s) (i : Fin 4) :
    (blocks C hg atG atH k c r s i).p=pWeights atG atH k (tilted c (delta C.theta T)) r s i ∧
      (blocks C hg atG atH k c r s i).q=qWeights atG atH k (tilted c (delta C.theta T)) r s i := by
  fin_cases i <;> simp [blocks,Block.p,Block.q,pWeights,qWeights,
    min_eq_left hk,max_eq_right hk,min_eq_left hG,max_eq_right hG,min_eq_left hH,max_eq_right hH]

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.Source
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open Certificate (Row)

abbrev sec := SecantNormCurvature.secant
abbrev aError := JointNegativeAETD2.Source.aError
abbrev eError := JointNegativeAETD2.Source.eError
abbrev lambdaG := JointNegativeAETD2.Source.lambdaG
abbrev lambdaB := JointNegativeAETD2.Source.lambdaB
abbrev lambdaH := JointNegativeAETD2.Source.lambdaH
abbrev lambdaD := JointNegativeAETD2.Source.lambdaD
def ordinaryD (atH : Bool) (c : ℝ) : Prop := atH=true ∧ c<1
instance (atH : Bool) (c : ℝ) : Decidable (ordinaryD atH c) := by
  unfold ordinaryD; infer_instance
def distinguished (atH : Bool) (c : ℝ) : Fin 5 := if ordinaryD atH c then 4 else 3
def owners (hg : Fin 4) (atG atH : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,3,0,if atH then 2 else 3,if atH then 1 else 0]
def weights (atG atH : Bool) (k m c r s : ℝ) : Vertex→ℝ :=
  ![k,lambdaG atG r,lambdaB atG r,m,c,lambdaD atH s,lambdaH atH s]
def pWeights (atG atH : Bool) (k m c r _s : ℝ) : Fin 5→ℝ :=
  ![k,k,min (lambdaB atG r) m,if ordinaryD atH c then c else k,k]
def qWeights (atG atH : Bool) (_k m _c r s : ℝ) : Fin 5→ℝ :=
  ![lambdaH atH s,lambdaG atG r,max (lambdaB atG r) m,1,1]
def blocks (C : SignedCycle) (hg : Fin 4) (atG atH : Bool) (k m c r s : ℝ) : Fin 5→Block :=
  ![⟨k,lambdaH atH s,if hg=0 then 0 else delta C.theta H,if atH then 0 else delta C.theta E⟩,
    ⟨k,lambdaG atG r,if hg=0 then delta C.theta H else 0,if atG then 0 else delta C.theta G⟩,
    ⟨lambdaB atG r,m,if atG then delta C.theta A else 0,0⟩,
    ⟨c,lambdaD atH s,delta C.theta T,if atH then delta C.theta D else 0⟩,
    ⟨k,1,0,0⟩]

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (atG atH : Bool) (k m c r s : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg atG atH k m c r s i).u+f (blocks C hg atG atH k m c r s i).v))=
      (∑v,f (delta C.theta v))-f (delta C.theta B)-f (aError C atG)-f (eError C atH) := by
  cases atG <;> cases atH <;> by_cases hhg : hg=0 <;>
    simp [blocks,aError,eError,JointNegativeAETD2.Source.aError,JointNegativeAETD2.Source.eError,
      hhg,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

structure Budget (C : SignedCycle) (hg : Fin 4) (atG atH : Bool) (k m c r s : ℝ) : Prop where
  total_domain : r+s∈Icc 0 frameCap
  bt_domain : delta C.theta B∈Icc 0 frameCap
  positive_eq : (∑i,(blocks C hg atG atH k m c r s i).P)=positiveVariation C.theta-delta C.theta B
  negative_eq : (∑i,(blocks C hg atG atH k m c r s i).N)=negativeVariation C.theta-r-s
  positive_bound : (∑i,(blocks C hg atG atH k m c r s i).P)≤frameCap-delta C.theta B
  negative_bound : (∑i,(blocks C hg atG atH k m c r s i).N)≤frameCap-(r+s)
  balance : (∑i,(blocks C hg atG atH k m c r s i).N)-
    (∑i,(blocks C hg atG atH k m c r s i).P)=delta C.theta B-(r+s)

theorem budgets {C : SignedCycle} {r s : ℝ} (hg : Fin 4) (atG atH : Bool) (k m c : ℝ)
    (hr : 0≤r) (hs : 0≤ s) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta B) :
    Budget C hg atG atH k m c r s := by
  have hp := sum_parts C hg atG atH k m c r s positivePart positivePart_zero
  have hn := sum_parts C hg atG atH k m c r s negativePart negativePart_zero
  have hpz : positivePart (delta C.theta B)=delta C.theta B := max_eq_left hz
  have hnz : negativePart (delta C.theta B)=0 := max_eq_right (by linarith)
  have hpa : positivePart (aError C atG)=0 := by rw [ha]; exact max_eq_right (by linarith)
  have hpe : positivePart (eError C atH)=0 := by rw [he]; exact max_eq_right (by linarith)
  have hna : negativePart (aError C atG)=r := by rw [ha]; simpa [negativePart] using max_eq_left hr
  have hne : negativePart (eError C atH)=s := by rw [he]; simpa [negativePart] using max_eq_left hs
  have hP : (∑i,(blocks C hg atG atH k m c r s i).P)=positiveVariation C.theta-delta C.theta B := by
    simpa only [Block.P,positiveVariation,hpz,hpa,hpe,sub_zero] using hp
  have hN : (∑i,(blocks C hg atG atH k m c r s i).N)=negativeVariation C.theta-r-s := by
    simpa only [Block.N,negativeVariation,hnz,hna,hne,sub_zero] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => (blocks C hg atG atH k m c r s i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => (blocks C hg atG atH k m c r s i).N_nonneg)
  have hvariation := variations_equal C.theta
  exact ⟨⟨add_nonneg hr hs,by linarith⟩,⟨hz,by linarith⟩,hP,hN,
    by linarith,by linarith,by linarith⟩

theorem block_budgets {C : SignedCycle} {r s : ℝ} (hg : Fin 4) (atG atH : Bool) (k m c : ℝ)
    (hr : 0≤r) (hs : 0≤ s) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta B) (i : Fin 5) :
    (blocks C hg atG atH k m c r s i).P≤frameCap ∧ (blocks C hg atG atH k m c r s i).N≤frameCap := by
  have hb := budgets hg atG atH k m c hr hs ha he hvar hz
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG atH k m c r s j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG atH k m c r s j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound],by linarith [hb.negative_bound]⟩

theorem pair_domain (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (i : Fin 5) :
    0<pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i ∧
      pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i≤
        qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i ∧
      qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i≤
        (17/10)*pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i := by
  have hc := Explicit.ranges f hz
  have hl := JointNegativeAETD2.Source.lambda_bounds atG atH hr hs hH
  have hk : 0<Explicit.k f z := by linarith [hc.k_domain.1]
  have hm : 0<Explicit.m f z := hk.trans_le hc.k_le_m
  have hmhi : Explicit.m f z≤7/5 := hc.m_le_c.trans hc.c_domain.2
  fin_cases i
  · simp only [pWeights,qWeights,Fin.zero_eta,Fin.isValue,Matrix.cons_val]
    exact ⟨hk,by linarith [hc.k_domain.2,hl.2.2.1.1],by linarith [hc.k_domain.1,hl.2.2.1.2]⟩
  · simp only [pWeights,qWeights,Fin.mk_one,Fin.isValue,Matrix.cons_val]
    exact ⟨hk,by linarith [hc.k_domain.2,hl.1.1],by linarith [hc.k_domain.1,hl.1.2]⟩
  · change 0 < min (lambdaB atG r) (Explicit.m f z) ∧
      min (lambdaB atG r) (Explicit.m f z) ≤ max (lambdaB atG r) (Explicit.m f z) ∧
      max (lambdaB atG r) (Explicit.m f z) ≤ (17/10)*min (lambdaB atG r) (Explicit.m f z)
    refine ⟨lt_min (by linarith [hl.2.1.1]) hm,min_le_max,?_⟩
    rcases le_total (lambdaB atG r) (Explicit.m f z) with h|h
    · rw [min_eq_left h,max_eq_right h]
      linarith [hl.2.1.1]
    · rw [min_eq_right h,max_eq_left h]
      linarith [hl.2.1.2,hc.k_domain.1,hc.k_le_m]
  · by_cases ho : ordinaryD atH (Explicit.c f z)
    · simp only [pWeights,qWeights,Fin.reduceFinMk,Matrix.cons_val,ho,↓reduceIte]
      exact ⟨by linarith [hc.c_domain.1],ho.2.le,by linarith [hc.c_domain.1]⟩
    · simp only [pWeights,qWeights,Fin.reduceFinMk,Matrix.cons_val,ho,↓reduceIte]
      exact ⟨hk,by linarith [hc.k_domain.2],by linarith [hc.k_domain.1]⟩
  · simp only [pWeights,qWeights,Fin.reduceFinMk,Matrix.cons_val]
    exact ⟨hk,by linarith [hc.k_domain.2],by linarith [hc.k_domain.1]⟩

theorem ordinary_coefficients {C : SignedCycle} {hg : Fin 4} (atG atH : Bool)
    {k m c r s : ℝ} (hk : k≤1) (hG : k≤lambdaG atG r) (hH : k≤lambdaH atH s)
    (i : Fin 5) (hi : i≠distinguished atH c) :
    (blocks C hg atG atH k m c r s i).p=pWeights atG atH k m c r s i ∧
      (blocks C hg atG atH k m c r s i).q=qWeights atG atH k m c r s i := by
  by_cases ho : ordinaryD atH c
  · have he : atH=true := ho.1
    subst atH
    fin_cases i <;>
      simp [blocks,Block.p,Block.q,pWeights,qWeights,distinguished,ho,lambdaD,
        JointNegativeAETD2.Source.lambdaD,
        min_eq_left hG,max_eq_right hG,min_eq_left hH,max_eq_right hH,
        min_eq_left ho.2.le,max_eq_right ho.2.le] at hi ⊢
  · fin_cases i <;>
      simp [blocks,Block.p,Block.q,pWeights,qWeights,distinguished,ho,
        min_eq_left hk,max_eq_right hk,min_eq_left hG,max_eq_right hG,
        min_eq_left hH,max_eq_right hH] at hi ⊢

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Source
end
end
end
