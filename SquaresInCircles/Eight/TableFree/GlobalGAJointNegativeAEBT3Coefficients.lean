module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAEBT3Polynomial

/-!
# The three continuous BT3 weight families

Uncompiled transcription of Section 2 of the BT3 scalar companion.
The high-family inequality m > k follows from the derivative of c-kf
and its single far endpoint. The varying tilt is differentiated before
any coefficient bound is applied; no interval sampling is used.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Explicit
open Candidate Secondary Certificate (Row)

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
  have hend (x : ℝ) (hx : x=3/20 ∨ x=frameCap) : (103/100:ℝ)<highF x := by
    have ht := NegativeAPositiveTD.NegativeSlope.rational_taylor
      (show x∈Icc 0 frameCap by rcases hx with rfl|rfl <;> norm_num [frameCap])
    rcases hx with rfl|rfl
    all_goals
      norm_num [NegativeAPositiveTD.NegativeSlope.sinLo,NegativeAPositiveTD.NegativeSlope.cosLo,
        PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,
        PositiveTD.Certificate.C10,PositiveTD.Certificate.C4,frameCap] at ht
      dsimp [highF,highEta,frameCap]
      linarith [ht.1,ht.2.2.1]
  exact concave_gt_of_endpoints hc hz (hend _ (Or.inl rfl)) (hend _ (Or.inr rfl))

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
  have ht := NegativeAPositiveTD.NegativeSlope.rational_taylor
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  norm_num [NegativeAPositiveTD.NegativeSlope.sinHi,NegativeAPositiveTD.NegativeSlope.cosLo,
    PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C10,
    PositiveTD.Certificate.C4,frameCap] at ht
  have hend : -(1/8:ℝ)<highFirst frameCap := by
    dsimp [highFirst,highEta,frameCap]
    linarith [ht.2.1,ht.2.2.1]
  exact hend.trans_le hh

theorem low_F_bounds {z : ℝ} (hz : z∈Icc (0:ℝ) (3/20)) :
    1≤f .low z ∧ f .low z<21/20 := by
  have hcos := cos_lower_two hz.1
  have hsin := sin_lower_three hz.1
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hprod : 0≤z*((6373/20000:ℝ)-z/2-(6373/20000)*z^2/6) := by
    apply mul_nonneg hz.1
    nlinarith
  have hlo : 1≤f .low z := by
    dsimp [f,tilt,eta,Certificate.eta]
    norm_num
    nlinarith
  refine ⟨hlo,?_⟩
  have hh := Real.sin_sq_add_cos_sq z
  have hs := sq_nonneg ((6373/20000:ℝ)*Real.cos z-Real.sin z)
  dsimp [f,tilt,eta,Certificate.eta] at hlo ⊢
  norm_num at hlo ⊢
  nlinarith

theorem c_derivative (r : Row) (z : ℝ) :
    HasDerivAt (c r) (match r with
      | .low=>-13/5+(28/5)*z
      | .middle=>-61/50+(86/25)*(z-1/4)
      | .high=>-67/100+(24/25)*(z-1/4)) z := by
  have hh := CenteredMonomialBounds.aeval_hasDerivAt (Certificate.c r) z
  cases r <;> simpa [c,Certificate.c] using hh

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
      have hprod := mul_nonneg (show 0≤aeval x (Certificate.k .high).derivative by
        change 0≤aeval x (JointNegativeAETD2.Certificate.k .full).derivative
        linarith)
        (show 0≤highF x by linarith)
      have hfirst := mul_le_mul_of_nonneg_left hfd.le
        (show 0≤k .high x by
          change 0≤JointNegativeAETD2.Explicit.k .full x
          linarith [hk.1])
      have hk' : k .high x<751/1000 := by simpa [k,Certificate.k,JointNegativeAETD2.Explicit.k] using hk.2
      norm_num [frameCap] at hx
      nlinarith
  have hh := hm hz (show frameCap∈Icc (1/4:ℝ) frameCap by norm_num [frameCap]) hz.2
  have hright : (61/10000:ℝ)<c .high frameCap-k .high frameCap*highF frameCap := by
    have ht := NegativeAPositiveTD.NegativeSlope.rational_taylor
      (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
    have hk := JointNegativeAETD2.Explicit.high_k_ranges
      (show frameCap∈Icc (3/20:ℝ) (7/10) by norm_num [frameCap])
    have hf := high_F_lower (show frameCap∈Icc (3/20:ℝ) frameCap by norm_num [frameCap])
    have hprod := mul_le_mul_of_nonneg_right hk.2.le (show 0≤highF frameCap by linarith)
    have hupper : highF frameCap<10513/10000 := by
      norm_num [NegativeAPositiveTD.NegativeSlope.sinHi,NegativeAPositiveTD.NegativeSlope.cosHi,
        PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,
        PositiveTD.Certificate.C10,PositiveTD.Certificate.C4,frameCap] at ht
      dsimp [highF,highEta,frameCap]
      linarith [ht.2.1,ht.2.2.2]
    norm_num [c,Certificate.c,frameCap] at ⊢
    change k .high frameCap*highF frameCap≤(751/1000)*highF frameCap at hprod
    nlinarith
  linarith

structure Ranges (r : Row) (z : ℝ) : Prop where
  k_domain : k r z∈Icc (13/20:ℝ) (751/1000)
  c_domain : c r z∈Icc (7/10:ℝ) (7/5)
  eta_domain : eta r z∈Icc (0:ℝ) (9/20)
  f_domain : f r z∈Icc (1:ℝ) (219/200)
  k_le_m : k r z≤m r z
  m_le_c : m r z≤c r z
  diagonal_cut : 1≤c r z → z≤3/10 ∧ k r z≤1673/2500
  later_c : 3/20≤z → c r z≤6/5

theorem ranges (r : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) : Ranges r z := by
  have hz' := frame_domain r hz
  have hc := c_ranges r hz
  have hk : k r z∈Icc (13/20:ℝ) (751/1000) := by
    cases r
    · norm_num [k,Certificate.k,JointNegativeAETD2.Certificate.k]
    · have hh := JointNegativeAETD2.Explicit.high_k_ranges
        (show z∈Icc (3/20:ℝ) (7/10) by exact ⟨hz.1,hz'.2⟩)
      exact ⟨hh.1.le,hh.2.le⟩
    · have hh := JointNegativeAETD2.Explicit.high_k_ranges
        (show z∈Icc (3/20:ℝ) (7/10) by exact ⟨by linarith [hz.1],hz'.2⟩)
      exact ⟨hh.1.le,hh.2.le⟩
  have he : eta r z∈Icc (0:ℝ) (9/20) := by
    cases r <;> norm_num [eta,Certificate.eta,Certificate.left,Certificate.right,frameCap] at * <;>
      constructor <;> linarith
  have hf : f r z∈Icc (1:ℝ) (219/200) := by
    cases r
    · have hh := low_F_bounds hz
      exact ⟨hh.1,by linarith [hh.2]⟩
    · have hh : z∈Icc (3/20:ℝ) frameCap := ⟨hz.1,hz'.2⟩
      rw [f_high .middle (by decide)]
      exact ⟨by linarith [high_F_lower hh],(high_F_upper hh).le⟩
    · have hh : z∈Icc (3/20:ℝ) frameCap := ⟨by linarith [hz.1],hz'.2⟩
      rw [f_high .high (by decide)]
      exact ⟨by linarith [high_F_lower hh],(high_F_upper hh).le⟩
  have hc' : c r z∈Icc (7/10:ℝ) (7/5) := by
    cases r <;> simp only at hc <;> constructor <;> linarith [hc.1,hc.2]
  have hkm : k r z≤m r z := by
    apply (le_div_iff₀ (show 0<f r z by linarith [hf.1])).2
    cases r
    · have hlow := low_F_bounds hz
      norm_num [k,Certificate.k,JointNegativeAETD2.Certificate.k]
      linarith [hc.1]
    · have hprod := mul_le_mul hk.2 hf.2 (by linarith [hf.1]) (by norm_num : (0:ℝ)≤751/1000)
      linarith [hc.1]
    · have hgap := high_gap_positive (show z∈Icc (1/4:ℝ) frameCap from ⟨hz.1,hz'.2⟩)
      rw [f_high .high (by decide)]
      linarith
  have hmc : m r z≤c r z := by
    apply (div_le_iff₀ (show 0<f r z by linarith [hf.1])).2
    nlinarith [hc'.1,mul_nonneg (show 0≤c r z by linarith [hc'.1]) (sub_nonneg.mpr hf.1)]
  refine ⟨hk,hc',he,hf,hkm,hmc,?_,?_⟩
  · intro hdiag
    have hcut : z≤1/4 := by
      cases r
      · linarith [hz.2]
      · exact hz.2
      · have hu : 0≤(z-1/4)*(frameCap-z) := mul_nonneg (by linarith [hz.1]) (by linarith [hz'.2])
        norm_num [c,Certificate.c,frameCap] at hdiag hu
        nlinarith
    refine ⟨by linarith,?_⟩
    cases r
    · norm_num [k,Certificate.k,JointNegativeAETD2.Certificate.k]
    all_goals
      have hh := high_k_monotone
        (show z∈Icc (3/20:ℝ) frameCap from ⟨by linarith [hz.1],hz'.2⟩)
        (show (1/4:ℝ)∈Icc (3/20:ℝ) frameCap by norm_num [frameCap]) hcut
      norm_num [k,Certificate.k,JointNegativeAETD2.Certificate.k] at hh ⊢
      linarith
  · intro hlater
    cases r
    · have heq : z=3/20 := le_antisymm hz.2 hlater
      norm_num [heq,c,Certificate.c]
    · linarith [hc.2]
    · linarith [hc.2]

theorem D_branch (r : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    (Certificate.diagonalD r=true → 1≤c r z) ∧
      (Certificate.diagonalD r=false → c r z≤1) := by
  have hc := c_ranges r hz
  cases r <;> simp [Certificate.diagonalD] <;> linarith [hc.1,hc.2]

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Explicit
