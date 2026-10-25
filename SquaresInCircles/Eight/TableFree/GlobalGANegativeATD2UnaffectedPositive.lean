module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2SecantBaseline

/-!
# Pure positive surplus in an unaffected pair

Uncompiled transcription of (27), (30)--(31) in the angle companion.
Both coefficient families and the D linear term are included. The
original secant assignment is retained; only the unaffected pair is
constant as s moves down to z.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.UnaffectedPositive
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate (Family)
open Explicit SecantBaseline

def affectedIndex (atG : Bool) : Fin 4 := if atG then 1 else 2
def p₀ (f : Family) (z : ℝ) : Fin 4→ℝ := ![k f z,k f z,min (l f z) (m f z),k f z]
def q₀ (f : Family) (z : ℝ) : Fin 4→ℝ := ![1,l f z,max (l f z) (m f z),1]

theorem zero_weights (f : Family) (atG : Bool) (z : ℝ) :
    Source.pWeights atG (k f z) (l f z) (m f z) 0=p₀ f z ∧
    Source.qWeights atG (k f z) (l f z) (m f z) 0=q₀ f z := by
  cases atG <;> simp [Source.pWeights,Source.qWeights,p₀,q₀,lambdaG,lambdaB,
    NegativeAPositiveTD.secant]

theorem unaffected_weights (f : Family) (atG : Bool) (s z : ℝ) (i : Fin 4)
    (hi : i≠affectedIndex atG) :
    Source.pWeights atG (k f z) (l f z) (m f z) s i=p₀ f z i ∧
    Source.qWeights atG (k f z) (l f z) (m f z) s i=q₀ f z i := by
  cases atG <;> fin_cases i <;>
    simp [affectedIndex,Source.pWeights,Source.qWeights,p₀,q₀,lambdaG,lambdaB] at hi ⊢

theorem zero_pair_domain (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (i : Fin 4) :
    0<p₀ f z i ∧ p₀ f z i≤q₀ f z i ∧ q₀ f z i≤2*p₀ f z i := by
  have hh := ordered_pair_domain f true hz
    (show (0:ℝ)∈Icc 0 (angleCut true) by norm_num [angleCut]) i
  rw [(zero_weights f true z).1,(zero_weights f true z).2] at hh
  exact hh

theorem zero_q_bounds (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (i : Fin 4) :
    1≤q₀ f z i ∧ q₀ f z i≤(71/50)*l f z := by
  have hb := family_basic_domain f hz
  have hllo := hb.2.2.1
  have hmhi := hb.2.2.2.2.2.2
  fin_cases i
  · show (1:ℝ)≤1 ∧ (1:ℝ)≤(71/50)*l f z
    exact ⟨le_rfl,by linarith⟩
  · show 1≤l f z ∧ l f z≤(71/50)*l f z
    exact ⟨hllo.le,by linarith⟩
  · show 1 ≤ max (l f z) (m f z) ∧ max (l f z) (m f z)≤(71/50)*l f z
    exact ⟨hllo.le.trans (le_max_left _ _),max_le (by linarith) hmhi.le⟩
  · show (1:ℝ)≤1 ∧ (1:ℝ)≤(71/50)*l f z
    exact ⟨le_rfl,by linarith⟩

theorem AB_unaffected_q_bound (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (i : Fin 4)
    (hi : i≠affectedIndex false) : q₀ f z i≤l f z := by
  have hllo := (family_basic_domain f hz).2.2.1
  fin_cases i <;> simp [affectedIndex,q₀] at hi ⊢ <;> linarith

theorem GA_slope (f : Family) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (1/4:ℝ)) :
    (897/1000)*l f z<angleSlope (l f z) (basicRatio true (k f z) (l f z) (c f z) z) s := by
  have hb := family_basic_domain f hz
  have hl : 0<l f z := by linarith [hb.2.2.1]
  have ht := trig_bracket (l:=0) (u:=(1/4:ℝ)) (by norm_num)
    (by linarith [Real.pi_gt_three]) hs
  have hcos : (121/125:ℝ)<Real.cos s := by norm_num at ht; linarith [ht.2.2.1]
  have hsin : Real.sin s<(31/125:ℝ) := by norm_num at ht; linarith [ht.2.1]
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hratio : (11/20:ℝ)≤basicRatio true (k f z) (l f z) (c f z) z := by
    dsimp [basicRatio,affected]
    exact (le_div_iff₀ hl).2 hb.2.2.2.2.1.le
  have hc := coefficient_upper (r₀:=11/20) (c₀:=121/125) (D:=7/4)
    (by norm_num) (by norm_num) (by norm_num) hratio hcos.le
    (by norm_num [qCap])
  exact slope_lower hl (by linarith) (transport_trig hsf).2.2.1 hsin.le
    (by norm_num) (by norm_num) hc.le (by norm_num)

theorem AB_ratio_after_equal (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hzcut : z≤19/50) : (4/5)*l f z< m f z := by
  cases f
  · have hz' : z∈Icc (0:ℝ) (1/5) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split] at hz
      exact hz
    have hh := low_tilted hz'
    have hl := (low_ranges hz').2.2.1
    linarith [hh.1]
  · have hz' : z∈Icc (1/5:ℝ) (7/10) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split,
        PositiveTD.Certificate.h] at hz
      exact hz
    exact high_tilted_lower_to_AB_cut ⟨hz'.1,hzcut⟩

theorem AB_slope (f : Family) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (19/50:ℝ)) (hzs : z≤ s) :
    (43/50)*l f z<angleSlope (l f z) (basicRatio false (k f z) (l f z) (c f z) z) s := by
  have hl : 0<l f z := (family_positive f hz).2.1
  have ht := trig_bracket (l:=0) (u:=(19/50:ℝ)) (by norm_num)
    (by linarith [Real.pi_gt_three]) hs
  have hcos : (116/125:ℝ)<Real.cos s := by norm_num at ht; linarith [ht.2.2.1]
  have hsin : Real.sin s<(371/1000:ℝ) := by norm_num at ht; linarith [ht.2.1]
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hratio : (4/5:ℝ)≤basicRatio false (k f z) (l f z) (c f z) z := by
    change (4/5:ℝ)≤ m f z/l f z
    exact (le_div_iff₀ hl).2 (AB_ratio_after_equal f hz (hzs.trans hs.2)).le
  have hc := coefficient_upper (r₀:=4/5) (c₀:=116/125) (D:=8/5)
    (by norm_num) (by norm_num) (by norm_num) hratio hcos.le
    (by norm_num [qCap])
  exact slope_lower hl (by linarith) (transport_trig hsf).2.2.1 hsin.le
    (by norm_num) (by norm_num) hc.le (by norm_num)

def positiveD (f : Family) (z : ℝ) (i : Fin 4) (t : ℝ) : ℝ :=
  if i=3 then -(GlobalGA.Secondary.diagonal-1/2) else PositiveSlope.Ud (p₀ f z i) (q₀ f z i) t
def curve (f : Family) (atG : Bool) (z : ℝ) (i : Fin 4) (s : ℝ) : ℝ :=
  angularBaseline atG (k f z) (l f z) (c f z) s z+
    PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2) (p₀ f z) (q₀ f z) 3 i (s-z)

theorem positive_hasDerivAt (f : Family) {z t : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (ht : t∈Icc 0 frameCap) (i : Fin 4) :
    HasDerivAt (PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2) (p₀ f z) (q₀ f z) 3 i)
      (positiveD f z i t) t := by
  by_cases hi : i=3
  · have he : PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2) (p₀ f z) (q₀ f z) 3 i=
        fun P => -(GlobalGA.Secondary.diagonal-1/2)*P := by
      funext P; simp [PositiveTD.Hybrid.positive,hi]
    have hd : positiveD f z i t=-(GlobalGA.Secondary.diagonal-1/2) := by
      simp [positiveD,hi]
    rw [he,hd]
    simpa using (hasDerivAt_id t).const_mul (-(GlobalGA.Secondary.diagonal-1/2))
  · have hp := zero_pair_domain f hz i
    have hd : positiveD f z i t=PositiveSlope.Ud (p₀ f z i) (q₀ f z i) t := by
      simp [positiveD,hi]
    rw [hd]
    convert PositiveSlope.U_hasDerivAt hp.1 (hp.1.trans_le hp.2.1) ht using 1
    funext P; simp [PositiveTD.Hybrid.positive,hi]

theorem positiveD_lower (f : Family) {z t : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (ht : t∈Icc 0 (19/50:ℝ)) (i : Fin 4) :
    -(3/5)*q₀ f z i<positiveD f z i t := by
  by_cases hi : i=3
  · simp only [positiveD,ite_eq_left hi]
    have hq := (zero_q_bounds f hz i).1
    linarith [diagonal_bounds.2]
  · simp only [positiveD,ite_eq_right hi]
    have hp := zero_pair_domain f hz i
    exact PositiveSlope.short_bound hp.1 hp.2.1 hp.2.2 ht

theorem curve_hasDerivAt (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc z (angleCut atG)) (i : Fin 4) :
    HasDerivAt (curve f atG z i)
      (angleSlope (l f z) (basicRatio atG (k f z) (l f z) (c f z) z) s+
        positiveD f z i (s-z)) s := by
  have hzf := family_frame_domain f hz
  have hss : s∈Icc 0 (angleCut atG) := ⟨hzf.1.trans hs.1,hs.2⟩
  have hsf := (angle_domain atG hss).2
  have hdiff : s-z∈Icc 0 frameCap :=
    ⟨by linarith [hs.1],by linarith [hsf.2,hzf.1]⟩
  have hbase := angularBaseline_hasDerivAt atG (k:=k f z) (c:=c f z) (z:=z)
    (family_positive f hz).2.1
    (show 0<Real.cos s by linarith [(transport_trig hsf).1])
  have hpos := (positive_hasDerivAt f hz hdiff i).comp s ((hasDerivAt_id s).sub_const z)
  rw [mul_one] at hpos
  exact hbase.add hpos

theorem curve_monotone (f : Family) (atG : Bool) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (i : Fin 4)
    (hi : i≠affectedIndex atG) : MonotoneOn (curve f atG z i) (Icc z (angleCut atG)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (curve_hasDerivAt f atG hz hs i).continuousAt.continuousWithinAt)
    (fun s hs => curve_hasDerivAt f atG hz (Ioo_subset_Icc_self hs) i)
  intro s hs
  have hzf := family_frame_domain f hz
  have hss : s∈Icc 0 (angleCut atG) := ⟨by linarith [hzf.1,hs.1],hs.2.le⟩
  have hshort := (angle_domain atG hss).1
  have hdiff : s-z∈Icc 0 (19/50:ℝ) :=
    ⟨by linarith [hs.1],by linarith [hshort.2,hzf.1]⟩
  have hpos := positiveD_lower f hz hdiff i
  have hl := (family_positive f hz).2.1
  cases atG
  · have hb := AB_slope f hz hss hs.1.le
    have hq := AB_unaffected_q_bound f hz i hi
    linarith
  · have hb := GA_slope f hz hss
    have hq := (zero_q_bounds f hz i).2
    linarith

theorem reduces_to_equal (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) (hzs : z≤ s) (i : Fin 4)
    (hi : i≠affectedIndex atG) :
    baseline atG (k f z) (l f z) (c f z) z z≤
      baseline atG (k f z) (l f z) (c f z) s z+
        PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2)
          (Source.pWeights atG (k f z) (l f z) (m f z) s)
          (Source.qWeights atG (k f z) (l f z) (m f z) s) 3 i (s-z) := by
  have hzf := family_frame_domain f hz
  have hm := curve_monotone f atG hz i hi
    (show z∈Icc z (angleCut atG) from ⟨le_rfl,hzs.trans hs.2⟩)
    (show s∈Icc z (angleCut atG) from ⟨hzs,hs.2⟩) hzs
  obtain ⟨hp,hq⟩ := unaffected_weights f atG s z i hi
  rw [baseline_eq_extension atG _ _ _ _ hzf,
    baseline_eq_extension atG _ _ _ _ (angle_domain atG hs).2]
  dsimp [curve] at hm
  simp only [sub_self,PositiveTD.Hybrid.positive,U_zero,mul_zero,ite_self,add_zero] at hm
  simpa only [PositiveTD.Hybrid.positive,hp,hq] using hm

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.UnaffectedPositive
