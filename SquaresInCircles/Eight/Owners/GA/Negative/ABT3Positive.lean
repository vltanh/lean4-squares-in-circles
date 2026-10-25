module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Angular
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3CoefficientDomain
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Concentration

/-!
# Eight squares: every pure-positive alternative reduces to equal angles

The actual coefficient assignment is fixed at z.
The low D cost .67 is paid by the absolute baseline slope; each ordinary
unaffected pair uses its short-angle derivative bound. The affected
GA and both AB coefficient orders use the exact normalized curves.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.Positive
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate (Family)
open Explicit Angular
open NegativeAPositiveTD.SecantBaseline (coefficient_upper slope_lower)

private theorem r69_high_dom {z : ℝ}
    (hz : z∈Icc (Certificate.left .high:ℝ) (Certificate.right .high:ℝ)) : z∈Icc (1/4:ℝ) (7/10) := by
  have h := hz; norm_num [Certificate.left,Certificate.right,Certificate.split] at h; exact h

def affectedIndex (atG : Bool) : Fin 4 := if atG then 1 else 2
def p₀ (f : Family) (z : ℝ) := Explicit.p f true z 0
def q₀ (f : Family) (z : ℝ) := Explicit.q f true z 0

theorem unaffected_weights (f : Family) (atG : Bool) (s z : ℝ) (i : Fin 4)
    (hi : i≠affectedIndex atG) :
    Explicit.p f atG z s i=p₀ f z i ∧ Explicit.q f atG z s i=q₀ f z i := by
  cases atG <;> fin_cases i <;>
    simp [affectedIndex,Explicit.p,Explicit.q,pWeights,qWeights,p₀,q₀,lambdaG,lambdaB,
      NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,NegativeAPositiveTD.secant] at hi ⊢

theorem zero_pair_domain (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (i : Fin 4) :
    0<p₀ f z i ∧ p₀ f z i≤q₀ f z i ∧ q₀ f z i≤2*p₀ f z i :=
  ordered_pair_domain f true hz (show (0:ℝ)∈Icc 0 (angleCut true) by
    norm_num [angleCut,NegativeAPositiveTD.Explicit.angleCut]) i

theorem zero_q_bounds (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (i : Fin 4) :
    1≤q₀ f z i ∧ q₀ f z i≤(71/50)*l f z := by
  have hb := basic_domain f hz
  have hl : 1<l f z := by linarith [hb.2.1]
  have hm : m f z<(71/50)*l f z := by linarith [hb.2.2.2.2.2.1]
  fin_cases i
  · simpa [q₀,Explicit.q,qWeights] using And.intro (le_refl (1:ℝ)) (by linarith : (1:ℝ)≤(71/50)*l f z)
  · simpa [q₀,Explicit.q,qWeights,lambdaG,NegativeAPositiveTD.lambdaG,secant,NegativeAPositiveTD.secant] using
      And.intro hl.le (by linarith : l f z≤(71/50)*l f z)
  · simp only [q₀,Explicit.q,qWeights,lambdaB,NegativeAPositiveTD.lambdaB,↓reduceIte,
      ]
    exact ⟨hl.le.trans (le_max_left _ _),max_le (by linarith) hm.le⟩
  · cases f
    · simpa [q₀,Explicit.q,qWeights] using And.intro (le_refl (1:ℝ))
        (by linarith : (1:ℝ)≤(71/50)*l .low z)
    · have hc := (high_rotation (r69_high_dom hz)).2.2
      simpa [q₀,Explicit.q,qWeights,max_eq_left hc.le] using And.intro (le_refl (1:ℝ))
        (by linarith : (1:ℝ)≤(71/50)*l .high z)

theorem AB_unaffected_q_bound (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (i : Fin 4)
    (hi : i≠affectedIndex false) : q₀ f z i≤l f z := by
  have hl := (basic_domain f hz).2.1
  fin_cases i
  · simp [q₀,Explicit.q,qWeights]
    linarith
  · simp [q₀,Explicit.q,qWeights,lambdaG,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.secant]
  · exact False.elim (hi rfl)
  · cases f
    · simp [q₀,Explicit.q,qWeights]
      linarith
    · simp [q₀,Explicit.q,qWeights,max_eq_left (high_rotation (r69_high_dom hz)).2.2.le]
      linarith

theorem GA_slope (f : Family) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) :
    (897/1000)*l f z<angleSlope (l f z) (ratio true (k f z) (l f z) (m f z)) s := by
  have hb := basic_domain f hz
  have hl : 0<l f z := by linarith [hb.2.1]
  have ht := trig_bracket (l:=0) (u:=(1/4:ℝ)) (by norm_num) (by linarith [Real.pi_gt_three]) hs
  have hcos : (121/125:ℝ)<Real.cos s := by norm_num at ht; linarith [ht.2.2.1]
  have hsin : Real.sin s<(31/125:ℝ) := by norm_num at ht; linarith [ht.2.1]
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hr : (11/20:ℝ)≤ratio true (k f z) (l f z) (m f z) :=
    (le_div_iff₀ hl).2 hb.2.2.1.le
  have hc := coefficient_upper (r₀:=11/20) (c₀:=121/125) (D:=7/4)
    (by norm_num) (by norm_num) (by norm_num) hr hcos.le (by norm_num [qCap])
  exact slope_lower hl (by linarith) (transport_trig hsf).2.2.1 hsin.le
    (by norm_num) (by norm_num) hc.le (by norm_num)

theorem AB_slope (f : Family) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (hs : s∈Icc 0 (19/50:ℝ)) :
    (43/50)*l f z<angleSlope (l f z) (ratio false (k f z) (l f z) (m f z)) s := by
  have hb := basic_domain f hz
  have hl : 0<l f z := by linarith [hb.2.1]
  have ht := trig_bracket (l:=0) (u:=(19/50:ℝ)) (by norm_num) (by linarith [Real.pi_gt_three]) hs
  have hcos : (116/125:ℝ)<Real.cos s := by norm_num at ht; linarith [ht.2.2.1]
  have hsin : Real.sin s<(371/1000:ℝ) := by norm_num at ht; linarith [ht.2.1]
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hr : (4/5:ℝ)≤ratio false (k f z) (l f z) (m f z) :=
    (le_div_iff₀ hl).2 hb.2.2.2.2.1.le
  have hc := coefficient_upper (r₀:=4/5) (c₀:=116/125) (D:=8/5)
    (by norm_num) (by norm_num) (by norm_num) hr hcos.le (by norm_num [qCap])
  exact slope_lower hl (by linarith) (transport_trig hsf).2.2.1 hsin.le
    (by norm_num) (by norm_num) hc.le (by norm_num)

def positiveD (f : Family) (z : ℝ) (i : Fin 4) (t : ℝ) : ℝ :=
  if f=.low ∧ i=3 then -(67/100) else NegativeAPositiveTD.PositiveSlope.Ud (p₀ f z i) (q₀ f z i) t
def curve (f : Family) (atG : Bool) (z : ℝ) (i : Fin 4) (s : ℝ) : ℝ :=
  extension atG (k f z) (l f z) (m f z) s z+Concentration.positive f (p₀ f z) (q₀ f z) i (s-z)

theorem positive_hasDerivAt (f : Family) {z t : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (ht : t∈Icc 0 frameCap) (i : Fin 4) :
    HasDerivAt (Concentration.positive f (p₀ f z) (q₀ f z) i) (positiveD f z i t) t := by
  have hp := zero_pair_domain f hz i
  by_cases hi : f=.low ∧ i=3
  · obtain ⟨rfl,rfl⟩ := hi
    have he : Concentration.positive .low (p₀ .low z) (q₀ .low z) 3=fun t => -(67/100)*t := by
      funext t; simp [Concentration.positive,PositiveTD.Hybrid.positive]
    have hD : positiveD .low z 3 t= -(67/100) := by simp [positiveD]
    rw [he,hD]
    simpa using (hasDerivAt_id t).const_mul (-(67/100:ℝ))
  · have hd := NegativeAPositiveTD.PositiveSlope.U_hasDerivAt hp.1 (hp.1.trans_le hp.2.1) ht
    have he : Concentration.positive f (p₀ f z) (q₀ f z) i=U R (p₀ f z i) (q₀ f z i) := by
      funext t
      cases f
      · have hi3 : i≠3 := fun h => hi ⟨rfl,h⟩
        simp [Concentration.positive,PositiveTD.Hybrid.positive,hi3]
      · simp [Concentration.positive]
    have hD : positiveD f z i t=NegativeAPositiveTD.PositiveSlope.Ud (p₀ f z i) (q₀ f z i) t := by
      simp only [positiveD,ite_eq_right hi]
    rw [he,hD]
    exact hd

theorem curve_hasDerivAt (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc z (angleCut atG)) (i : Fin 4) :
    HasDerivAt (curve f atG z i)
      (angleSlope (l f z) (ratio atG (k f z) (l f z) (m f z)) s+positiveD f z i (s-z)) s := by
  have hzf := frame_domain f hz
  have hss : s∈Icc 0 (angleCut atG) := ⟨hzf.1.trans hs.1,hs.2⟩
  have hsf := (angle_domain atG hss).2
  have hdiff : s-z∈Icc 0 frameCap := ⟨by linarith [hs.1],by linarith [hsf.2,hzf.1]⟩
  have hl : 0<l f z := by linarith [(basic_domain f hz).2.1]
  have hb := extension_hasDerivAt (k:=k f z) (m:=m f z) (z:=z) atG hl
    (show 0<Real.cos s by linarith [(transport_trig hsf).1])
  have hu := (positive_hasDerivAt f hz hdiff i).comp s ((hasDerivAt_id s).sub_const z)
  have h := hb.add hu
  rw [mul_one] at h
  exact h

theorem curve_monotone (f : Family) (atG : Bool) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (i : Fin 4)
    (hi : i≠affectedIndex atG) : MonotoneOn (curve f atG z i) (Icc z (angleCut atG)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (curve_hasDerivAt f atG hz hs i).continuousAt.continuousWithinAt)
    (fun s hs => curve_hasDerivAt f atG hz (Ioo_subset_Icc_self hs) i)
  intro s hs
  have hzf := frame_domain f hz
  have hss : s∈Icc 0 (angleCut atG) := ⟨by linarith [hzf.1,hs.1],hs.2.le⟩
  have hshort := (angle_domain atG hss).1
  have ht : s-z∈Icc 0 (19/50:ℝ) := ⟨by linarith [hs.1],by linarith [hshort.2,hzf.1]⟩
  have hl := (basic_domain f hz).2.1
  by_cases hD : f=.low ∧ i=3
  · simp only [positiveD,ite_eq_left hD]
    cases atG
    · linarith [AB_slope f hz hss]
    · linarith [GA_slope f hz hss]
  · have hp := zero_pair_domain f hz i
    have hu := NegativeAPositiveTD.PositiveSlope.short_bound hp.1 hp.2.1 hp.2.2 ht
    simp only [positiveD,ite_eq_right hD]
    cases atG
    · have hq := AB_unaffected_q_bound f hz i hi
      linarith [AB_slope f hz hss]
    · have hq := (zero_q_bounds f hz i).2
      linarith [GA_slope f hz hss]

theorem unaffected_reduces (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) (hzs : z≤ s) (i : Fin 4) (hi : i≠affectedIndex atG) :
    baseline atG (k f z) (l f z) (m f z) z z≤
      baseline atG (k f z) (l f z) (m f z) s z+
        Concentration.positive f (Explicit.p f atG z s) (Explicit.q f atG z s) i (s-z) := by
  have hm := curve_monotone f atG hz i hi ⟨le_rfl,hzs.trans hs.2⟩ ⟨hzs,hs.2⟩ hzs
  obtain ⟨hp,hq⟩ := unaffected_weights f atG s z i hi
  rw [baseline_eq_extension atG _ _ _ _ (frame_domain f hz),
    baseline_eq_extension atG _ _ _ _ (angle_domain atG hs).2]
  dsimp [curve] at hm
  simp only [sub_self,Concentration.positive_zero,add_zero] at hm
  simpa only [Concentration.positive,PositiveTD.Hybrid.positive,hp,hq] using hm

theorem affected_reduces (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) (hzs : z≤ s) :
    baseline atG (k f z) (l f z) (m f z) z z≤
      baseline atG (k f z) (l f z) (m f z) s z+
        Concentration.positive f (Explicit.p f atG z s) (Explicit.q f atG z s) (affectedIndex atG) (s-z) := by
  have hb := basic_domain f hz
  have hl : 0<l f z := by linarith [hb.2.1]
  have hzf := frame_domain f hz
  have hsf := (angle_domain atG hs).2
  cases atG
  · have hr : m f z/l f z∈Icc (4/5:ℝ) (71/50:ℝ) :=
      ⟨(le_div_iff₀ hl).2 hb.2.2.2.2.1.le,(div_le_iff₀ hl).2 (by linarith [hb.2.2.2.2.2.1])⟩
    have hm := NegativeAPositiveTD.AffectedPositive.AB_min_monotone hr ⟨hzf.1,hzs.trans hs.2⟩
      ⟨le_rfl,hzs.trans hs.2⟩ ⟨hzs,hs.2⟩ hzs
    have hez := AB_positive_identity (k:=k f z) (m:=m f z) (z:=z) hl hzf ⟨hzf.1,le_rfl⟩
    have hes := AB_positive_identity (k:=k f z) (m:=m f z) (z:=z) hl hsf ⟨hzf.1,hzs⟩
    simp only at hm
    have hmul := mul_le_mul_of_nonneg_left hm hl.le
    simp only [sub_self,U_zero,add_zero] at hez
    cases f <;> simp only [Concentration.positive,PositiveTD.Hybrid.positive,affectedIndex,
      Explicit.p,Explicit.q,pWeights,qWeights,lambdaB,NegativeAPositiveTD.lambdaB,
      Bool.false_eq_true,↓reduceIte,Matrix.cons_val,reduceCtorEq,Fin.reduceEq] <;> linarith
  · have hr : k f z/l f z∈Icc (11/20:ℝ) (17/20:ℝ) :=
      ⟨(le_div_iff₀ hl).2 hb.2.2.1.le,(div_le_iff₀ hl).2 hb.2.2.2.1.le⟩
    have hm := NegativeAPositiveTD.AffectedPositiveCurves.GA_upper_monotone hr ⟨hzf.1,hzs.trans hs.2⟩
      ⟨le_rfl,hzs.trans hs.2⟩ ⟨hzs,hs.2⟩ hzs
    have hez := GA_positive_identity (k:=k f z) (m:=m f z) (z:=z) hl hzf
    have hes := GA_positive_identity (k:=k f z) (m:=m f z) (z:=z) hl hsf
    have hmul := mul_le_mul_of_nonneg_left hm hl.le
    simp only [sub_self,U_zero,add_zero] at hez
    cases f <;> simp only [Concentration.positive,PositiveTD.Hybrid.positive,affectedIndex,
      Explicit.p,Explicit.q,pWeights,qWeights,lambdaG,NegativeAPositiveTD.lambdaG,
      ↓reduceIte,Matrix.cons_val,reduceCtorEq,Fin.reduceEq] <;> linarith

theorem reduces_to_equal (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) (hzs : z≤ s) (i : Fin 4) :
    baseline atG (k f z) (l f z) (m f z) z z≤
      baseline atG (k f z) (l f z) (m f z) s z+
        Concentration.positive f (Explicit.p f atG z s) (Explicit.q f atG z s) i (s-z) := by
  by_cases hi : i=affectedIndex atG
  · subst i
    exact affected_reduces f atG hz hs hzs
  · exact unaffected_reduces f atG hz hs hzs i hi

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.Positive
