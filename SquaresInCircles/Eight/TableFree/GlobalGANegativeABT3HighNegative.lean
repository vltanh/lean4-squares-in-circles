module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3Concentration

/-!
# The high pure-negative alternatives

Uncompiled Section 5, high interval. The unaffected H/B or H/G curve
uses the secant-coordinate curvature on the actual cut. Both affected
pairs have their fixed coefficient below l, so their complete variable
part is the concave affine-minus-norm branch. D is compared with H.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.HighNegative
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativeAPositiveTD.SecantCoordinate NegativeAPositiveTD.SecantBounds
open NegativeAPositiveTD.UnaffectedCurvature

def Unaffected : Bool→Fin 4→Prop
  | true,i => i=0∨i=2
  | false,i => i=0∨i=1
def p (atG : Bool) (z : ℝ) : Fin 4→ℝ := Explicit.p .high atG z 0
def q (atG : Bool) (z : ℝ) : Fin 4→ℝ := Explicit.q .high atG z 0
def ratio (atG : Bool) (z : ℝ) : ℝ :=
  Angular.ratio atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z)
def angleEnd (atG : Bool) (z : ℝ) : ℝ := min z (Explicit.angleCut atG)
def scalar (atG : Bool) (z : ℝ) (i : Fin 4) (x : ℝ) : ℝ :=
  NegativeAPositiveTD.SecantCoordinate.pure
    (baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) 0 z)
    (Explicit.l .high z) (ratio atG z) (p atG z i) (q atG z i) z x

theorem cut_domain (atG : Bool) : Explicit.angleCut atG∈Icc (0:ℝ) frameCap := by
  cases atG <;> norm_num [Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut,frameCap]
theorem angleEnd_domain (atG : Bool) {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    angleEnd atG z∈Icc 0 frameCap ∧ angleEnd atG z≤z ∧ angleEnd atG z≤Explicit.angleCut atG := by
  have hc := cut_domain atG
  exact ⟨⟨le_min (by linarith [hz.1]) hc.1,(min_le_right _ _).trans hc.2⟩,
    min_le_left _ _,min_le_right _ _⟩
theorem weights_fixed (atG : Bool) (z s : ℝ) (i : Fin 4) (hi : Unaffected atG i) :
    Explicit.p .high atG z s i=p atG z i ∧ Explicit.q .high atG z s i=q atG z i := by
  cases atG <;> rcases hi with rfl|rfl <;>
    simp [p,q,Explicit.p,Explicit.q,pWeights,qWeights,lambdaG,lambdaB,
      NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,secant,NegativeAPositiveTD.secant]
theorem ordered (atG : Bool) {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (i : Fin 4) :
    0<p atG z i ∧ p atG z i≤q atG z i ∧ q atG z i≤2*p atG z i :=
  Explicit.ordered_pair_domain .high atG hz ⟨le_rfl,(cut_domain atG).1⟩ i
theorem GA_pair_upper {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (i : Fin 4) :
    q true z i≤(11/10)*Explicit.l .high z := by
  have hq := (Explicit.high_GA_pair_bounds hz (show (0:ℝ)∈Icc 0 (1/4:ℝ) by norm_num) i).2.2
  have hl := (Explicit.high_ranges hz).2.1.1
  dsimp [q]
  linarith
theorem AB_pair_upper {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ))
    (i : Fin 4) (hi : Unaffected false i) :
    p false z i≤(21/25)*q false z i ∧ q false z i≤Explicit.l .high z := by
  have hb := Explicit.high_ranges hz
  have hr := Explicit.high_ratios hz
  rcases hi with rfl|rfl <;>
    norm_num [p,q,Explicit.p,Explicit.q,pWeights,qWeights,lambdaG,lambdaB,
      NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,secant,NegativeAPositiveTD.secant] <;>
    constructor <;> linarith [hb.1.2,hb.2.1.1,hr.2.1]
theorem ratio_bounds (atG : Bool) {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    ratio atG z∈Icc 0 (if atG then (17/20:ℝ) else 129/125) ∧ ratio atG z<1 := by
  have hb := Explicit.positive .high hz
  have hl : 0<Explicit.l .high z := by linarith [hb.2.1]
  have hr := Explicit.high_ratios hz
  cases atG <;> simp only [ratio,Angular.ratio,Angular.affected,↓reduceIte]
  · exact ⟨⟨div_nonneg hb.2.2.le hl.le,(div_le_iff₀ hl).2 hr.2.2.2.1.le⟩,
      (div_lt_one hl).2 hr.2.2.2.2⟩
  · exact ⟨⟨div_nonneg hb.1.le hl.le,(div_le_iff₀ hl).2 (by linarith [hr.2.1])⟩,
      (div_lt_one hl).2 (by linarith [hr.2.1])⟩
theorem AB_ratio_late {z x : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ))
    (hx : x∈Icc 0 (Real.tan (angleEnd false z))) (hlate : (7/20:ℝ)<x) :
    ratio false z∈Icc 0 (23/25:ℝ) := by
  have ha := angleEnd_domain false hz
  have hs := arctan_interval ha.1 hx
  have hsf : Real.arctan x∈Icc 0 frameCap := ⟨hs.1,hs.2.trans ha.1.2⟩
  have hthird : (1/3:ℝ)<Real.arctan x := by
    by_contra hh
    have ht := tan_monotone hsf (show (1/3:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) (le_of_not_gt hh)
    rw [Real.tan_arctan] at ht
    linarith [tan_third]
  have hm := Explicit.high_ratio_late (show z∈Icc (1/3:ℝ) (7/10:ℝ) from
    ⟨by linarith [hs.2,ha.2.1],hz.2⟩)
  have hl : 0<Explicit.l .high z := by linarith [(Explicit.positive .high hz).2.1]
  exact ⟨(ratio_bounds false hz).1.1,(div_le_iff₀ hl).2 hm.le⟩

theorem scalar_at_original (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 frameCap)
    (i : Fin 4) (hi : Unaffected atG i) :
    scalar atG z i (Real.tan s)=
      baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s z+
        V R (Explicit.p .high atG z s i) (Explicit.q .high atG z s i) (z-s) := by
  obtain ⟨hp,hq⟩ := weights_fixed atG z s i hi
  rw [hp,hq]
  exact Angular.pure_at_original atG (by linarith [(Explicit.positive .high hz).2.1]) hs
theorem scalar_zero (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) : 0<scalar atG z i 0 := by
  obtain ⟨hH,hG,hB,hGA,hAB⟩ := high_endpoints hz
  have hml := (Explicit.high_ratios hz).2.2.2.2
  cases atG <;> rcases hi with rfl|rfl
  all_goals simp only [scalar,NegativeAPositiveTD.SecantCoordinate.pure,Real.arctan_zero,sub_zero,
    sub_self,mul_zero,add_zero,baseline_zero]
  all_goals simp [p,q,Explicit.p,Explicit.q,pWeights,qWeights,lambdaG,lambdaB,
    NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,secant,NegativeAPositiveTD.secant,
    min_eq_right hml.le,max_eq_left hml.le] <;> assumption
theorem scalar_right (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) :
    0<scalar atG z i (Real.tan (angleEnd atG z)) := by
  by_cases he : z≤Explicit.angleCut atG
  · rw [angleEnd,min_eq_left he,scalar_at_original atG hz (Explicit.frame_domain .high hz) i hi]
    simp only [sub_self,V_zero,add_zero]
    cases atG
    · exact (high_endpoints hz).2.2.2.2
    · exact (high_endpoints hz).2.2.2.1
  · have he' := le_of_not_ge he
    rw [angleEnd,min_eq_right he',scalar_at_original atG hz (cut_domain atG) i hi]
    have hml := (Explicit.high_ratios hz).2.2.2.2
    cases atG
    · obtain ⟨hG,hH⟩ := AB_cut_endpoints (show z∈Icc (19/50:ℝ) (7/10:ℝ) from ⟨he',hz.2⟩)
      rcases hi with rfl|rfl <;> simpa [Explicit.p,Explicit.q,pWeights,qWeights,lambdaG,lambdaB,
        NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,
        Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut] using (by assumption)
    · obtain ⟨hH,hB⟩ := GA_cut_endpoints hz
      rcases hi with rfl|rfl <;> simpa [Explicit.p,Explicit.q,pWeights,qWeights,lambdaG,lambdaB,
        NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,min_eq_right hml.le,max_eq_left hml.le,
        Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut] using (by assumption)

theorem scalar_concave (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) :
    ConcaveOn ℝ (Icc 0 (Real.tan (angleEnd atG z))) (scalar atG z i) := by
  have ha := angleEnd_domain atG hz
  obtain ⟨hp,hpq,hqp⟩ := ordered atG hz i
  have hl : 0<Explicit.l .high z := by linarith [(Explicit.positive .high hz).2.1]
  apply pure_concave hp (hp.trans_le hpq) ha.1 ha.2.1 hz.2
  intro x hx
  have hs := arctan_interval ha.1 hx
  have hθ : z-Real.arctan x∈Icc 0 frameCap :=
    ⟨by linarith [hs.2,ha.2.1],by linarith [hz.2,hs.1]⟩
  have htan := tan_monotone ha.1 (cut_domain atG) ha.2.2
  cases atG
  · have hxcut : x≤2/5 := by
      simpa [Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut] using
        (hx.2.trans htan).trans tan_AB_cut.le
    have hpair := AB_pair_upper hz i hi
    by_cases hearly : x≤7/20
    · exact (AB_early_total_curvature hl (ratio_bounds false hz).1 hp hpq hqp hpair.1 hpair.2
        ⟨hx.1,hearly⟩ hθ).le
    · exact (AB_late_total_curvature hl (AB_ratio_late hz hx (lt_of_not_ge hearly))
        hp hpq hqp hpair.1 hpair.2 ⟨(lt_of_not_ge hearly).le,hxcut⟩ hθ).le.trans (by linarith)
  · have hxcut : x≤32/125 := by
      simpa [Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut] using
        (hx.2.trans htan).trans tan_GA_cut.le
    exact (GA_total_curvature hl (ratio_bounds true hz).1 hp hpq hqp (GA_pair_upper hz i)
      ⟨hx.1,hxcut⟩ hθ).le.trans (by linarith)

theorem unaffected_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (hsz : s≤z) (i : Fin 4) (hi : Unaffected atG i) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s z+
      V R (Explicit.p .high atG z s i) (Explicit.q .high atG z s i) (z-s) := by
  have hsf := (Explicit.angle_domain atG hs).2
  have ha := angleEnd_domain atG hz
  have hx : Real.tan s∈Icc 0 (Real.tan (angleEnd atG z)) :=
    ⟨tan_nonnegative hsf,tan_monotone hsf ha.1 (le_min hsz hs.2)⟩
  have hh := concave_gt_of_endpoints (scalar_concave atG hz i hi) hx
    (scalar_zero atG hz i hi) (scalar_right atG hz i hi)
  rwa [scalar_at_original atG hz hsf i hi] at hh

def affectedScalar (atG : Bool) (z x : ℝ) : ℝ :=
  baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) 0 z+
    Explicit.l .high z*(NegativeAPositiveTD.AffectedNegativeCurves.upper (ratio atG z) z x-1+
      R*OrdinaryCurvatureBounds.shape (ratio atG z))

theorem affected_identity (atG : Bool) {k l m s z : ℝ} (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    baseline atG k l m s z+V R (Angular.affected atG k m) (secant l s) (z-s)=
      baseline atG k l m 0 z+l*(NegativeAPositiveTD.AffectedNegativeCurves.upper
        (Angular.ratio atG k l m) z (Real.tan s)-1+
        R*OrdinaryCurvatureBounds.shape (Angular.ratio atG k l m)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hcos : Real.cos (z-s)/Real.cos s=Real.cos z+Real.tan s*Real.sin z := by
    rw [Real.cos_sub,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    ring
  rw [Angular.baseline_eq_extension atG k l m z hs]
  simp only [Angular.extension,FlatTStress.secantCharge,V]
  rw [show -(z-s)=s-z by ring,
    NegativeAPositiveTD.AffectedPositive.rotation_norm hl hc (Angular.affected atG k m) z,
    NegativeAPositiveTD.AffectedPositive.zero_norm hl (Angular.affected atG k m)]
  dsimp [Angular.ratio,NegativeAPositiveTD.AffectedNegativeCurves.upper,secant,NegativeAPositiveTD.secant]
  have hh := congrArg (fun a : ℝ => l*a) hcos
  field_simp [hl.ne',hc.ne'] at hh ⊢
  nlinarith only [hh]

theorem affectedScalar_concave (atG : Bool) {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    ConcaveOn ℝ (Icc 0 (Real.tan z)) (affectedScalar atG z) := by
  have hr := ratio_bounds atG hz
  have hv := NegativeAPositiveTD.AffectedNorm.second_coordinate_pos
    ⟨hr.1.1,by linarith [hr.2]⟩ (Explicit.frame_domain .high hz)
  have hc := NegativeAPositiveTD.AffectedNegativeCurves.upper_concave
    (a:=0) (b:=Real.tan z) hv
  have hl : 0<Explicit.l .high z := by linarith [(Explicit.positive .high hz).2.1]
  refine ⟨hc.1,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hc.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  have hp := mul_le_mul_of_nonneg_left hh hl.le
  dsimp [affectedScalar]
  nlinarith [congrArg (fun t : ℝ => t*(baseline atG (Explicit.k .high z)
    (Explicit.l .high z) (Explicit.m .high z) 0 z+
    Explicit.l .high z*(-1+R*OrdinaryCurvatureBounds.shape (ratio atG z)))) hab]

theorem affected_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (hsz : s≤z) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s z+
      V R (Angular.affected atG (Explicit.k .high z) (Explicit.m .high z))
        (secant (Explicit.l .high z) s) (z-s) := by
  have hl : 0<Explicit.l .high z := by linarith [(Explicit.positive .high hz).2.1]
  have hzframe := Explicit.frame_domain .high hz
  have hsf := (Explicit.angle_domain atG hs).2
  have he (a : ℝ) (ha : a∈Icc 0 frameCap) := affected_identity atG
    (k:=Explicit.k .high z) (m:=Explicit.m .high z) (z:=z) hl ha
  have hzero : 0<affectedScalar atG z 0 := by
    have hh := he 0 (by norm_num [frameCap])
    simp only [Real.tan_zero] at hh
    rw [affectedScalar,←hh]
    cases atG
    · simpa [Angular.affected,secant,NegativeAPositiveTD.secant,baseline_zero] using (high_endpoints hz).2.2.1
    · simpa [Angular.affected,secant,NegativeAPositiveTD.secant,baseline_zero] using (high_endpoints hz).2.1
  have hright : 0<affectedScalar atG z (Real.tan z) := by
    rw [affectedScalar,←he z hzframe]
    simp only [sub_self,V_zero,add_zero]
    cases atG
    · exact (high_endpoints hz).2.2.2.2
    · exact (high_endpoints hz).2.2.2.1
  have hx : Real.tan s∈Icc 0 (Real.tan z) := ⟨tan_nonnegative hsf,tan_monotone hsf hzframe hsz⟩
  have hh := concave_gt_of_endpoints (affectedScalar_concave atG hz) hx hzero hright
  simpa only [affectedScalar,←he s hsf] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.HighNegative
