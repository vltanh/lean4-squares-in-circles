module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELargeAShapes

/-!
# Complete scalar positivity for nonnegative A and a combined negative gain

Uncompiled transcription of the intrinsic endpoints in Section 5 of
`HAND_G3_CORE_E_NONNEGATIVE_A_NONPOSITIVE_TD2_EXCLUSION.md`.

Both gains M*w and J_M(w) are proved positive independently. The cut at
w=1/4 is retained in every concavity argument. The final theorem accepts
the original two sign budgets and a proved combined gain lower bound;
all coefficient, derivative and endpoint facts are internal theorems.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELargeA
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity TwoPositive.ASupport

theorem jointGain_of_ge {w : ℝ} (hw : u≤w) : jointGain w=g u+M*(w-u) := by
  by_cases he : w≤u
  · have hwu : w=u := le_antisymm he hw
    subst w
    simp
  · simp [jointGain,he]

private theorem const_add_concave {A B : ℝ} {f : ℝ→ℝ}
    (hf : ConcaveOn ℝ (Icc A B) f) (b : ℝ) :
    ConcaveOn ℝ (Icc A B) (fun x => b+f x) := by
  convert (NegativeOrdinaryEnvelope.affine_concave 0 b A B).add hf using 1
  funext x
  ring

theorem zero_negative_positive (i : Fin 4) {a : ℝ} (ha : a∈Icc L frameCap) :
    0<base+l*charge a+V R (p i) (q i) a := by
  have hc := shifted_negative_concave i (A:=L) (B:=frameCap) (b:=0)
    (by norm_num [L,u]) (by norm_num [L,frameCap]) le_rfl
    (fun a ha => ⟨by dsimp [L] at ha; linarith [ha.1],by simpa using ha.2⟩)
  have he := negative_endpoint_reserves i
  have hleft : 0<base+l*charge L+V R (p i) (q i) L :=
    (by fin_cases i <;> norm_num [leftReserve] : 0<leftReserve i).trans he.1
  have hright : 0<base+l*charge frameCap+V R (p i) (q i) frameCap :=
    (by fin_cases i <;> norm_num [capReserve] : 0<capReserve i).trans he.2.1
  simpa only [sub_zero,add_assoc] using concave_gt_of_endpoints (const_add_concave hc base) ha
    (by simpa only [sub_zero,add_assoc] using hleft)
    (by simpa only [sub_zero,add_assoc] using hright)

theorem linear_middle_positive {a : ℝ} (ha : a∈Icc L frameCap) :
    0<base+l*charge a+M*a := by
  have hm := linear_middle_monotone (by norm_num [L,frameCap]) ha ha.1
  linarith [zero_increment_reserves.2.2.2.1]

theorem joint_middle_positive {a : ℝ} (ha : a∈Icc L frameCap) :
    0<base+l*charge a+jointGain a := by
  by_cases hau : a≤u
  · have hc := const_add_concave short_middle_concave base
    have hh := concave_gt_of_endpoints hc ⟨ha.1,hau⟩
      (show 0<base+(l*charge L+g L) by linarith [zero_increment_reserves.1])
      (show 0<base+(l*charge u+g u) by linarith [zero_increment_reserves.2.1])
    simp only [jointGain,if_pos hau]
    linarith
  · have hua : u≤a := (lt_of_not_ge hau).le
    have hm := linear_middle_monotone (by norm_num [L,u,frameCap]) ha hua
    rw [jointGain_of_ge hua]
    linarith [zero_increment_reserves.2.1]

theorem cut_negative_positive (i : Fin 4) {a : ℝ} (ha : a∈Icc u frameCap) :
    0<base+l*charge a+g u+V R (p i) (q i) (a-u) := by
  have hc := shifted_negative_concave i (A:=u) (B:=frameCap) (b:=u)
    (by norm_num [L,u]) (by norm_num [u,frameCap]) le_rfl
    (fun a ha => ⟨by linarith [ha.1],by dsimp [u]; linarith [ha.2]⟩)
  have hleft : 0<base+g u+(l*charge u+V R (p i) (q i) (u-u)) := by
    simp only [sub_self,V_zero,add_zero]
    linarith [zero_increment_reserves.2.1]
  have hright : 0<base+g u+(l*charge frameCap+V R (p i) (q i) (frameCap-u)) := by
    have hh := (negative_endpoint_reserves i).2.2
    have hp : 0<cutNegativeReserve i := by fin_cases i <;> norm_num [cutNegativeReserve]
    linarith
  have hh := concave_gt_of_endpoints (const_add_concave hc (base+g u)) ha hleft hright
  linarith

theorem cut_positive_positive (i : Fin 4) {a : ℝ} (ha : a∈Icc L u) :
    0<base+l*charge a+g u+positive i (u-a) := by
  by_cases hi : i=3
  · subst i
    have hm := D_remainder_antitone u
      ⟨ha.1,ha.2.trans (by norm_num [u,frameCap])⟩ (by norm_num [L,u,frameCap]) ha.2
    simp only [sub_self,mul_zero,sub_zero] at hm
    simp only [positive,PositiveTD.Hybrid.positive,if_pos rfl]
    linarith [zero_increment_reserves.2.1]
  · have hc := shifted_positive_concave i (B:=u) (b:=u)
      (by norm_num [L,u]) (by norm_num [u,frameCap])
      (fun a ha => ⟨by linarith [ha.2],by dsimp [L,u,span] at ha ⊢; linarith [ha.1]⟩)
    have hleft : 0<base+g u+(l*charge L+U R (p i) (q i) (u-L)) := by
      have hh := (positive_endpoint_reserves i).1
      have hp : 0<cutPositiveReserve i := by fin_cases i <;> norm_num [cutPositiveReserve]
      linarith
    have hright : 0<base+g u+(l*charge u+U R (p i) (q i) (u-u)) := by
      simp only [sub_self,U_zero,add_zero]
      linarith [zero_increment_reserves.2.1]
    have hh := concave_gt_of_endpoints (const_add_concave hc (base+g u)) ha hleft hright
    simp only [positive,PositiveTD.Hybrid.positive,if_neg hi]
    linarith

theorem cap_positive_positive (i : Fin 4) {a : ℝ} (ha : a∈Icc L frameCap) :
    0<base+l*charge a+M*frameCap+positive i (frameCap-a) ∧
    0<base+l*charge a+jointGain frameCap+positive i (frameCap-a) := by
  have hcut : u≤frameCap := by norm_num [u,frameCap]
  rw [jointGain_of_ge hcut]
  by_cases hi : i=3
  · subst i
    have hm := D_remainder_antitone frameCap ha (by norm_num [L,frameCap]) ha.2
    simp only [sub_self,mul_zero,sub_zero] at hm
    simp only [positive,PositiveTD.Hybrid.positive,if_pos rfl]
    constructor
    · linarith [zero_increment_reserves.2.2.2.2]
    · linarith [zero_increment_reserves.2.2.1]
  · have hc := shifted_positive_concave i (B:=frameCap) (b:=frameCap)
      (by norm_num [L,frameCap]) le_rfl
      (fun a ha => ⟨by linarith [ha.2],by dsimp [L,span,frameCap] at ha ⊢; linarith [ha.1]⟩)
    have hleft₁ : 0<base+M*frameCap+(l*charge L+U R (p i) (q i) (frameCap-L)) := by
      have hh := (positive_endpoint_reserves i).2.2
      have hp : 0<linearCapReserve i := by fin_cases i <;> norm_num [linearCapReserve]
      have he : frameCap-L=span := by norm_num [L,span,frameCap]
      rw [he]
      linarith
    have hleft₂ : 0<base+g u+M*(frameCap-u)+(l*charge L+U R (p i) (q i) (frameCap-L)) := by
      have hh := (positive_endpoint_reserves i).2.1
      have hp : 0<jointCapReserve i := by fin_cases i <;> norm_num [jointCapReserve]
      have he : frameCap-L=span := by norm_num [L,span,frameCap]
      rw [he]
      linarith
    have hright₁ : 0<base+M*frameCap+(l*charge frameCap+U R (p i) (q i) (frameCap-frameCap)) := by
      simp only [sub_self,U_zero,add_zero]
      linarith [zero_increment_reserves.2.2.2.2]
    have hright₂ : 0<base+g u+M*(frameCap-u)+(l*charge frameCap+U R (p i) (q i) (frameCap-frameCap)) := by
      simp only [sub_self,U_zero,add_zero]
      linarith [zero_increment_reserves.2.2.1]
    have hh₁ := concave_gt_of_endpoints (const_add_concave hc (base+M*frameCap)) ha hleft₁ hright₁
    have hh₂ := concave_gt_of_endpoints (const_add_concave hc (base+g u+M*(frameCap-u))) ha hleft₂ hright₂
    simp only [positive,PositiveTD.Hybrid.positive,if_neg hi]
    exact ⟨by linarith,by linarith⟩

private theorem negative_gain_concave (i : Fin 4) {a A B : ℝ} {C : ℝ→ℝ}
    (hC : ConcaveOn ℝ (Icc A B) C)
    (harg : ∀w∈Icc A B,a-w∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc A B) (fun w => base+l*charge a+C w+V R (p i) (q i) (a-w)) := by
  have hc := coefficients i
  have hV := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1 (by linarith [hc.2.2.1]))
    (a:= -1) (b:=a) (l:=A) (u:=B) (fun w hw => by convert harg w hw using 1 <;> ring)
  have hV' : ConcaveOn ℝ (Icc A B) (fun w => V R (p i) (q i) (a-w)) := by
    convert hV using 1
    funext w
    congr 1
    ring
  convert const_add_concave (hC.add hV') (base+l*charge a) using 1
  funext w
  ring

private theorem positive_gain_concave (i : Fin 4) {a A B : ℝ} {C : ℝ→ℝ}
    (hC : ConcaveOn ℝ (Icc A B) C)
    (harg : ∀w∈Icc A B,w-a∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc A B) (fun w => base+l*charge a+C w+positive i (w-a)) := by
  have hc := coefficients i
  have hU := concave_affine_argument
    (PositiveTD.Hybrid.positive_concave (R:=R) (a:=aD) (p:=p) (q:=q) (d:=3) (i:=i)
      (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1 (by linarith [hc.2.2.1]))
    (a:=1) (b:= -a) (l:=A) (u:=B) (fun w hw => by convert harg w hw using 1 <;> ring)
  have hU' : ConcaveOn ℝ (Icc A B) (fun w => positive i (w-a)) := by
    convert hU using 1
    funext w
    dsimp [positive]
    congr 1
    ring
  convert const_add_concave (hC.add hU') (base+l*charge a) using 1
  funext w
  dsimp [positive]
  ring

private theorem linear_gain_concave (A B : ℝ) :
    ConcaveOn ℝ (Icc A B) (fun w => M*w) := by
  simpa using NegativeOrdinaryEnvelope.affine_concave M 0 A B

private theorem upper_gain_concave (A B : ℝ) :
    ConcaveOn ℝ (Icc A B) (fun w => g u+M*(w-u)) := by
  convert NegativeOrdinaryEnvelope.affine_concave M (g u-M*u) A B using 1
  funext w
  ring

theorem linear_negative_positive (i : Fin 4) {a w : ℝ}
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 a) :
    0<base+l*charge a+M*w+V R (p i) (q i) (a-w) := by
  have hc := negative_gain_concave i (a:=a) (linear_gain_concave 0 a)
    (fun w hw => ⟨by linarith [hw.2],by linarith [ha.2,hw.1]⟩)
  exact concave_gt_of_endpoints hc hw
    (by simpa using zero_negative_positive i ha)
    (by simpa using linear_middle_positive ha)

theorem linear_positive_positive (i : Fin 4) {a w : ℝ}
    (ha : a∈Icc L frameCap) (hw : w∈Icc a frameCap) :
    0<base+l*charge a+M*w+positive i (w-a) := by
  have ha0 : 0≤a := by dsimp [L] at ha; linarith [ha.1]
  have hc := positive_gain_concave i (a:=a) (linear_gain_concave a frameCap)
    (fun w hw => ⟨by linarith [hw.1],by linarith [hw.2]⟩)
  exact concave_gt_of_endpoints hc hw
    (by simpa [positive] using linear_middle_positive ha)
    (cap_positive_positive i ha).1

theorem joint_negative_positive (i : Fin 4) {a w : ℝ}
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 a) :
    0<base+l*charge a+jointGain w+V R (p i) (q i) (a-w) := by
  by_cases hau : a≤u
  · have hC := g_concave.subset (Icc_subset_Icc le_rfl ha.2) (convex_Icc 0 a)
    have hc := negative_gain_concave i (a:=a) hC
      (fun w hw => ⟨by linarith [hw.2],by linarith [ha.2,hw.1]⟩)
    have hh := concave_gt_of_endpoints hc hw
      (by simpa using zero_negative_positive i ha)
      (by simpa [jointGain,hau] using joint_middle_positive ha)
    simpa only [jointGain,if_pos (hw.2.trans hau)] using hh
  · have hua : u≤a := (lt_of_not_ge hau).le
    by_cases hwu : w≤u
    · have hC := g_concave.subset (Icc_subset_Icc le_rfl (by norm_num [u,frameCap])) (convex_Icc 0 u)
      have hc := negative_gain_concave i (a:=a) hC
        (fun w hw => ⟨by linarith [hw.2],by linarith [ha.2,hw.1]⟩)
      have hh := concave_gt_of_endpoints hc ⟨hw.1,hwu⟩
        (by simpa using zero_negative_positive i ha) (cut_negative_positive i ⟨hua,ha.2⟩)
      simpa only [jointGain,if_pos hwu] using hh
    · have huw : u≤w := (lt_of_not_ge hwu).le
      have hc := negative_gain_concave i (a:=a) (upper_gain_concave u a)
        (fun w hw => ⟨by linarith [hw.2],by dsimp [u] at hw; linarith [ha.2,hw.1]⟩)
      have hh := concave_gt_of_endpoints hc ⟨huw,hw.2⟩
        (by simpa using cut_negative_positive i ⟨hua,ha.2⟩)
        (by simpa [jointGain_of_ge hua] using joint_middle_positive ha)
      simpa only [jointGain_of_ge huw] using hh

theorem joint_positive_positive (i : Fin 4) {a w : ℝ}
    (ha : a∈Icc L frameCap) (hw : w∈Icc a frameCap) :
    0<base+l*charge a+jointGain w+positive i (w-a) := by
  have ha0 : 0≤a := by dsimp [L] at ha; linarith [ha.1]
  have hcap : u≤frameCap := by norm_num [u,frameCap]
  by_cases hua : u≤a
  · have hc := positive_gain_concave i (a:=a) (upper_gain_concave a frameCap)
      (fun w hw => ⟨by linarith [hw.1],by linarith [hw.2]⟩)
    have hh := concave_gt_of_endpoints hc hw
      (by simpa [positive,jointGain_of_ge hua] using joint_middle_positive ha)
      (by simpa [jointGain_of_ge hcap] using (cap_positive_positive i ha).2)
    simpa only [jointGain_of_ge (hua.trans hw.1)] using hh
  · have hau : a≤u := (lt_of_not_ge hua).le
    by_cases hwu : w≤u
    · have hC := g_concave.subset (Icc_subset_Icc ha0 hcap) (convex_Icc a u)
      have hc := positive_gain_concave i (a:=a) hC
        (fun w hw => ⟨by linarith [hw.1],by dsimp [u,frameCap] at hw ⊢; linarith [hw.2]⟩)
      have hh := concave_gt_of_endpoints hc ⟨hw.1,hwu⟩
        (by simpa [positive,jointGain,hau] using joint_middle_positive ha)
        (cut_positive_positive i ⟨ha.1,hau⟩)
      simpa only [jointGain,if_pos hwu] using hh
    · have huw : u≤w := (lt_of_not_ge hwu).le
      have hc := positive_gain_concave i (a:=a) (upper_gain_concave u frameCap)
        (fun w hw => ⟨by linarith [hw.1],by linarith [hw.2]⟩)
      have hh := concave_gt_of_endpoints hc ⟨huw,hw.2⟩
        (by simpa using cut_positive_positive i ⟨ha.1,hau⟩)
        (by simpa [jointGain_of_ge hcap] using (cap_positive_positive i ha).2)
      simpa only [jointGain_of_ge huw] using hh

theorem sum_scalar_positive_linear {a w : ℝ} (P N : Fin 4→ℝ)
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPt : (∑i,P i)≤frameCap-a) (hNt : (∑i,N i)≤frameCap-w)
    (hbalance : (∑i,N i)-(∑i,P i)=a-w) :
    0<base+l*charge a+M*w+∑i,block i (P i) (N i) := by
  obtain ⟨i,hi⟩ := sum_pure_lower P N ha hw hP hN hPt hNt hbalance
  by_cases hwa : w≤a
  · rw [if_pos hwa] at hi
    have hp := linear_negative_positive i ha ⟨hw.1,hwa⟩
    linarith
  · rw [if_neg hwa] at hi
    have hp := linear_positive_positive i ha ⟨(lt_of_not_ge hwa).le,hw.2⟩
    linarith

theorem sum_scalar_positive_joint {a w : ℝ} (P N : Fin 4→ℝ)
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPt : (∑i,P i)≤frameCap-a) (hNt : (∑i,N i)≤frameCap-w)
    (hbalance : (∑i,N i)-(∑i,P i)=a-w) :
    0<base+l*charge a+jointGain w+∑i,block i (P i) (N i) := by
  obtain ⟨i,hi⟩ := sum_pure_lower P N ha hw hP hN hPt hNt hbalance
  by_cases hwa : w≤a
  · rw [if_pos hwa] at hi
    have hp := joint_negative_positive i ha ⟨hw.1,hwa⟩
    linarith
  · rw [if_neg hwa] at hi
    have hp := joint_positive_positive i ha ⟨(lt_of_not_ge hwa).le,hw.2⟩
    linarith

/-- Source-facing scalar entry. The combined gain may come from DE/EH/TD
or from an independently proved T-pair reduction. No coefficient or
endpoint obligation is a premise. -/
theorem sum_scalar_positive {a w gain : ℝ} (P N : Fin 4→ℝ)
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPt : (∑i,P i)≤frameCap-a) (hNt : (∑i,N i)≤frameCap-w)
    (hbalance : (∑i,N i)-(∑i,P i)=a-w)
    (hgain : min (M*w) (jointGain w)≤gain) :
    0<base+l*charge a+gain+∑i,block i (P i) (N i) := by
  have hlinear := sum_scalar_positive_linear P N ha hw hP hN hPt hNt hbalance
  have hjoint := sum_scalar_positive_joint P N ha hw hP hN hPt hNt hbalance
  rcases le_total (M*w) (jointGain w) with h|h
  · rw [min_eq_left h] at hgain
    linarith
  · rw [min_eq_right h] at hgain
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELargeA
