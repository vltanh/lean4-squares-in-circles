module

public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeAShapes

/-!
# Eight squares: scalar positivity for nonnegative A and a combined negative gain

Both gains `M w` and `J_M(w)` are proved positive separately (`sum_scalar_positive_linear`,
`sum_scalar_positive_joint`). The cut at `w = 1/4` is kept in every concavity argument. The final
theorem `sum_scalar_positive` takes the two sign budgets and a lower bound of the combined gain;
all coefficient, derivative and endpoint facts are proved here.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeELargeA
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity TwoPositive.ASupport

theorem jointGain_of_ge {w : ℝ} (hw : u≤w) : jointGain w=g u+M*(w-u) := by
  unfold jointGain
  by_cases he : w≤u
  · have hwu : w=u := le_antisymm he hw
    rw [ite_eq_left he,hwu,sub_self,mul_zero,add_zero]
  · rw [ite_eq_right he]

private theorem const_add_concave {A B : ℝ} {f : ℝ→ℝ}
    (hf : ConcaveOn ℝ (Icc A B) f) (b : ℝ) :
    ConcaveOn ℝ (Icc A B) (fun x => b+f x) := by
  have h := (affine_concave 0 b A B).add hf
  convert h using 1
  funext x
  simp only [Pi.add_apply,zero_mul,zero_add]

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
  have hm : l*TwoPositive.ASupport.charge L+M*L≤l*TwoPositive.ASupport.charge a+M*a :=
    linear_middle_monotone (by norm_num [L,frameCap]) ha ha.1
  have h := zero_increment_reserves.2.2.2.1
  simp only [l,M] at hm h ⊢
  linarith

theorem joint_middle_positive {a : ℝ} (ha : a∈Icc L frameCap) :
    0<base+l*charge a+jointGain a := by
  by_cases hau : a≤u
  · have hc := const_add_concave short_middle_concave base
    have h1 := zero_increment_reserves.1
    have h2 := zero_increment_reserves.2.1
    have hl : 0<base+(l*TwoPositive.ASupport.charge L+g L) := by simp only [l] at h1 ⊢; linarith
    have hu : 0<base+(l*TwoPositive.ASupport.charge u+g u) := by simp only [l] at h2 ⊢; linarith
    have hh := concave_gt_of_endpoints (c:=0) hc ⟨ha.1,hau⟩ hl hu
    rw [jointGain,ite_eq_left hau]
    simp only [l] at hh ⊢
    linarith
  · have hua : u≤a := (lt_of_not_ge hau).le
    have hm : l*TwoPositive.ASupport.charge u+M*u≤l*TwoPositive.ASupport.charge a+M*a :=
      linear_middle_monotone (by norm_num [L,u,frameCap]) ha hua
    rw [jointGain_of_ge hua]
    have h2 := zero_increment_reserves.2.1
    simp only [l,M] at hm h2 ⊢
    linarith

theorem cut_negative_positive (i : Fin 4) {a : ℝ} (ha : a∈Icc u frameCap) :
    0<base+l*charge a+g u+V R (p i) (q i) (a-u) := by
  have hc := shifted_negative_concave i (A:=u) (B:=frameCap) (b:=u)
    (by norm_num [L,u]) (by norm_num [u,frameCap]) le_rfl
    (fun a ha => ⟨by linarith [ha.1],by
      have h := ha.2; simp only [u,frameCap] at h ⊢; linarith⟩)
  have hleft : 0<base+g u+(l*TwoPositive.ASupport.charge u+V R (p i) (q i) (u-u)) := by
    simp only [sub_self,V_zero,add_zero]
    have h := zero_increment_reserves.2.1
    simp only [l] at h ⊢
    linarith
  have hright : 0<base+g u+(l*TwoPositive.ASupport.charge frameCap+V R (p i) (q i) (frameCap-u)) := by
    have hh := (negative_endpoint_reserves i).2.2
    have hp : 0<cutNegativeReserve i := by fin_cases i <;> norm_num [cutNegativeReserve]
    simp only [l] at hh ⊢
    linarith
  have hh := concave_gt_of_endpoints (c:=0) (const_add_concave hc (base+g u)) ha hleft hright
  simp only [l] at hh ⊢
  linarith

theorem cut_positive_positive (i : Fin 4) {a : ℝ} (ha : a∈Icc L u) :
    0<base+l*charge a+g u+positive i (u-a) := by
  by_cases hi : i=3
  · subst hi
    have hm : l*TwoPositive.ASupport.charge u-aD*(u-u)≤l*TwoPositive.ASupport.charge a-aD*(u-a) := D_remainder_antitone u
      ⟨ha.1,ha.2.trans (by norm_num [u,frameCap])⟩ (by norm_num [L,u,frameCap]) ha.2
    simp only [sub_self,mul_zero,sub_zero] at hm
    simp only [positive,PositiveTD.Hybrid.positive,ite_true]
    have h := zero_increment_reserves.2.1
    simp only [l] at hm h ⊢
    linarith
  · have hc := shifted_positive_concave i (B:=u) (b:=u)
      (by norm_num [L,u]) (by norm_num [u,frameCap])
      (fun a ha => ⟨by linarith [ha.2],by
        have h := ha.1; simp only [L,u,span] at h ⊢; linarith⟩)
    have hleft : 0<base+g u+(l*TwoPositive.ASupport.charge L+U R (p i) (q i) (u-L)) := by
      have hh := (positive_endpoint_reserves i).1
      have hp : 0<cutPositiveReserve i := by fin_cases i <;> norm_num [cutPositiveReserve]
      simp only [l] at hh ⊢
      linarith
    have hright : 0<base+g u+(l*TwoPositive.ASupport.charge u+U R (p i) (q i) (u-u)) := by
      simp only [sub_self,U_zero,add_zero]
      have h := zero_increment_reserves.2.1
      simp only [l] at h ⊢
      linarith
    have hh := concave_gt_of_endpoints (c:=0) (const_add_concave hc (base+g u)) ha hleft hright
    simp only [positive,PositiveTD.Hybrid.positive,ite_eq_right hi]
    simp only [l] at hh ⊢
    linarith

theorem cap_positive_positive (i : Fin 4) {a : ℝ} (ha : a∈Icc L frameCap) :
    0<base+l*charge a+M*frameCap+positive i (frameCap-a) ∧
    0<base+l*charge a+jointGain frameCap+positive i (frameCap-a) := by
  have hcut : u≤frameCap := by norm_num [u,frameCap]
  rw [jointGain_of_ge hcut]
  by_cases hi : i=3
  · subst hi
    have hm : l*TwoPositive.ASupport.charge frameCap-aD*(frameCap-frameCap)≤l*TwoPositive.ASupport.charge a-aD*(frameCap-a) :=
      D_remainder_antitone frameCap ha (by norm_num [L,frameCap]) ha.2
    simp only [sub_self,mul_zero,sub_zero] at hm
    simp only [positive,PositiveTD.Hybrid.positive,ite_true]
    have h1 := zero_increment_reserves.2.2.2.2
    have h2 := zero_increment_reserves.2.2.1
    simp only [l,M] at hm h1 h2 ⊢
    constructor
    · linarith
    · linarith
  · have hc := shifted_positive_concave i (B:=frameCap) (b:=frameCap)
      (by norm_num [L,frameCap]) le_rfl
      (fun a ha => ⟨by linarith [ha.2],by
        have h := ha.1; simp only [L,span,frameCap] at h ⊢; linarith⟩)
    have he : frameCap-L=span := by norm_num [L,span,frameCap]
    have hleft₁ : 0<base+M*frameCap+(l*TwoPositive.ASupport.charge L+U R (p i) (q i) (frameCap-L)) := by
      have hh := (positive_endpoint_reserves i).2.2
      have hp : 0<linearCapReserve i := by fin_cases i <;> norm_num [linearCapReserve]
      rw [he]
      simp only [l,M] at hh ⊢
      linarith
    have hleft₂ : 0<base+g u+M*(frameCap-u)+(l*TwoPositive.ASupport.charge L+U R (p i) (q i) (frameCap-L)) := by
      have hh := (positive_endpoint_reserves i).2.1
      have hp : 0<jointCapReserve i := by fin_cases i <;> norm_num [jointCapReserve]
      rw [he]
      simp only [l,M] at hh ⊢
      linarith
    have hright₁ : 0<base+M*frameCap+(l*TwoPositive.ASupport.charge frameCap+U R (p i) (q i) (frameCap-frameCap)) := by
      simp only [sub_self,U_zero,add_zero]
      have h := zero_increment_reserves.2.2.2.2
      simp only [l,M] at h ⊢
      linarith
    have hright₂ : 0<base+g u+M*(frameCap-u)+
        (l*TwoPositive.ASupport.charge frameCap+U R (p i) (q i) (frameCap-frameCap)) := by
      simp only [sub_self,U_zero,add_zero]
      have h := zero_increment_reserves.2.2.1
      simp only [l,M] at h ⊢
      linarith
    have hh₁ := concave_gt_of_endpoints (c:=0) (const_add_concave hc (base+M*frameCap)) ha
      hleft₁ hright₁
    have hh₂ := concave_gt_of_endpoints (c:=0) (const_add_concave hc (base+g u+M*(frameCap-u))) ha
      hleft₂ hright₂
    simp only [positive,PositiveTD.Hybrid.positive,ite_eq_right hi]
    simp only [l,M] at hh₁ hh₂ ⊢
    exact ⟨by linarith,by linarith⟩

private theorem negative_gain_concave (i : Fin 4) {a A B : ℝ} {C : ℝ→ℝ}
    (hC : ConcaveOn ℝ (Icc A B) C)
    (harg : ∀w∈Icc A B,a-w∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc A B) (fun w => base+l*charge a+C w+V R (p i) (q i) (a-w)) := by
  have hc := coefficients i
  have hV := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1 (by linarith [hc.2.2.1]))
    (a:= -1) (b:=a) (l:=A) (u:=B)
    (fun w hw => by rw [show -1*w+a=a-w by ring]; exact harg w hw)
  have hV' : ConcaveOn ℝ (Icc A B) (fun w => V R (p i) (q i) (a-w)) := by
    convert hV using 1
    funext w
    rw [show -1*w+a=a-w by ring]
  convert const_add_concave (hC.add hV') (base+l*charge a) using 1
  funext w
  simp only [Pi.add_apply]
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
  have h := affine_concave M 0 A B
  simp only [add_zero] at h
  exact h

private theorem upper_gain_concave (A B : ℝ) :
    ConcaveOn ℝ (Icc A B) (fun w => g u+M*(w-u)) := by
  convert affine_concave M (g u-M*u) A B using 1
  funext w
  ring

private theorem r78_positive_zero (i : Fin 4) : positive i 0=0 := by
  simp [positive,PositiveTD.Hybrid.positive]

private theorem r78_neg_arg {a A B : ℝ} (ha : a≤frameCap) (hA : 0≤A) :
    ∀w∈Icc A B,w≤a → a-w∈Icc 0 frameCap := by
  intro w hw hwa
  refine ⟨by linarith,?_⟩
  have h := hw.1
  simp only [frameCap] at ha ⊢
  linarith

private theorem r78_pos_arg {a A B : ℝ} (ha : 0≤a) (hB : B≤frameCap) :
    ∀w∈Icc A B,a≤w → w-a∈Icc 0 frameCap := by
  intro w hw haw
  refine ⟨by linarith,?_⟩
  have h := hw.2
  simp only [frameCap] at hB ⊢
  linarith

theorem linear_negative_positive (i : Fin 4) {a w : ℝ}
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 a) :
    0<base+l*charge a+M*w+V R (p i) (q i) (a-w) := by
  have hc := negative_gain_concave i (a:=a) (linear_gain_concave 0 a)
    (fun w hw => r78_neg_arg ha.2 le_rfl w hw hw.2)
  have h0 : 0<base+l*TwoPositive.ASupport.charge a+M*0+V R (p i) (q i) (a-0) := by
    rw [mul_zero,add_zero,sub_zero]; exact zero_negative_positive i ha
  have h1 : 0<base+l*TwoPositive.ASupport.charge a+M*a+V R (p i) (q i) (a-a) := by
    rw [sub_self,V_zero,add_zero]; exact linear_middle_positive ha
  have hh := concave_gt_of_endpoints hc hw h0 h1
  exact hh

theorem linear_positive_positive (i : Fin 4) {a w : ℝ}
    (ha : a∈Icc L frameCap) (hw : w∈Icc a frameCap) :
    0<base+l*charge a+M*w+positive i (w-a) := by
  have ha0 : 0≤a := by have h := ha.1; simp only [L] at h; linarith
  have hc := positive_gain_concave i (a:=a) (linear_gain_concave a frameCap)
    (fun w hw => r78_pos_arg ha0 le_rfl w hw hw.1)
  have h0 : 0<base+l*TwoPositive.ASupport.charge a+M*a+positive i (a-a) := by
    rw [sub_self,r78_positive_zero,add_zero]; exact linear_middle_positive ha
  have hh := concave_gt_of_endpoints hc hw h0 (cap_positive_positive i ha).1
  exact hh

theorem joint_negative_positive (i : Fin 4) {a w : ℝ}
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 a) :
    0<base+l*charge a+jointGain w+V R (p i) (q i) (a-w) := by
  have ha0 : 0≤a := by have h := ha.1; simp only [L] at h; linarith
  have h0 : 0<base+l*TwoPositive.ASupport.charge a+g 0+V R (p i) (q i) (a-0) := by
    rw [g_zero,add_zero,sub_zero]; exact zero_negative_positive i ha
  by_cases hau : a≤u
  · have hC := g_concave.subset (Icc_subset_Icc le_rfl ha.2) (convex_Icc 0 a)
    have hc := negative_gain_concave i (a:=a) hC (fun w hw => r78_neg_arg ha.2 le_rfl w hw hw.2)
    have h1 : 0<base+l*TwoPositive.ASupport.charge a+g a+V R (p i) (q i) (a-a) := by
      have h := joint_middle_positive ha
      rw [jointGain,ite_eq_left hau] at h
      rw [sub_self,V_zero,add_zero]; exact h
    have hh := concave_gt_of_endpoints hc hw h0 h1
    rw [jointGain,ite_eq_left (hw.2.trans hau)]
    exact hh
  · have hua : u≤a := (lt_of_not_ge hau).le
    by_cases hwu : w≤u
    · have hC := g_concave.subset (Icc_subset_Icc le_rfl (by norm_num [u,frameCap]))
        (convex_Icc 0 u)
      have hc := negative_gain_concave i (a:=a) hC
        (fun w hw => r78_neg_arg ha.2 le_rfl w hw (hw.2.trans hua))
      have hh := concave_gt_of_endpoints hc ⟨hw.1,hwu⟩ h0 (cut_negative_positive i ⟨hua,ha.2⟩)
      rw [jointGain,ite_eq_left hwu]
      exact hh
    · have huw : u≤w := (lt_of_not_ge hwu).le
      have hc := negative_gain_concave i (a:=a) (upper_gain_concave u a)
        (fun w hw => r78_neg_arg ha.2 (by norm_num [u]) w hw hw.2)
      have h1 : 0<base+l*TwoPositive.ASupport.charge a+(g u+M*(u-u))+V R (p i) (q i) (a-u) := by
        rw [sub_self,mul_zero,add_zero]; exact cut_negative_positive i ⟨hua,ha.2⟩
      have h2 : 0<base+l*TwoPositive.ASupport.charge a+(g u+M*(a-u))+V R (p i) (q i) (a-a) := by
        have h := joint_middle_positive ha
        rw [jointGain_of_ge hua] at h
        rw [sub_self,V_zero,add_zero]; exact h
      have hh := concave_gt_of_endpoints hc ⟨huw,hw.2⟩ h1 h2
      rw [jointGain_of_ge huw]
      exact hh

theorem joint_positive_positive (i : Fin 4) {a w : ℝ}
    (ha : a∈Icc L frameCap) (hw : w∈Icc a frameCap) :
    0<base+l*charge a+jointGain w+positive i (w-a) := by
  have ha0 : 0≤a := by have h := ha.1; simp only [L] at h; linarith
  have hcap : u≤frameCap := by norm_num [u,frameCap]
  by_cases hua : u≤a
  · have hc := positive_gain_concave i (a:=a) (upper_gain_concave a frameCap)
      (fun w hw => r78_pos_arg ha0 le_rfl w hw hw.1)
    have h1 : 0<base+l*TwoPositive.ASupport.charge a+(g u+M*(a-u))+positive i (a-a) := by
      have h := joint_middle_positive ha
      rw [jointGain_of_ge hua] at h
      rw [sub_self,r78_positive_zero,add_zero]; exact h
    have h2 : 0<base+l*TwoPositive.ASupport.charge a+(g u+M*(frameCap-u))+positive i (frameCap-a) := by
      have h := (cap_positive_positive i ha).2
      rw [jointGain_of_ge hcap] at h
      exact h
    have hh := concave_gt_of_endpoints hc hw h1 h2
    rw [jointGain_of_ge (hua.trans hw.1)]
    exact hh
  · have hau : a≤u := (lt_of_not_ge hua).le
    by_cases hwu : w≤u
    · have hC := g_concave.subset (Icc_subset_Icc ha0 hcap) (convex_Icc a u)
      have hc := positive_gain_concave i (a:=a) hC
        (fun w hw => r78_pos_arg ha0 hcap w hw hw.1)
      have h1 : 0<base+l*TwoPositive.ASupport.charge a+g a+positive i (a-a) := by
        have h := joint_middle_positive ha
        rw [jointGain,ite_eq_left hau] at h
        rw [sub_self,r78_positive_zero,add_zero]; exact h
      have hh := concave_gt_of_endpoints hc ⟨hw.1,hwu⟩ h1 (cut_positive_positive i ⟨ha.1,hau⟩)
      rw [jointGain,ite_eq_left hwu]
      exact hh
    · have huw : u≤w := (lt_of_not_ge hwu).le
      have hc := positive_gain_concave i (a:=a) (upper_gain_concave u frameCap)
        (fun w hw => r78_pos_arg ha0 le_rfl w hw (hau.trans hw.1))
      have h1 : 0<base+l*TwoPositive.ASupport.charge a+(g u+M*(u-u))+positive i (u-a) := by
        rw [sub_self,mul_zero,add_zero]; exact cut_positive_positive i ⟨ha.1,hau⟩
      have h2 : 0<base+l*TwoPositive.ASupport.charge a+(g u+M*(frameCap-u))+positive i (frameCap-a) := by
        have h := (cap_positive_positive i ha).2
        rw [jointGain_of_ge hcap] at h
        exact h
      have hh := concave_gt_of_endpoints hc ⟨huw,hw.2⟩ h1 h2
      rw [jointGain_of_ge huw]
      exact hh

theorem sum_scalar_positive_linear {a w : ℝ} (P N : Fin 4→ℝ)
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPt : (∑i,P i)≤frameCap-a) (hNt : (∑i,N i)≤frameCap-w)
    (hbalance : (∑i,N i)-(∑i,P i)=a-w) :
    0<base+l*charge a+M*w+∑i,block i (P i) (N i) := by
  obtain ⟨i,hi⟩ := sum_pure_lower P N ha hw hP hN hPt hNt hbalance
  by_cases hwa : w≤a
  · rw [ite_eq_left hwa] at hi
    have hp := linear_negative_positive i ha ⟨hw.1,hwa⟩
    linarith
  · rw [ite_eq_right hwa] at hi
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
  · rw [ite_eq_left hwa] at hi
    have hp := joint_negative_positive i ha ⟨hw.1,hwa⟩
    linarith
  · rw [ite_eq_right hwa] at hi
    have hp := joint_positive_positive i ha ⟨(lt_of_not_ge hwa).le,hw.2⟩
    linarith

/-- The scalar statement used on the cycle. The combined gain may come from DE, EH and TD, or from
a T-pair reduction. No coefficient or endpoint fact is a hypothesis. -/
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

end SquaresInCircles.Eight.GlobalGA.NegativeELargeA
