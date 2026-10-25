module

public import SquaresInCircles.Eight.Frames.Ordinary.PositiveEnvelope
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Angular
public import SquaresInCircles.Eight.Owners.GA.Negative.ELowAStress
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Data
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Endpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowNegativeComparison
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Concentration
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedPositive
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowPositiveCoefficients
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeAConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2HighAffected

/-!
# Eight squares: every high intrinsic BT3 reference alternative

All four ordinary pairs satisfy
the existing full and half-angle derivative margins. The optional
index used in the generic lemma below merely expresses an ordinary
family as a hybrid family with an unused distinguished index; its
conclusion is stated only for the original four pairs.
-/

section
/-!
## Concentrating the two signed totals

The budgets are `h - z` and `h - s`, and their signed difference `z - s` is kept. The high family
uses four ordinary blocks; the low family keeps the sorted-D hybrid minorant (`concentrate`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.Concentration
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open Certificate (Family)

def positive (f : Family) (p q : Fin 4→ℝ) (i : Fin 4) (t : ℝ) : ℝ :=
  if f=.low then PositiveTD.Hybrid.positive R (67/100) p q 3 i t else U R (p i) (q i) t
def block (f : Family) (p q : Fin 4→ℝ) (i : Fin 4) (P N : ℝ) : ℝ :=
  if f=.low then PositiveTD.Hybrid.block R (67/100) p q 3 i P N else mixedBlock R (p i) (q i) P N
def pure (f : Family) (p q : Fin 4→ℝ) (i j : Fin 4) (s z : ℝ) : ℝ :=
  if s≤z then V R (p j) (q j) (z-s) else positive f p q i (s-z)
def saturated (f : Family) (p q : Fin 4→ℝ) (i j : Fin 4) (s z : ℝ) : ℝ :=
  if i=j then block f p q i (frameCap-z) (frameCap-s)
  else positive f p q i (frameCap-z)+V R (p j) (q j) (frameCap-s)

@[simp] theorem positive_zero (f : Family) (p q : Fin 4→ℝ) (i : Fin 4) : positive f p q i 0=0 := by
  cases f <;> simp [positive,PositiveTD.Hybrid.positive]
@[simp] theorem block_zero_left (f : Family) (p q : Fin 4→ℝ) (i : Fin 4) (t : ℝ) :
    block f p q i 0 t=V R (p i) (q i) t := by
  cases f <;> simp [block,PositiveTD.Hybrid.block]
@[simp] theorem block_zero_right (f : Family) (p q : Fin 4→ℝ) (i : Fin 4) (t : ℝ) :
    block f p q i t 0=positive f p q i t := by
  cases f <;> simp [block,positive,PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive]

theorem reverse_separated_concave {p q p' q' t : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hp' : 0<p') (hpq' : p'≤q') (hqp' : q'≤2*p')
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t)) (fun N => U R p q (t+N)+V R p' q' N) := by
  have hU := concave_affine_argument (U_concave (Real.sqrt_nonneg _) radius_sq.le hp hpq hqp)
    (a:=1) (b:=t) (l:=0) (u:=frameCap-t)
    (fun N hN => ⟨by linarith [hN.1,ht.1],by linarith [hN.2]⟩)
  have hV := (V_concave (Real.sqrt_nonneg _) radius_sq.le hp' hpq' hqp').subset
    (Icc_subset_Icc le_rfl (by linarith [ht.1])) (convex_Icc 0 (frameCap-t))
  convert hU.add hV using 1
  funext N
  simp only [Pi.add_apply,one_mul,add_comm t N]

theorem concentrate (f : Family) (p q P N : Fin 4→ℝ) {s z : ℝ}
    (hp : ∀i,0<p i) (hpq : ∀i,p i≤q i) (hqp : ∀i,q i≤2*p i)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hPbudget : (∑i,P i)≤frameCap-z) (hNbudget : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=z-s) :
    ∃i j,min (pure f p q i j s z) (saturated f p q i j s z)≤∑k,block f p q k (P k) (N k) := by
  cases f
  · have hh := NegativeAPositiveTD.Concentration.concentrate R (67/100) p q P N 3
      (Real.sqrt_nonneg _) radius_sq.le hp hpq hqp hP hN hs hz hPbudget hNbudget hbalance
    simpa only [pure,saturated,positive,block,↓reduceIte,
      NegativeAPositiveTD.Concentration.pure,NegativeAPositiveTD.Concentration.saturated] using hh
  · have hPt : (∑i,P i)≤frameCap := by linarith [hz.1]
    have hNt : (∑i,N i)≤frameCap := by linarith [hs.1]
    obtain ⟨i,j,hij⟩ := OrdinaryAngleConcentration.both_signs_concentrate R p q P N
      (Real.sqrt_nonneg _) radius_sq.le hp hpq hqp hP hN hPt hNt
    refine ⟨i,j,?_⟩
    simp only [pure,saturated,positive,block]
    by_cases hsz : s≤z
    · have ht : z-s∈Icc 0 frameCap := ⟨by linarith,by linarith [hz.2,hs.1]⟩
      have htotal : (∑i,P i)∈Icc 0 (frameCap-z) :=
        ⟨Finset.sum_nonneg (fun i _ => hP i),hPbudget⟩
      have hspan : 0≤frameCap-z := by linarith [hz.2]
      have heq : (∑i,N i)=(z-s)+(∑i,P i) := by linarith
      have he : (z-s)+(frameCap-z)=frameCap-s := by ring
      simp only [ite_eq_left hsz]
      by_cases heij : i=j
      · subst j
        simp only [heq] at hij ⊢
        have hc := (sameBlockLine_concave (R:=R) (hp i).le ((hp i).trans_le (hpq i)).le ht).subset
          (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-z))
        have hm := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
        rw [add_zero,mixedBlock_zero_left,he] at hm
        exact hm.trans hij
      · simp only [ite_eq_right heij,heq] at hij ⊢
        have hc := (separatedLine_concave (Real.sqrt_nonneg _) radius_sq.le
          (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
          (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-z))
        have hm := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
        simp only [U_zero,zero_add,add_zero,he] at hm
        exact hm.trans hij
    · have ht : s-z∈Icc 0 frameCap := ⟨by linarith,by linarith [hs.2,hz.1]⟩
      have htotal : (∑i,N i)∈Icc 0 (frameCap-s) :=
        ⟨Finset.sum_nonneg (fun i _ => hN i),hNbudget⟩
      have hspan : 0≤frameCap-s := by linarith [hs.2]
      have heq : (∑i,P i)=(s-z)+(∑i,N i) := by linarith
      have he : (s-z)+(frameCap-s)=frameCap-z := by ring
      simp only [ite_eq_right hsz]
      by_cases heij : i=j
      · subst j
        simp only [heq] at hij ⊢
        have hc := (NegativeAPositiveTD.Concentration.reverse_ordinary_line_concave
          (R:=R) (hp i).le ((hp i).trans_le (hpq i)).le ht).subset
          (Icc_subset_Icc le_rfl (by linarith [hz.1])) (convex_Icc 0 (frameCap-s))
        have hm := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
        rw [add_zero,mixedBlock_zero_right,he] at hm
        exact hm.trans hij
      · simp only [ite_eq_right heij,heq] at hij ⊢
        have hc := (reverse_separated_concave
          (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
          (Icc_subset_Icc le_rfl (by linarith [hz.1])) (convex_Icc 0 (frameCap-s))
        have hm := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
        simp only [V_zero,add_zero,he] at hm
        exact hm.trans hij

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.Concentration
end
end
end

section
/-!
## The high pure-negative alternatives

The unaffected H/B or H/G curve
uses the secant-coordinate curvature on the actual cut. Both affected
pairs have their fixed coefficient below l, so their complete variable
part is the concave affine-minus-norm branch. D is compared with H.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.HighNegative
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

private theorem r68_hd {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    z∈Icc (Certificate.left .high:ℝ) (Certificate.right .high:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]
  exact hz

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
      NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,NegativeAPositiveTD.secant]
theorem ordered (atG : Bool) {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (i : Fin 4) :
    0<p atG z i ∧ p atG z i≤q atG z i ∧ q atG z i≤2*p atG z i := by
  exact Explicit.ordered_pair_domain .high atG (r68_hd hz) ⟨le_rfl,(cut_domain atG).1⟩ i
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
    simp only [p,q,Explicit.p,Explicit.q,pWeights,qWeights,Matrix.cons_val,lambdaG,
      NegativeAPositiveTD.lambdaG,Bool.false_eq_true,↓reduceIte]
  · exact ⟨by linarith [hb.1.2],by linarith [hb.2.1.1]⟩
  · exact ⟨by linarith [hr.2.1,hb.2.1.1],le_rfl⟩
theorem ratio_bounds (atG : Bool) {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    ratio atG z∈Icc 0 (if atG then (17/20:ℝ) else 129/125) ∧ ratio atG z<1 := by
  have hb := Explicit.positive .high (r68_hd hz)
  have hl : 0<Explicit.l .high z := by linarith [hb.2.1]
  have hr := Explicit.high_ratios hz
  cases atG <;> simp only [ratio,Angular.ratio,Angular.affected,↓reduceIte,Bool.false_eq_true]
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
    have ht := tan_monotone hsf (show (1/3:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
      (le_of_not_gt hh)
    rw [Real.tan_arctan] at ht
    linarith [tan_third]
  have hm := Explicit.high_ratio_late (show z∈Icc (1/3:ℝ) (7/10:ℝ) from
    ⟨by linarith [hs.2,ha.2.1],hz.2⟩)
  have hl : 0<Explicit.l .high z := by linarith [(Explicit.positive .high (r68_hd hz)).2.1]
  exact ⟨(ratio_bounds false hz).1.1,(div_le_iff₀ hl).2 hm.le⟩

theorem scalar_at_original (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 frameCap)
    (i : Fin 4) (hi : Unaffected atG i) :
    scalar atG z i (Real.tan s)=
      baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s z+
        V R (Explicit.p .high atG z s i) (Explicit.q .high atG z s i) (z-s) := by
  obtain ⟨hp,hq⟩ := weights_fixed atG z s i hi
  rw [hp,hq]
  exact Angular.pure_at_original atG
    (by linarith [(Explicit.positive .high (r68_hd hz)).2.1]) hs
theorem scalar_zero (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) : 0<scalar atG z i 0 := by
  obtain ⟨hH,hG,hB,hGA,hAB⟩ := high_endpoints hz
  have hml := (Explicit.high_ratios hz).2.2.2.2
  have h0 := scalar_at_original atG hz (s:=0) ⟨le_rfl,by norm_num [frameCap]⟩ i hi
  rw [Real.tan_zero] at h0
  rw [h0,baseline_zero,sub_zero]
  cases atG <;> rcases hi with rfl|rfl <;>
    simp only [Explicit.p,Explicit.q,pWeights,qWeights,Matrix.cons_val,lambdaG,lambdaB,
      NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,Bool.false_eq_true,↓reduceIte,
      min_eq_right hml.le,max_eq_left hml.le]
  · exact hH
  · exact hG
  · exact hH
  · exact hB
theorem scalar_right (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) :
    0<scalar atG z i (Real.tan (angleEnd atG z)) := by
  by_cases he : z≤Explicit.angleCut atG
  · rw [angleEnd,min_eq_left he,
      scalar_at_original atG hz (Explicit.frame_domain .high (r68_hd hz)) i hi]
    simp only [sub_self,V_zero,add_zero]
    cases atG
    · exact (high_endpoints hz).2.2.2.2
    · exact (high_endpoints hz).2.2.2.1
  · have he' := le_of_not_ge he
    rw [angleEnd,min_eq_right he',scalar_at_original atG hz (cut_domain atG) i hi]
    have hml := (Explicit.high_ratios hz).2.2.2.2
    cases atG
    · have hcut : Explicit.angleCut false=19/50 := by
        simp [Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut]
      rw [hcut] at he' ⊢
      obtain ⟨hG,hH⟩ := AB_cut_endpoints (show z∈Icc (19/50:ℝ) (7/10:ℝ) from ⟨he',hz.2⟩)
      rcases hi with rfl|rfl <;>
        simp only [Explicit.p,Explicit.q,pWeights,qWeights,Matrix.cons_val,lambdaG,
          NegativeAPositiveTD.lambdaG,Bool.false_eq_true,↓reduceIte]
      · exact hH
      · exact hG
    · have hcut : Explicit.angleCut true=1/4 := by
        simp [Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut]
      rw [hcut]
      obtain ⟨hH,hB⟩ := GA_cut_endpoints hz
      rcases hi with rfl|rfl <;>
        simp only [Explicit.p,Explicit.q,pWeights,qWeights,Matrix.cons_val,lambdaB,
          NegativeAPositiveTD.lambdaB,↓reduceIte,min_eq_right hml.le,max_eq_left hml.le]
      · exact hH
      · exact hB

theorem scalar_concave (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) :
    ConcaveOn ℝ (Icc 0 (Real.tan (angleEnd atG z))) (scalar atG z i) := by
  have ha := angleEnd_domain atG hz
  obtain ⟨hp,hpq,hqp⟩ := ordered atG hz i
  have hl : 0<Explicit.l .high z := by linarith [(Explicit.positive .high (r68_hd hz)).2.1]
  apply pure_concave hp (hp.trans_le hpq) ha.1 ha.2.1 (by simp only [frameCap]; exact hz.2)
  intro x hx
  have hs := arctan_interval ha.1 hx
  have hθ : z-Real.arctan x∈Icc 0 frameCap :=
    ⟨by linarith [hs.2,ha.2.1],by simp only [frameCap]; linarith [hz.2,hs.1]⟩
  have htan := tan_monotone ha.1 (cut_domain atG) ha.2.2
  cases atG
  · have hcut : Explicit.angleCut false=19/50 := by
      simp [Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut]
    have hxcut : x≤2/5 := by
      rw [hcut] at htan
      linarith [hx.2,tan_AB_cut]
    have hpair := AB_pair_upper hz i hi
    by_cases hearly : x≤7/20
    · exact (AB_early_total_curvature hl (ratio_bounds false hz).1 hp hpq hqp hpair.1 hpair.2
        ⟨hx.1,hearly⟩ hθ).le
    · exact (AB_late_total_curvature hl (AB_ratio_late hz hx (lt_of_not_ge hearly))
        hp hpq hqp hpair.1 hpair.2 ⟨(lt_of_not_ge hearly).le,hxcut⟩ hθ).le.trans
        (by linarith)
  · have hcut : Explicit.angleCut true=1/4 := by
      simp [Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut]
    have hxcut : x≤32/125 := by
      rw [hcut] at htan
      linarith [hx.2,tan_GA_cut]
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
  have hcos : Real.cos (z-s)=(Real.cos z+Real.tan s*Real.sin z)*Real.cos s := by
    rw [Real.cos_sub,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
  rw [Angular.baseline_eq_extension atG k l m z hs]
  simp only [Angular.extension,FlatTStress.secantCharge,V]
  rw [show -(z-s)=s-z by ring,
    NegativeAPositiveTD.AffectedPositive.rotation_norm hl hc (Angular.affected atG k m) z,
    NegativeAPositiveTD.AffectedPositive.zero_norm hl (Angular.affected atG k m)]
  simp only [Angular.ratio,NegativeAPositiveTD.AffectedNegativeCurves.upper,secant,
    NegativeAPositiveTD.secant]
  rw [hcos]
  field_simp [hc.ne']
  ring

theorem affectedScalar_concave (atG : Bool) {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    ConcaveOn ℝ (Icc 0 (Real.tan z)) (affectedScalar atG z) := by
  have hr := ratio_bounds atG hz
  have hv := NegativeAPositiveTD.AffectedNorm.second_coordinate_pos
    ⟨hr.1.1,by linarith [hr.2]⟩ (Explicit.frame_domain .high (r68_hd hz))
  have hc := NegativeAPositiveTD.AffectedNegativeCurves.upper_concave
    (a:=0) (b:=Real.tan z) hv
  have hl : 0<Explicit.l .high z := by linarith [(Explicit.positive .high (r68_hd hz)).2.1]
  refine ⟨hc.1,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hc.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  have hp := mul_le_mul_of_nonneg_left hh hl.le
  simp only [affectedScalar]
  have hab' := congrArg (fun t : ℝ => t*(baseline atG (Explicit.k .high z)
    (Explicit.l .high z) (Explicit.m .high z) 0 z+
    Explicit.l .high z*(-1+R*OrdinaryCurvatureBounds.shape (ratio atG z)))) hab
  linarith

theorem affected_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (hsz : s≤z) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s z+
      V R (Angular.affected atG (Explicit.k .high z) (Explicit.m .high z))
        (secant (Explicit.l .high z) s) (z-s) := by
  have hl : 0<Explicit.l .high z := by linarith [(Explicit.positive .high (r68_hd hz)).2.1]
  have hzframe := Explicit.frame_domain .high (r68_hd hz)
  have hsf := (Explicit.angle_domain atG hs).2
  have he (a : ℝ) (ha : a∈Icc 0 frameCap) := affected_identity atG
    (k:=Explicit.k .high z) (m:=Explicit.m .high z) (z:=z) hl ha
  have hml := (Explicit.high_ratios hz).2.2.2.2
  have hzero : 0<affectedScalar atG z 0 := by
    have hh := he 0 (by norm_num [frameCap])
    simp only [Real.tan_zero] at hh
    have h2 : affectedScalar atG z 0=_ := hh.symm
    rw [h2,baseline_zero,sub_zero]
    have hsec : secant (Explicit.l .high z) 0=Explicit.l .high z := by
      simp [secant,NegativeAPositiveTD.secant]
    rw [hsec]
    cases atG
    · simpa only [Angular.affected,Bool.false_eq_true,↓reduceIte] using (high_endpoints hz).2.2.1
    · simpa only [Angular.affected,↓reduceIte] using (high_endpoints hz).2.1
  have hright : 0<affectedScalar atG z (Real.tan z) := by
    have h := he z hzframe
    simp only [sub_self,V_zero,add_zero] at h
    have h2 : affectedScalar atG z (Real.tan z)=_ := h.symm
    rw [h2]
    cases atG
    · exact (high_endpoints hz).2.2.2.2
    · exact (high_endpoints hz).2.2.2.1
  have hx : Real.tan s∈Icc 0 (Real.tan z) := ⟨tan_nonnegative hsf,tan_monotone hsf hzframe hsz⟩
  have hh := concave_gt_of_endpoints (affectedScalar_concave atG hz) hx hzero hright
  rw [he s hsf]
  exact hh

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.HighNegative
end
end
end

section
/-!
## Every pure-positive alternative reduces to equal angles

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
end
end
end

section
/-!
## The intrinsic scalar alternatives forced by the witnesses

For each coefficient family the weight ranges and the pair domains hold, and the witnesses of the
cycle make one intrinsic alternative `intrinsic` nonpositive (`original_intrinsic_nonpositive`).
This is the necessary inequality of the cycle itself; its intrinsic alternatives are then
compared with the fourteen scalar endpoints.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open Certificate (Family)

def intrinsic (atG : Bool) (k l c s z : ℝ) (i j : Fin 4) : ℝ :=
  baseline atG k l c s z+
    min (Concentration.pure R (GlobalGA.Secondary.diagonal-1/2)
      (pWeights atG k l (PositiveTD.tilted c z) s)
      (qWeights atG k l (PositiveTD.tilted c z) s) 3 i j s z)
      (Concentration.saturated R (GlobalGA.Secondary.diagonal-1/2)
        (pWeights atG k l (PositiveTD.tilted c z) s)
        (qWeights atG k l (PositiveTD.tilted c z) s) 3 i j s z)

theorem original_intrinsic_nonpositive {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Family) (atG : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ha : aError C atG=-s)
    (hflat : (C.point A).a=7/12)
    (hz : delta C.theta T∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hhg : hg=0 ∨ hg=2)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) :
    ∃i j,intrinsic atG (Explicit.k f (delta C.theta T))
      (Explicit.l f (delta C.theta T)) (Explicit.c f (delta C.theta T))
      s (delta C.theta T) i j≤0 := by
  let k := Explicit.k f (delta C.theta T)
  let l := Explicit.l f (delta C.theta T)
  let c := Explicit.c f (delta C.theta T)
  have hsf := (Explicit.angle_domain atG hs).2
  have hzf := Explicit.family_frame_domain f hz
  obtain ⟨hk,hG,hB,hc,hm⟩ := Explicit.family_coefficient_domain f atG hz hs
  have hpos := Explicit.family_positive f hz
  have hcoeff := Explicit.ordered_pair_domain f atG hz hs
  have hb := original_budgets hg atG k l c hsf.1 ha hvar hzf.1
  have hlo := original_stress_lower atG hsorted hcontained hq hHy hGy hBy hDy
    hvar hsf ha hflat hzf.1 hhg hk hG hB hc hm
  have hhi := stress_nonpositive atG hpos.1.le hpos.2.1.le hpos.2.2.1 hsf hzf
    hHG hGA hAB hBT hTD hDE hEH
  obtain ⟨i,j,hmin⟩ := Concentration.concentrate R (GlobalGA.Secondary.diagonal-1/2)
    (pWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s)
    (qWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s)
    (fun i => (blocks C hg atG k l c s i).P)
    (fun i => (blocks C hg atG k l c s i).N) 3
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hcoeff i).1) (fun i => (hcoeff i).2.1) (fun i => (hcoeff i).2.2)
    (fun i => (blocks C hg atG k l c s i).P_nonneg)
    (fun i => (blocks C hg atG k l c s i).N_nonneg)
    hsf hzf hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
  refine ⟨i,j,?_⟩
  change intrinsic atG k l c s (delta C.theta T) i j≤0
  dsimp [intrinsic]
  dsimp [k,l,c,Explicit.m] at hmin hlo hhi ⊢
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Source
end
end
end

section
/-!
## Removing the saturated alternatives on the high coefficient interval

The surplus is kept exactly. The four derivative margins are `.0105`, `.01325`, `.078` and
`.067`, with the linear positive piece of D included (`pure_le_saturated`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.HighSaturated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope OrdinaryPositiveEnvelope PositiveTD.Hybrid
open NegativeSlope

def fullCase (atG : Bool) : Lower := if atG then .GAfull else .ABfull
def halfCase (atG : Bool) : Lower := if atG then .GAhalf else .ABhalf
def largerCap (atG : Bool) : ℝ := if atG then 11/10 else 23/20

theorem case_angles (atG : Bool) :
    (lowerAngle (fullCase atG):ℝ)=frameCap ∧
    (lowerAngle (halfCase atG):ℝ)=(1/2:ℝ) ∧
    lowerRatio (halfCase atG)=lowerRatio (fullCase atG) := by
  cases atG <;> norm_num [fullCase,halfCase,lowerAngle,lowerRatio,frameCap]

theorem negative_growth (e : Lower) {p q x y : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hpr : (lowerRatio e:ℝ)*q≤p)
    (hx : x∈Icc 0 (lowerAngle e:ℝ)) (hy : y∈Icc 0 (lowerAngle e:ℝ))
    (hxy : x≤y) :
    (lowerValue e:ℝ)*q*(y-x)≤V R p q y-V R p q x := by
  have hq := hp.trans_le hpq
  have hd := lower_angle_domain e
  have hf (t : ℝ) (ht : t∈Icc 0 (lowerAngle e:ℝ)) :=
    V_hasDerivAt (R:=R) hp hq (show t∈Icc 0 frameCap from ⟨ht.1,ht.2.trans hd.2⟩)
  exact derivative_reserve
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => hf t (Ioo_subset_Icc_self ht))
    (fun t ht => (lower_bound e hp hpq hqp hpr (Ioo_subset_Icc_self ht)).le)
    hx hy hxy

variable {ι : Type*} [DecidableEq ι]

theorem positive_lower {p q : ι→ℝ} {d i : ι} {a t : ℝ}
    (ha : a≤2/5) (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (hq : 1≤q i) (ht : t∈Icc 0 frameCap) :
    -(109/200)*q i*t≤positive R a p q d i t := by
  by_cases hi : i=d
  · simp only [positive,ite_eq_left hi]
    have hm := mul_le_mul_of_nonneg_right
      (show a≤(109/200)*q i by linarith) ht.1
    linarith
  · simpa only [positive,ite_eq_right hi] using U_lower
      (Real.sqrt_nonneg qCap) (Real.sq_sqrt (by norm_num [qCap])).le hp hpq hqp ht

theorem positive_half_growth {p q : ι→ℝ} {d i : ι} {a x y : ℝ}
    (ha : a≤2/5) (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (hq : 1≤q i) (hx : x∈Icc 0 (1/2:ℝ)) (hy : y∈Icc 0 (1/2:ℝ))
    (hxy : x≤y) :
    -(31/50)*q i*(y-x)≤positive R a p q d i y-positive R a p q d i x := by
  by_cases hi : i=d
  · simp only [positive,ite_eq_left hi]
    have hm := mul_le_mul_of_nonneg_right
      (show a≤(31/50)*q i by linarith) (sub_nonneg.mpr hxy)
    linarith
  · simp only [positive,ite_eq_right hi]
    have hf (t : ℝ) (ht : t∈Icc 0 (1/2:ℝ)) :=
      PositiveSlope.U_hasDerivAt hp (hp.trans_le hpq)
        (show t∈Icc 0 frameCap by exact ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩)
    exact derivative_reserve
      (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
      (fun t ht => hf t (Ioo_subset_Icc_self ht))
      (fun t ht => (PositiveSlope.half_bound hp hpq hqp (Ioo_subset_Icc_self ht)).le)
      hx hy hxy

theorem pure_le_saturated (atG : Bool) {p q : ι→ℝ} {d i j : ι} {a s z : ℝ}
    (ha : a≤2/5)
    (hp : ∀i,0<p i) (hpq : ∀i,p i≤q i) (hqp : ∀i,q i≤2*p i)
    (hqlo : ∀i,1≤q i) (hqhi : ∀i,q i≤largerCap atG)
    (hratio : ∀i,(lowerRatio (fullCase atG):ℝ)*q i≤p i)
    (hsine : ∀i,q i*Real.sin (frameCap-s)≤p i)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc (1/5:ℝ) frameCap) :
    Concentration.pure R a p q d i j s z≤
      Concentration.saturated R a p q d i j s z := by
  let P : ℝ := frameCap-z
  let N : ℝ := frameCap-s
  have hP : P∈Icc 0 frameCap := by
    dsimp [P]
    exact ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hPhalf : P∈Icc 0 (1/2:ℝ) := by
    dsimp [P,frameCap] at ⊢
    dsimp [frameCap] at hz
    exact ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hN : N∈Icc 0 frameCap := by
    dsimp [N]
    exact ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hf (a₁ a₂ : ℝ) (h₁ : a₁∈Icc 0 frameCap)
      (h₂ : a₂∈Icc 0 frameCap) (h₁₂ : a₁≤a₂) (k : ι) :
      (lowerValue (fullCase atG):ℝ)*q k*(a₂-a₁)≤V R (p k) (q k) a₂-V R (p k) (q k) a₁ := by
    apply negative_growth (fullCase atG) (hp k) (hpq k) (hqp k) (hratio k)
    · simpa only [(case_angles atG).1] using h₁
    · simpa only [(case_angles atG).1] using h₂
    · exact h₁₂
  have hh (a₁ a₂ : ℝ) (h₁ : a₁∈Icc 0 (1/2:ℝ))
      (h₂ : a₂∈Icc 0 (1/2:ℝ)) (h₁₂ : a₁≤a₂) (k : ι) :
      (lowerValue (halfCase atG):ℝ)*q k*(a₂-a₁)≤V R (p k) (q k) a₂-V R (p k) (q k) a₁ := by
    apply negative_growth (halfCase atG) (hp k) (hpq k) (hqp k)
    · simpa only [(case_angles atG).2.2] using hratio k
    · simpa only [(case_angles atG).2.1] using h₁
    · simpa only [(case_angles atG).2.1] using h₂
    · exact h₁₂
  have hpay (k : ι) : a≤(lowerValue (fullCase atG):ℝ)*q k := by
    have hq := hqlo k
    cases atG <;> norm_num [fullCase,lowerValue] at ⊢ <;> linarith
  by_cases hsz : s≤z
  · have hPN : P≤N := by dsimp [P,N]; linarith
    have hsurplus : N-P=z-s := by dsimp [P,N]; ring
    have hdiff : N-P∈Icc 0 frameCap :=
      ⟨by linarith,by linarith [hN.2,hP.1]⟩
    simp only [Concentration.pure,ite_eq_left hsz,Concentration.saturated]
    by_cases hij : i=j
    · subst j
      simp only
      by_cases hid : i=d
      · simp only [block,ite_eq_left hid,↓reduceIte]
        have hg := hf (N-P) N hdiff hN (by linarith [hP.1]) i
        have hp₁ := mul_le_mul_of_nonneg_right (hpay i) hP.1
        rw [hsurplus] at hg
        change V R (p i) (q i) (z-s)≤ -a*P+V R (p i) (q i) N
        nlinarith
      · simp only [block,ite_eq_right hid,↓reduceIte]
        have hsine' : q i*Real.sin N≤p i := by simpa [N] using hsine i
        have hc := SameBlock.negative_surplus (hp i).le
          (show P∈Icc 0 N from ⟨hP.1,hPN⟩) hN hsine'
        simpa only [hsurplus] using hc
    · simp only [ite_eq_right hij]
      have hg := hf (N-P) N hdiff hN (by linarith [hP.1]) j
      have hu := positive_lower (d:=d) ha (hp i) (hpq i) (hqp i) (hqlo i) hP
      have hqi := mul_le_mul_of_nonneg_right (hqhi i) hP.1
      have hqj := mul_le_mul_of_nonneg_right (hqlo j) hP.1
      rw [show N-(N-P)=P by ring,hsurplus] at hg
      change V R (p j) (q j) (z-s)≤positive R a p q d i P+V R (p j) (q j) N
      generalize R=R0 at hg hu ⊢
      cases atG <;> norm_num [fullCase,lowerValue,largerCap] at hg hqi <;> linarith [hP.1]
  · have hzs : z ≤ s := (lt_of_not_ge hsz).le
    have hNP : N≤P := by dsimp [P,N]; linarith
    have hsurplus : P-N=s-z := by dsimp [P,N]; ring
    have hdiff : P-N∈Icc 0 (1/2:ℝ) :=
      ⟨by linarith,by linarith [hPhalf.2,hN.1]⟩
    have hNhalf : N∈Icc 0 (1/2:ℝ) := ⟨hN.1,hNP.trans hPhalf.2⟩
    simp only [Concentration.pure,ite_eq_right hsz,Concentration.saturated]
    by_cases hij : i=j
    · subst j
      simp only
      by_cases hid : i=d
      · simp only [block,positive,ite_eq_left hid,↓reduceIte]
        have hg := hf 0 N (by norm_num [frameCap]) hN hN.1 i
        have hp₁ := mul_le_mul_of_nonneg_right (hpay i) hN.1
        simp only [V_zero,sub_zero] at hg
        change -a*(s-z)≤ -a*P+V R (p i) (q i) N
        rw [←hsurplus]
        nlinarith
      · simp only [block,positive,ite_eq_right hid,↓reduceIte]
        have hratio' : q i≤(17/10)*p i := by
          have hr := hratio i
          have hq := hqlo i
          cases atG <;> norm_num [fullCase,lowerRatio] at hr <;> linarith
        have hc := SameBlock.positive_surplus (hp i).le hratio' hP ⟨hN.1,hNP⟩
        simpa only [hsurplus] using hc
    · simp only [ite_eq_right hij]
      have hg := hh 0 N (by norm_num) hNhalf hN.1 j
      have hu := positive_half_growth (d:=d) ha (hp i) (hpq i) (hqp i)
        (hqlo i) hdiff hPhalf (by linarith [hN.1])
      have hqi := mul_le_mul_of_nonneg_right (hqhi i) hN.1
      have hqj := mul_le_mul_of_nonneg_right (hqlo j) hN.1
      simp only [V_zero,sub_zero] at hg
      rw [hsurplus] at hu
      change positive R a p q d i (s-z)≤positive R a p q d i P+V R (p j) (q j) N
      generalize R=R0 at hg hu ⊢
      cases atG <;> norm_num [halfCase,lowerValue,largerCap] at hg hqi <;> linarith [hN.1]

theorem explicit_sine_condition (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i : Fin 4) :
    Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i*
        Real.sin (frameCap-s)≤
      Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i := by
  have hsf := (Explicit.angle_domain atG hs).2
  have hN : frameCap-s∈Icc 0 frameCap :=
    ⟨by linarith [hsf.2],by linarith [hsf.1]⟩
  have hsin := (transport_trig hN).2.2.2.1
  cases atG
  · have hb := Explicit.high_AB_pair_bounds hz hs i
    have hq0 : 0≤Source.qWeights false (Explicit.k .high z) (Explicit.l .high z)
        (Explicit.m .high z) s i := by linarith [hb.2.1]
    have hh := mul_le_mul_of_nonneg_left hsin.le hq0
    nlinarith [hb.1]
  · obtain ⟨hklo,hkhi,hllo,hlhi,_,_,_,_⟩ := Explicit.high_ranges hz
    have hkl := Explicit.high_ratio_lower hz
    have hml := Explicit.high_tilted hz
    have hl : 0<Explicit.l .high z := by linarith
    have hm : 0<Explicit.m .high z := by linarith [hml.1]
    fin_cases i
    · change (1:ℝ)*Real.sin (frameCap-s)≤Explicit.k .high z
      linarith
    · change lambdaG true (Explicit.l .high z) s*Real.sin (frameCap-s)≤Explicit.k .high z
      simp only [lambdaG,↓reduceIte]
      have ht := transport_trig hsf
      have hc : 0<Real.cos s := by linarith [ht.1]
      have hcap := transport_trig
        (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
      have hprod : 0≤Real.cos frameCap*Real.sin s :=
        mul_nonneg (by linarith [hcap.1]) ht.2.2.1
      have hsine : Real.sin (frameCap-s)≤Real.sin frameCap*Real.cos s := by
        rw [Real.sin_sub]
        linarith
      have hscaled := mul_le_mul_of_nonneg_left hsine hl.le
      have hsec : secant (Explicit.l .high z) s*Real.sin (frameCap-s)≤
          Explicit.l .high z*Real.sin frameCap := by
        dsimp [secant]
        rw [div_mul_eq_mul_div,div_le_iff₀ hc]
        nlinarith only [hscaled]
      have hright := mul_le_mul_of_nonneg_left hcap.2.2.2.1.le hl.le
      linarith
    · change max (lambdaB true (Explicit.l .high z) s) (Explicit.m .high z)*
          Real.sin (frameCap-s)≤ min (lambdaB true (Explicit.l .high z) s) (Explicit.m .high z)
      simp only [lambdaB,↓reduceIte]
      rcases le_total (Explicit.l .high z) (Explicit.m .high z) with hle | hle
      · rw [max_eq_right hle,min_eq_left hle]
        have hh := mul_le_mul_of_nonneg_left hsin.le hm.le
        nlinarith [hml.2.1]
      · rw [max_eq_left hle,min_eq_right hle]
        have hh := mul_le_mul_of_nonneg_left hsin.le hl.le
        nlinarith [hml.1]
    · change (1:ℝ)*Real.sin (frameCap-s)≤Explicit.k .high z
      linarith

private theorem r70_high_dom {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    z∈Icc (Certificate.left .high:ℝ) (Certificate.right .high:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split,PositiveTD.Certificate.h]
  exact hz

theorem explicit_pure_le_saturated (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i j : Fin 4) :
    Concentration.pure R (GlobalGA.Secondary.diagonal-1/2)
      (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
      (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
      3 i j s z≤
    Concentration.saturated R (GlobalGA.Secondary.diagonal-1/2)
      (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
      (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
      3 i j s z := by
  have hp := Explicit.ordered_pair_domain .high atG (r70_high_dom hz) hs
  have hb (i : Fin 4) :
      (lowerRatio (fullCase atG):ℝ)*
          Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i<
        Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i ∧
      1≤Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i ∧
      Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i<largerCap atG := by
    cases atG
    · simpa [fullCase,lowerRatio,largerCap] using Explicit.high_AB_pair_bounds hz hs i
    · simpa [fullCase,lowerRatio,largerCap] using Explicit.high_GA_pair_bounds hz hs i
  exact pure_le_saturated atG (by linarith [diagonal_bounds.2])
    (fun i => (hp i).1) (fun i => (hp i).2.1) (fun i => (hp i).2.2)
    (fun i => (hb i).2.1) (fun i => (hb i).2.2.le) (fun i => (hb i).1.le)
    (explicit_sine_condition atG hz hs) (Explicit.angle_domain atG hs).2 hz

theorem intrinsic_eq_pure (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i j : Fin 4) :
    Source.intrinsic atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z i j=
      baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z+
        Concentration.pure R (GlobalGA.Secondary.diagonal-1/2)
          (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
          (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
          3 i j s z := by
  have hh := explicit_pure_le_saturated atG hz hs i j
  have hm : Explicit.m .high z=PositiveTD.tilted (Explicit.c .high z) z := rfl
  rw [hm] at hh
  simp only [Source.intrinsic,hm]
  rw [min_eq_left hh]

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.HighSaturated
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.High
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeEnvelope
open NegativeAPositiveTD.HighSaturated NegativeAPositiveTD.NegativeSlope

private theorem r68_hd {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    z∈Icc (Certificate.left .high:ℝ) (Certificate.right .high:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]
  exact hz

private theorem r68_cut_false {s : ℝ} (hs : s∈Icc 0 (Explicit.angleCut false)) :
    s∈Icc 0 (19/50:ℝ) := by
  simpa [Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut] using hs

private theorem r68_cut_true {s : ℝ} (hs : s∈Icc 0 (Explicit.angleCut true)) :
    s∈Icc 0 (1/4:ℝ) := by
  simpa [Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut] using hs

theorem ordinary_pure_le_saturated (atG : Bool) {p q : Fin 4→ℝ} {i j : Fin 4} {s z : ℝ}
    (hp : ∀i,0<p i) (hpq : ∀i,p i≤q i) (hqp : ∀i,q i≤2*p i)
    (hqlo : ∀i,1≤q i) (hqhi : ∀i,q i≤largerCap atG)
    (hratio : ∀i,(lowerRatio (fullCase atG):ℝ)*q i≤p i)
    (hsine : ∀i,q i*Real.sin (frameCap-s)≤p i)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc (1/5:ℝ) frameCap) :
    Concentration.pure .high p q i j s z≤Concentration.saturated .high p q i j s z := by
  let p' : Option (Fin 4)→ℝ := fun x => x.elim 1 p
  let q' : Option (Fin 4)→ℝ := fun x => x.elim 1 q
  have hp' (x : Option (Fin 4)) : 0<p' x := by
    cases x with
    | none => norm_num [p']
    | some k => exact hp k
  have hpq' (x : Option (Fin 4)) : p' x≤q' x := by
    cases x with
    | none => norm_num [p',q']
    | some k => exact hpq k
  have hqp' (x : Option (Fin 4)) : q' x≤2*p' x := by
    cases x with
    | none => norm_num [p',q']
    | some k => exact hqp k
  have hqlo' (x : Option (Fin 4)) : 1≤q' x := by
    cases x with
    | none => norm_num [q']
    | some k => exact hqlo k
  have hqhi' (x : Option (Fin 4)) : q' x≤largerCap atG := by
    cases x with
    | none => cases atG <;> norm_num [q',largerCap]
    | some k => exact hqhi k
  have hr' (x : Option (Fin 4)) : (lowerRatio (fullCase atG):ℝ)*q' x≤p' x := by
    cases x with
    | none => cases atG <;> norm_num [p',q',fullCase,lowerRatio]
    | some k => exact hratio k
  have hsin' (x : Option (Fin 4)) : q' x*Real.sin (frameCap-s)≤p' x := by
    cases x with
    | none => simpa [p',q'] using Real.sin_le_one (frameCap-s)
    | some k => exact hsine k
  have hh := NegativeAPositiveTD.HighSaturated.pure_le_saturated atG
    (d:=(none:Option (Fin 4))) (i:=some i) (j:=some j) (a:=0) (by norm_num)
    hp' hpq' hqp' hqlo' hqhi' hr' hsin' hs hz
  simpa [Concentration.pure,Concentration.saturated,Concentration.positive,Concentration.block,
    NegativeAPositiveTD.Concentration.pure,NegativeAPositiveTD.Concentration.saturated,
    PositiveTD.Hybrid.positive,PositiveTD.Hybrid.block,p',q'] using hh

theorem sine_condition (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i : Fin 4) :
    Explicit.q .high atG z s i*Real.sin (frameCap-s)≤Explicit.p .high atG z s i := by
  have hsf := (Explicit.angle_domain atG hs).2
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hsf.2],by linarith [hsf.1]⟩
  have hsin := (transport_trig hN).2.2.2.1
  cases atG
  · have hb := Explicit.high_AB_pair_bounds hz (r68_cut_false hs) i
    have hh := mul_le_mul_of_nonneg_left hsin.le
      (show 0≤Explicit.q .high false z s i by linarith [hb.2.1])
    nlinarith [hb.1]
  · have hb := Explicit.high_ranges hz
    have hr := Explicit.high_ratios hz
    have hc := Explicit.high_rotation hz
    have hl : 0<Explicit.l .high z := by linarith [hb.2.1.1]
    fin_cases i
    · simp only [Explicit.p,Explicit.q,pWeights,qWeights,Fin.reduceFinMk,Matrix.cons_val,one_mul]
      linarith [hb.1.1]
    · simp only [Explicit.p,Explicit.q,pWeights,qWeights,lambdaG,NegativeAPositiveTD.lambdaG,
        ↓reduceIte,Fin.reduceFinMk,Matrix.cons_val]
      have ht := transport_trig hsf
      have hcos : 0<Real.cos s := by linarith [ht.1]
      have hcap := transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
      have hprod := mul_nonneg (show 0≤Real.cos frameCap by linarith [hcap.1]) ht.2.2.1
      have hsine : Real.sin (frameCap-s)≤Real.sin frameCap*Real.cos s := by
        rw [Real.sin_sub]
        linarith
      have hscaled := mul_le_mul_of_nonneg_left hsine hl.le
      have hsec : secant (Explicit.l .high z) s*Real.sin (frameCap-s)≤
          Explicit.l .high z*Real.sin frameCap := by
        simp only [secant,NegativeAPositiveTD.secant]
        rw [div_mul_eq_mul_div,div_le_iff₀ hcos]
        linarith only [hscaled]
      have hright := mul_le_mul_of_nonneg_left hcap.2.2.2.1.le hl.le
      linarith [hr.1]
    · simp only [Explicit.p,Explicit.q,pWeights,qWeights,lambdaB,NegativeAPositiveTD.lambdaB,
        ↓reduceIte,Fin.reduceFinMk,Matrix.cons_val,
        min_eq_right hr.2.2.2.2.le,max_eq_left hr.2.2.2.2.le]
      have hh := mul_le_mul_of_nonneg_left hsin.le hl.le
      linarith [hr.2.2.1]
    · simp only [Explicit.p,Explicit.q,pWeights,qWeights,reduceCtorEq,↓reduceIte,
        Fin.reduceFinMk,Matrix.cons_val,min_eq_right hc.2.2.le,max_eq_left hc.2.2.le,one_mul]
      linarith [hc.1]

theorem pure_le_saturated (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    Concentration.pure .high (Explicit.p .high atG z s) (Explicit.q .high atG z s) i j s z≤
      Concentration.saturated .high (Explicit.p .high atG z s) (Explicit.q .high atG z s) i j s z := by
  have hp := Explicit.ordered_pair_domain .high atG (r68_hd hz) hs
  have hb (i : Fin 4) :
      (lowerRatio (fullCase atG):ℝ)*Explicit.q .high atG z s i<Explicit.p .high atG z s i ∧
      1≤Explicit.q .high atG z s i ∧ Explicit.q .high atG z s i<largerCap atG := by
    cases atG
    · simpa [fullCase,lowerRatio,largerCap] using
        Explicit.high_AB_pair_bounds hz (r68_cut_false hs) i
    · simpa [fullCase,lowerRatio,largerCap] using
        Explicit.high_GA_pair_bounds hz (r68_cut_true hs) i
  exact ordinary_pure_le_saturated atG (fun i => (hp i).1) (fun i => (hp i).2.1)
    (fun i => (hp i).2.2) (fun i => (hb i).2.1) (fun i => (hb i).2.2.le)
    (fun i => (hb i).1.le) (sine_condition atG hz hs) (Explicit.angle_domain atG hs).2
    ⟨by linarith [hz.1],by simp only [frameCap]; exact hz.2⟩

theorem D_dominates_H {z t : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (ht : t∈Icc 0 frameCap) :
    V R (Explicit.k .high z) 1 t≤V R (Explicit.c .high z) 1 t := by
  have hb := Explicit.basic_domain .high (r68_hd hz)
  have hc := Explicit.high_rotation hz
  exact V_monotone_smaller (Real.sqrt_nonneg _) (by norm_num) ht
    ⟨by linarith [hb.1.1],by linarith [hb.1.2]⟩
    ⟨by linarith [hc.1],hc.2.2.le⟩ hc.2.1.le

theorem negative_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (hsz : s≤z) (i : Fin 4) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s z+
      V R (Explicit.p .high atG z s i) (Explicit.q .high atG z s i) (z-s) := by
  by_cases hiD : i=3
  · subst i
    have hh := HighNegative.unaffected_positive atG hz hs hsz 0
      (by cases atG <;> exact Or.inl rfl)
    have hc := Explicit.high_rotation hz
    have hd := D_dominates_H hz (show z-s∈Icc 0 frameCap from
      ⟨by linarith,by simp only [frameCap]; linarith [hs.1,hz.2]⟩)
    simp only [Explicit.p,Explicit.q,pWeights,qWeights,reduceCtorEq,↓reduceIte,Matrix.cons_val,
      min_eq_right hc.2.2.le,max_eq_left hc.2.2.le] at hh ⊢
    linarith
  by_cases hu : HighNegative.Unaffected atG i
  · exact HighNegative.unaffected_positive atG hz hs hsz i hu
  · have ha := HighNegative.affected_positive atG hz hs hsz
    have hml := (Explicit.high_ratios hz).2.2.2.2
    have hw := (Explicit.secant_bounds .high atG (r68_hd hz) hs).1
    cases atG
    · have hi2 : i=2 := by
        fin_cases i <;> simp_all [HighNegative.Unaffected]
      subst hi2
      simp only [Explicit.p,Explicit.q,pWeights,qWeights,Matrix.cons_val,lambdaB,
        NegativeAPositiveTD.lambdaB,Bool.false_eq_true,↓reduceIte,
        min_eq_right (hml.le.trans hw),max_eq_left (hml.le.trans hw)]
      simpa only [Angular.affected,Bool.false_eq_true,↓reduceIte] using ha
    · have hi1 : i=1 := by
        fin_cases i <;> simp_all [HighNegative.Unaffected]
      subst hi1
      simp only [Explicit.p,Explicit.q,pWeights,qWeights,Matrix.cons_val,lambdaG,
        NegativeAPositiveTD.lambdaG,↓reduceIte]
      simpa only [Angular.affected,↓reduceIte] using ha

theorem pure_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s z+
      Concentration.pure .high (Explicit.p .high atG z s) (Explicit.q .high atG z s) i j s z := by
  by_cases hsz : s≤z
  · simpa only [Concentration.pure,hsz,↓reduceIte] using negative_positive atG hz hs hsz j
  · have hh := Positive.reduces_to_equal .high atG (r68_hd hz) hs (le_of_not_ge hsz) i
    have he : 0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z z := by
      cases atG
      · exact (high_endpoints hz).2.2.2.2
      · exact (high_endpoints hz).2.2.2.1
    simp only [Concentration.pure,hsz,↓reduceIte]
    linarith

theorem intrinsic_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s z+
      min (Concentration.pure .high (Explicit.p .high atG z s) (Explicit.q .high atG z s) i j s z)
        (Concentration.saturated .high (Explicit.p .high atG z s) (Explicit.q .high atG z s) i j s z) := by
  rw [min_eq_left (pure_le_saturated atG hz hs i j)]
  exact pure_positive atG hz hs i j

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.High
end
end
end
