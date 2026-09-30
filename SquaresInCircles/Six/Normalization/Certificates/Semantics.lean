import SquaresInCircles.Six.Normalization.Certificates.Checks
import SquaresInCircles.Six.ProofTools.FormulaLemmas

/-!
# The geometric meaning of the concrete checks

Every hypothesis below is a real containment, separator, or coordinate bound.
The Boolean equalities used internally have proofs in Checks.lean; callers
never supply a certificate-success assumption.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization.Certificates
open ProofTools

lemma basicE_holds {n : ℕ} (x : Fin n → ℝ) (t a b xl xh yl yh : Expr n)
    (hc : ContainedChart (Expr.denote a x) |Expr.denote b x|)
    (hs : ∃ k, 0 ≤ centralUpper k (Expr.denote t x) (Expr.denote a x) (Expr.denote b x)
      (Expr.denote xl x) (Expr.denote xh x) (Expr.denote yl x) (Expr.denote yh x)) :
    Formula.Holds (basicE t a b xl xh yl yh) x := by
  unfold basicE
  simp only [Formula.all,List.foldr_cons,List.foldr_nil,Formula.Holds]
  refine ⟨?_,?_,?_,?_,True.intro⟩
  · simpa [Expr.denote] using hc.half_le
  · simpa [Expr.denote] using hc.u_le
  · simpa [containE,Expr.denote,phi] using hc.containment
  · apply (Formula.holds_any_map x CentralAxis.all _).mpr
    obtain ⟨k,hk⟩ := hs
    exact ⟨k,CentralAxis.mem_all k,by simpa [Formula.Holds,Expr.denote] using hk⟩

lemma baseRoot_mem {t a b : ℝ} (ht : |t| ≤ Real.pi) (hc : ContainedChart a |b|) :
    baseRoot.Mem ![t,a,b] := by
  have ht' := abs_le.mp ht
  have hpi : Real.pi < (22:ℝ)/7 := by linarith [Real.pi_lt_d4]
  have ha := hc.a_le_rho0
  have hb := hc.u_lt_seven_tenths
  have hb' := abs_lt.mp hb
  intro i
  fin_cases i <;> norm_num [baseRoot,RInterval.Mem] <;> constructor <;>
    linarith [ht'.1,ht'.2,hpi,hc.half_le,ha,rho0_upper,hb'.1,hb'.2]

lemma pinMargin_pos_iff {t a b : ℝ} {q : Point} :
    0 < pinMargin t a b q ↔ openSquare (orientedSquare t a b) q := by
  rw [openSquare,orientedSquare_localX,orientedSquare_localY]
  dsimp [pinMargin]
  constructor
  · intro h
    have hh : max |q.1*Real.cos t+q.2*Real.sin t-a|
      |-q.1*Real.sin t+q.2*Real.cos t-b| < 1/2 := by linarith
    exact max_lt_iff.mp hh
  · intro h
    have hh := max_lt h.1 h.2
    linarith

/-- The five-pin covering statement for a chart in the strong central box. -/
theorem pin_cover_from_upper {t a b : ℝ} (ht : |t| ≤ Real.pi)
    (hc : ContainedChart a |b|)
    (hs : ∃ k, 0 ≤ centralUpper k t a b 0 c0 0 c0) :
    ∃ i : Fin 5, openSquare (orientedSquare t a b) (fixedPin i) := by
  have hx := baseRoot_mem ht hc
  have hcert := certify_sound pinCoverFormula (fun _ => 1) 0 64 pinCover_checked hx
  have hbasic : Formula.Holds
      (basicE (.var 0) (.var 1) (.var 2) 0 c0E 0 c0E) ![t,a,b] := by
    apply basicE_holds
    · simpa [Expr.denote] using hc
    · simpa [Expr.denote] using hs
  have hresult := hcert hbasic
  obtain ⟨i,_,hi⟩ := (Formula.holds_any_map ![t,a,b] (List.finRange 5) _).mp hresult
  have hm : (1:ℝ)/100 < pinMargin t a b (fixedPin i) := by
    simpa [Formula.Holds,Expr.denote] using hi
  exact ⟨i,pinMargin_pos_iff.mp (by linarith)⟩

lemma windowRoot_mem {t a b : ℝ} (i : Fin 5)
    (ht : -Real.pi ≤ t-phaseCenter i ∧ t-phaseCenter i ≤ Real.pi)
    (hc : ContainedChart a |b|) : (windowRoot i).Mem ![t,a,b] := by
  have ha := hc.a_le_rho0
  have hb := abs_lt.mp hc.u_lt_seven_tenths
  have hpi : Real.pi < (22:ℝ)/7 := by linarith [Real.pi_lt_d4]
  intro j
  fin_cases j
  · fin_cases i <;> norm_num [windowRoot,windowPhaseRoot,phaseCenter,RInterval.Mem] at * <;>
      constructor <;> linarith [Real.pi_gt_d2,Real.pi_lt_d4]
  · norm_num [windowRoot,RInterval.Mem]
    exact ⟨hc.half_le,by linarith [rho0_upper]⟩
  · norm_num [windowRoot,RInterval.Mem]
    exact ⟨by linarith [hb.1],by linarith [hb.2]⟩

/-- D1/D2's five windows and excluded cardinal directions, in each pin's lift. -/
theorem window_from_upper {t a b : ℝ} (i : Fin 5)
    (ht : -Real.pi ≤ t-phaseCenter i ∧ t-phaseCenter i ≤ Real.pi)
    (hc : ContainedChart a |b|)
    (hs : ∃ k, 0 ≤ centralUpper k t a b 0 c0 0 c0)
    (hpin : openSquare (orientedSquare t a b) (fixedPin i)) :
    ((windowLower i : ℝ) < t-phaseCenter i ∧ t-phaseCenter i < (windowUpper i : ℝ)) ∧
      (∀ k : CentralAxis, k ∉ allowed i → centralUpper k t a b 0 c0 0 c0 < 0) := by
  have hx := windowRoot_mem i ht hc
  have hcert := certify_sound (windowFormula i) (fun _ => 1) 0 64 (window_checked i) hx
  have hbasic : Formula.Holds
      (basicE (.var 0) (.var 1) (.var 2) 0 c0E 0 c0E) ![t,a,b] := by
    apply basicE_holds
    · simpa [Expr.denote] using hc
    · simpa [Expr.denote] using hs
  have hpm : Formula.Holds
      (.lt 0 (pinMarginE (.var 0) (.var 1) (.var 2) (pinE i).1 (pinE i).2)) ![t,a,b] := by
    simpa [Formula.Holds,Expr.denote] using pinMargin_pos_iff.mpr hpin
  have hresult := hcert ⟨hbasic,hpm⟩
  have hsplit := (Formula.holds_all_append ![t,a,b] _ _).mp hresult
  refine ⟨?_,?_⟩
  · simpa [Formula.all,Formula.Holds,Expr.denote] using hsplit.1
  · intro k hk
    have hm := (Formula.holds_all_map ![t,a,b] _ _).mp hsplit.2
    have hkin : k ∈ CentralAxis.all.filter (fun z => z ∉ allowed i) := by
      simp [CentralAxis.mem_all,hk]
    have hh := hm k hkin
    simpa [Formula.Holds,Expr.denote] using hh

lemma movingRoot_mem {t a b cx : ℝ}
    (ht : -5/12 < t ∧ t < 3/10) (hc : ContainedChart a |b|)
    (ha : 177/200 < a) (hb : |b| < 117/250)
    (hx0 : 0 ≤ cx) (hx : cx ≤ c0) : movingRoot.Mem ![t,a,b,cx] := by
  have hab := hc.a_le_rho0
  have hbb := abs_lt.mp hb
  have hcx : cx < 113/1000 := by dsimp [c0] at hx; linarith [rho0_upper]
  intro i
  fin_cases i <;> norm_num [movingRoot,RInterval.Mem] <;> constructor <;>
    linarith [ht.1,ht.2,ha,hab,hbb.1,hbb.2,hx0,hcx,rho0_upper]

/-- Lemma G, obtained from containment and OWN in the stated E window. -/
theorem own_moving_pin_from_margin {t a b cx cy : ℝ}
    (ht : -5/12 < t ∧ t < 3/10) (hc : ContainedChart a |b|)
    (ha : 177/200 < a) (hb : |b| < 117/250)
    (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy) (hx : cx ≤ c0) (hy : cy ≤ c0)
    (hown : 0 ≤ centralMargin .own t a b cx cy) :
    openSquare (orientedSquare t a b) (1+cx,0) := by
  have hupper := hown.trans
    (centralMargin_le_upper (xl := cx) (xh := cx) ⟨le_rfl,le_rfl⟩ ⟨hy0,hy⟩ .own)
  have hroot := movingRoot_mem ht hc ha hb hx0 hx
  have hcert := certify_sound movingFormula (fun _ => 1) 0 64 moving_checked hroot
  have hinput : Formula.Holds
      (.all [.le (r (1/2)) (.var 1),.le (.abs (.var 2)) (.var 1),
        .le (containE (.var 1) (.var 2)) q0E,.le (.var 3) c0E,
        .le 0 (upperE .own (.var 0) (.var 1) (.var 2) (.var 3) (.var 3) 0 c0E)])
      ![t,a,b,cx] := by
    simpa [Formula.all,Formula.Holds,Expr.denote,containE,phi] using
      And.intro hc.half_le (And.intro hc.u_le (And.intro hc.containment (And.intro hx hupper)))
  have hresult := hcert hinput
  have hm : (1:ℝ)/20 < pinMargin t a b (1+cx,0) := by
    simpa [Formula.Holds,Expr.denote] using hresult
  exact pinMargin_pos_iff.mp (by linarith)

end SquaresInCircles.Six.Normalization.Certificates
