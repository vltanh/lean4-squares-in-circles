module
public import SquaresInCircles.Six.Normalization.Certificates.Semantics
public import SquaresInCircles.Six.Normalization.OwnEastExclusion

@[expose] public section

/-!
# Lemma A from the checked reduced-separator predicates

CE is dropped only after the proved cx>c0 exclusion. OWN in the east quadrant
is dropped only after the proved A0 exclusion. The remaining disjunction is a
necessary consequence of actual SAT; no normalized sector or pin is assumed.
The weaker rational arcs are the sufficient arcs in section 8 of the supplied
manuscript, rather than its sharp endpoint formulas.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization.Certificates
open ProofTools

def ReducedUpper (t a b xl xh yl yh : ℝ) : Prop :=
  (((t < -Real.pi/4 ∨ Real.pi/4 < t) ∧ 0 ≤ centralUpper .own t a b xl xh yl yh) ∨
    0 ≤ centralUpper .secPlus t a b xl xh yl yh ∨
    0 ≤ centralUpper .secMinus t a b xl xh yl yh ∨
    0 ≤ centralUpper .west t a b xl xh yl yh ∨
    0 ≤ centralUpper .north t a b xl xh yl yh ∨
    0 ≤ centralUpper .south t a b xl xh yl yh)

lemma reducedUpper_of_actual {t a b cx cy xl xh yl yh : ℝ}
    (hc : ContainedChart a |b|) (hx : c0 < cx) (hy0 : 0 ≤ cy) (hy : cy ≤ cx+1/10)
    (hxbox : xl ≤ cx ∧ cx ≤ xh) (hybox : yl ≤ cy ∧ cy ≤ yh)
    (hs : ∃ k, 0 ≤ centralMargin k t a b cx cy) : ReducedUpper t a b xl xh yl yh := by
  obtain ⟨k,hk⟩ := hs
  have hu := hk.trans (centralMargin_le_upper hxbox hybox k)
  cases k
  · have hout : t < -Real.pi/4 ∨ Real.pi/4 < t := by
      by_cases h : t < -Real.pi/4
      · exact Or.inl h
      · right
        by_contra! ht
        have hangle : |t| ≤ Real.pi/4 := abs_le.mpr ⟨by linarith,ht⟩
        have hm := own_east_margin_negative hc.a_le_rho0 hx hy0 hy hangle
        change 0 ≤ a-1/2-(cx*Real.cos t+cy*Real.sin t)-
          (|Real.cos t|+|Real.sin t|)/2 at hk
        linarith
    exact Or.inl ⟨hout,hu⟩
  · exact Or.inr (Or.inl hu)
  · exact Or.inr (Or.inr (Or.inl hu))
  · have hm := east_separator_negative (t := t) hc hx
    change 0 ≤ a*Real.cos t-b*Real.sin t-
      (|Real.cos t|+|Real.sin t|)/2-cx-1/2 at hk
    linarith
  · exact Or.inr (Or.inr (Or.inr (Or.inl hu)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))

lemma arcOutsideE_middle {n : ℕ} (x : Fin n → ℝ) (m : Expr n) (am ap : ℚ)
    (h : Formula.Holds (arcOutsideE m am ap) x) :
    Expr.denote m x ≤ -(am:ℝ) ∨ (ap:ℝ) ≤ Expr.denote m x := by
  have hh := (Formula.holds_all_map x ([-1,0,1] : List ℤ) _).mp h
  have hz := hh 0 (by simp)
  simpa [Formula.Holds,Expr.denote] using hz

private lemma cone_from_check (xl xh yl yh : Expr 3) (am ap : ℚ)
    (hcheck : certify (coneFormula xl xh yl yh am ap) (fun _ => 1) 0 64 baseRoot = true)
    {t a b : ℝ} (ht : |t| ≤ Real.pi) (hc : ContainedChart a |b|)
    (hs : ReducedUpper t a b (Expr.denote xl ![t,a,b]) (Expr.denote xh ![t,a,b])
      (Expr.denote yl ![t,a,b]) (Expr.denote yh ![t,a,b])) :
    liftedMarker t a b ≤ -(am:ℝ) ∨ (ap:ℝ) ≤ liftedMarker t a b := by
  have hroot := baseRoot_mem ht hc
  have hcert := certify_sound (coneFormula xl xh yl yh am ap) (fun _ => 1) 0 64 hcheck hroot
  let T : Expr 3 := .var 0
  let A : Expr 3 := .var 1
  let B : Expr 3 := .var 2
  have hinput : Formula.Holds (.all [.le (r (1/2)) A,.le (.abs B) A,
      .le (containE A B) q0E,
      .any (CentralAxis.all.filterMap (fun k => match k with
        | .east => none
        | .own => some (.conj (.disj (.lt T (-.pi/4)) (.lt (.pi/4) T))
            (.le 0 (upperE k T A B xl xh yl yh)))
        | _ => some (.le 0 (upperE k T A B xl xh yl yh))))]) ![t,a,b] := by
    simpa [T,A,B,Formula.all,Formula.any,CentralAxis.all,Formula.Holds,Expr.denote,
      containE,phi,ReducedUpper] using
      And.intro hc.half_le (And.intro hc.u_le (And.intro hc.containment hs))
  have hresult := hcert hinput
  have hpair :
      (0 ≤ b → Formula.Holds (arcOutsideE (T+labelE A (.abs B)) am ap) ![t,a,b]) ∧
      (b ≤ 0 → Formula.Holds (arcOutsideE (T-labelE A (.abs B)) am ap) ![t,a,b]) := by
    simpa [T,A,B,Formula.all,Formula.Holds,Expr.denote] using hresult
  by_cases hb : b < 0
  · have hh := arcOutsideE_middle ![t,a,b] _ am ap (hpair.2 hb.le)
    simpa [T,A,B,Expr.denote,liftedMarker,signedLabel_of_neg hb] using hh
  · have hh := arcOutsideE_middle ![t,a,b] _ am ap (hpair.1 (le_of_not_gt hb))
    simpa [T,A,B,Expr.denote,liftedMarker,signedLabel_of_nonneg (le_of_not_gt hb)] using hh

/-- A1's sufficient rational empty arc, with no certificate hypothesis exposed. -/
theorem coneA1_marker {t a b : ℝ} (ht : |t| ≤ Real.pi) (hc : ContainedChart a |b|)
    (hs : ReducedUpper t a b c0 (1/2) 0 c0) :
    liftedMarker t a b ≤ -99/100 ∨ 61/50 ≤ liftedMarker t a b := by
  apply cone_from_check c0E (r (1/2)) 0 c0E (99/100) (61/50) coneA1_checked ht hc
  simpa [Expr.denote] using hs

/-- Each of the 36 A2 central boxes has its own proved finite check. -/
theorem coneA2_marker (i j : Fin 8) (hji : j ≤ i)
    {t a b : ℝ} (ht : |t| ≤ Real.pi) (hc : ContainedChart a |b|)
    (hs : ReducedUpper t a b (gridEdge i.val) (gridEdge (i.val+1))
      (gridEdge j.val) (gridEdge (j.val+1))) :
    liftedMarker t a b ≤ -27/50 ∨ 39/25 ≤ liftedMarker t a b := by
  apply cone_from_check (gridEdgeE i.val) (gridEdgeE (i.val+1))
    (gridEdgeE j.val) (gridEdgeE (j.val+1)) (27/50) (39/25) (coneA2_checked i j hji) ht hc
  simpa [Expr.denote] using hs

/-- With the chart phase in [-pi,pi], these near-east arcs have no hidden
2pi-shifted representative. This is a modular-angle statement, not just a
claim about the selected real lift. -/
lemma no_marker_lift_in_arc {t a b v am ap : ℝ}
    (ht : |t| ≤ Real.pi) (hc : ContainedChart a |b|)
    (ham : am < Real.pi/2) (hap : ap < Real.pi/2)
    (hout : liftedMarker t a b ≤ -am ∨ ap ≤ liftedMarker t a b)
    (hv : -am < v ∧ v < ap)
    (he : (v : Direction) = (liftedMarker t a b : Direction)) : False := by
  have hm := liftedMarker_bounds (t := t) hc.seven_admissible
  have htb := abs_le.mp ht
  obtain ⟨k,hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp he
  have hup : v-liftedMarker t a b < 2*Real.pi := by linarith [Real.pi_pos,hv.2,hm.1,htb.1]
  have hlo : -(2*Real.pi) < v-liftedMarker t a b := by linarith [Real.pi_pos,hv.1,hm.2,htb.2]
  rw [hk] at hup hlo
  have hp : 0 < 2*Real.pi := by positivity
  have hku : (k:ℝ) < 1 := (mul_lt_mul_left hp).mp (by simpa using hup)
  have hkl : (-1:ℝ) < (k:ℝ) := (mul_lt_mul_left hp).mp (by simpa using hlo)
  have hku' : k < 1 := by exact_mod_cast hku
  have hkl' : (-1:ℤ) < k := by exact_mod_cast hkl
  have hk0 : k=0 := by omega
  have hvEq : v=liftedMarker t a b := by simp [hk0] at hk; linarith
  rw [hvEq] at hv
  rcases hout with h | h <;> linarith [hv.1,hv.2]

end SquaresInCircles.Six.Normalization.Certificates
