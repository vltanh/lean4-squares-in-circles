module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowPositiveCoefficients
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLowSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLowSplit

/-!
# Eight squares: every far-low separated signed-mass alternative

The original B negative
part is compared with H, leaving the two fixed H/G negative coefficients.
Their angular slope is below .881 while the EH gain slope exceeds .8917.
Thus the whole EH interval reduces to its actual .1 endpoint. The two
possible total-angle ranges are paid by the already proved pure reserves.
The positive block is arbitrary, including the original DE2 singleton.
-/

section
/-!
## The positive D singleton in the negative-EH concentration

The coefficient interval contains both the fixed far-low H coefficient and the small-low H family.
The comparison `H_le_D` is non-strict at zero angle. It changes only a scalar minorant; the DE2
angle stays as it is.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEH.PositiveD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NegativeAPositiveTD.PositiveSlope

def reserve (k : ℝ) : ℝ := qCap*k^2-(k+2/5)^2*(1+k^2)
def reserveFirst (k : ℝ) : ℝ := -4*k^3-(12/5)*k^2+2*(qCap-29/25)*k-4/5
def reserveSecond (k : ℝ) : ℝ := -12*k^2-(24/5)*k+2*(qCap-29/25)

theorem reserve_derivative (k : ℝ) : HasDerivAt reserve (reserveFirst k) k := by
  have h2 : HasDerivAt (fun x : ℝ => x^2) (2*k) k := by simpa using hasDerivAt_pow 2 k
  have ha : HasDerivAt (fun x : ℝ => (x+2/5)^2) (2*(k+2/5)) k :=
    (((hasDerivAt_id' k).add_const (2/5)).fun_pow 2).congr_deriv (by norm_num)
  have h : HasDerivAt reserve
      (qCap*(2*k)-(2*(k+2/5)*(1+k^2)+(k+2/5)^2*(2*k))) k :=
    (h2.const_mul qCap).fun_sub (ha.fun_mul (h2.const_add 1))
  exact h.congr_deriv (by dsimp only [reserveFirst]; ring)

theorem reserveFirst_derivative (k : ℝ) : HasDerivAt reserveFirst (reserveSecond k) k := by
  have h2 : HasDerivAt (fun x : ℝ => x^2) (2*k) k := by simpa using hasDerivAt_pow 2 k
  have h3 : HasDerivAt (fun x : ℝ => x^3) (3*k^2) k := by simpa using hasDerivAt_pow 3 k
  have h : HasDerivAt reserveFirst
      (-4*(3*k^2)-(12/5)*(2*k)+2*(qCap-29/25)*1) k :=
    (((h3.const_mul (-4)).fun_sub (h2.const_mul (12/5))).fun_add
      ((hasDerivAt_id' k).const_mul (2*(qCap-29/25)))).sub_const (4/5)
  exact h.congr_deriv (by dsimp only [reserveSecond]; ring)

theorem reserve_positive {k : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5)) : 0<reserve k := by
  have hc : ConcaveOn ℝ (Icc (3/5:ℝ) (4/5)) reserve := by
    apply concave_of_deriv2 (fun k _ => reserve_derivative k)
      (fun k _ => reserveFirst_derivative k)
    intro k hk
    have hk2 : (3/5:ℝ)^2≤k^2 := by nlinarith [hk.1]
    dsimp [reserveSecond,qCap]
    nlinarith [hk.1]
  exact concave_gt_of_endpoints hc hk
    (by norm_num [reserve,qCap]) (by norm_num [reserve,qCap])

theorem H_zero_slope {k : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5)) : Ud k 1 0< -(2/5:ℝ) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hn := pairNorm_pos (t:=0) hk0 (by norm_num : (0:ℝ)<1) (by norm_num [frameCap])
  have hn2 := pairNorm_sq (t:=0) hk0 (by norm_num : (0:ℝ)<1) (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_zero,mul_zero,add_zero,one_pow] at hn2
  have hpoly := reserve_positive hk
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hcross : (k+2/5)*pairNorm k 1 0<R*k := by
    have hR : 0<R := by linarith [Secondary.radius_bounds.1]
    dsimp [reserve] at hpoly
    have hsquare : ((k+2/5)*pairNorm k 1 0)^2<(R*k)^2 := by
      rw [mul_pow,mul_pow,hn2,hR2]
      nlinarith only [hpoly]
    nlinarith [mul_pos hR hk0]
  have hdiv := (lt_div_iff₀ hn).2 hcross
  rw [mul_div_assoc] at hdiv
  simp only [Ud,mixedPDerivative,normD1,pairProduct,sub_zero,Real.sin_zero,Real.cos_zero,
    mul_one,sub_self]
  linarith

theorem H_linear_upper {k t : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (ht : t∈Icc 0 frameCap) : U R k 1 t≤-(2/5)*t := by
  have hk0 : 0<k := by linarith [hk.1]
  have hd (x : ℝ) (hx : x∈Icc 0 frameCap) :
      HasDerivAt (fun x => U R k 1 x+(2/5)*x) (Ud k 1 x+2/5) x := by
    have h3 : HasDerivAt (fun x : ℝ => (2/5)*x) (2/5) x := by
      simpa using (hasDerivAt_id x).const_mul (2/5:ℝ)
    exact (U_hasDerivAt hk0 (by norm_num) hx).fun_add h3
  have hm : AntitoneOn (fun x => U R k 1 x+(2/5)*x) (Icc 0 frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
    intro x hx
    have hh := Ud_antitone (q:=1) hk0 (by linarith [hk.2]) (by linarith [hk.1])
      (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) (Ioo_subset_Icc_self hx) hx.1.le
    linarith [H_zero_slope hk]
  have hh := hm (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht ht.1
  simp only [U_zero,mul_zero,add_zero] at hh
  linarith

theorem H_le_D {k t ε : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (ht : t∈Icc 0 frameCap) :
    U R k 1 t-ε*t≤ -(GlobalGA.Secondary.diagonal-1/2+ε)*t := by
  have hh := H_linear_upper hk ht
  have hc := mul_le_mul_of_nonneg_right
    (show GlobalGA.Secondary.diagonal-1/2≤2/5 by linarith [diagonal_bounds.2]) ht.1
  nlinarith

end SquaresInCircles.Eight.GlobalGA.NegativeEH.PositiveD
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.FarLowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope

def negativeQ (θ : ℝ) : Fin 2→ℝ := ![1,Explicit.l .far .low θ]

def energy (q s : ℝ) : ℝ := NegativeEH.G s+V R (121/200) q (frameCap-s)

lemma negativeQ_bounds {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) (j : Fin 2) :
    negativeQ θ j∈Icc (91/100:ℝ) 1 := by
  have hr := Explicit.far_low_ranges hθ
  fin_cases j
  · norm_num [negativeQ]
  · exact hr.2.1

lemma negative_representative {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) (j : Fin 4) :
    ∃r : Fin 2,V R (121/200) (negativeQ θ r) t≤Blocks.negative .far .low θ z t j := by
  fin_cases j
  · exact ⟨0,le_rfl⟩
  · exact ⟨1,le_rfl⟩
  · exact ⟨0,FarLowSlopes.H_le_B hθ hz ht⟩
  · exact ⟨0,le_rfl⟩

lemma remaining_angle {s : ℝ} (hs : s∈Icc (1/10:ℝ) (1/4)) :
    frameCap-s∈Icc (9/20:ℝ) (3/5) := by
  norm_num [frameCap]
  exact ⟨by linarith [hs.2],by linarith [hs.1]⟩

lemma energy_hasDerivAt {q s : ℝ} (hq : q∈Icc (91/100:ℝ) 1)
    (hs : s∈Icc (1/10:ℝ) (1/4)) :
    HasDerivAt (energy q) (NegativeEH.GD s-Vd R (121/200) q (frameCap-s)) s := by
  have hx := remaining_angle hs
  have ht : frameCap-s∈Icc 0 frameCap := by
    simp only [frameCap] at hx ⊢
    exact ⟨by linarith [hx.1],by linarith [hx.2,hs.1]⟩
  have hV := HasDerivAt.comp_const_sub frameCap s (V_hasDerivAt (R:=R)
    (by norm_num : (0:ℝ)<121/200) (show 0<q by linarith [hq.1]) ht)
  convert (NegativeEH.G_hasDerivAt s).fun_add hV using 1
  rfl

lemma energy_monotone {q : ℝ} (hq : q∈Icc (91/100:ℝ) 1) :
    MonotoneOn (energy q) (Icc (1/10:ℝ) (1/4)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (energy_hasDerivAt hq hs).continuousAt.continuousWithinAt)
    (fun s hs => energy_hasDerivAt hq (Ioo_subset_Icc_self hs))
  intro s hs
  have hsf := Ioo_subset_Icc_self hs
  have hG := NegativeEH.far_slope hsf
  have hV := FarLowSlopes.negative_slope hq (remaining_angle hsf)
  linarith

lemma negative_at_six {q : ℝ} (hq : q∈Icc (91/100:ℝ) 1) :
    (31581/70000:ℝ)≤V R (121/200) q (3/5) := by
  have hh := V_chord_lower (p:=(121/200:ℝ)) (q:=q)
    (by norm_num) (by linarith [hq.1]) (by linarith [hq.2])
    (show (3/5:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have e : (87/70:ℝ)*(121/200)*(3/5)=31581/70000 := by norm_num
  rw [e] at hh
  exact hh

lemma at_left_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 4) (j : Fin 2) :
    0<Explicit.baseline .far .low a z+NegativeEH.G (1/10)+
      Blocks.positive .far .low (a+z) z (frameCap-(a+z)) i+
        V R (121/200) (negativeQ (a+z) j) (3/5) := by
  have hsplit : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hP : frameCap-(a+z)∈Icc 0 frameCap := by
    norm_num [frameCap]
    exact ⟨by linarith [hθ.2],by linarith [hθ.1]⟩
  have hU := FarLowSlopes.positive_lower hθ hsplit hP i
  have hV := negative_at_six (negativeQ_bounds hθ j)
  by_cases he : a+z≤1/10
  · have hh := FarLowSplit.positive_H ⟨hθ.1,he⟩ ha hz
    have hHt := NegativeEH.PositiveD.H_linear_upper
      (k:=Explicit.k .far .low (a+z)) (by norm_num [Explicit.k])
      (show 1/10-(a+z)∈Icc 0 frameCap from
        ⟨by linarith,by norm_num [frameCap]; linarith [hθ.1]⟩)
    dsimp [frameCap,NegativeEH.epsilon] at *
    nlinarith [hθ.1]
  · have hh := FarLowSplit.negative_H ⟨by linarith,hθ.2⟩ ha hz
    have hHt := FarLowSlopes.H_upper (θ:=a+z) (z:=z)
      (show a+z-1/10∈Icc 0 frameCap from
        ⟨by linarith,by norm_num [frameCap]; linarith [hθ.2]⟩)
    change V R (Explicit.k .far .low (a+z)) 1 (a+z-1/10)≤(41/40)*(a+z-1/10) at hHt
    dsimp [frameCap] at hU
    nlinarith [hθ.2]

theorem original_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (1/10:ℝ) (1/4)) (i j : Fin 4) :
    0<Explicit.stressBase .far .low a z s+
      Blocks.positive .far .low (a+z) z (frameCap-(a+z)) i+
        Blocks.negative .far .low (a+z) z (frameCap-s) j := by
  have ht : frameCap-s∈Icc 0 frameCap := by
    norm_num [frameCap]
    exact ⟨by linarith [hs.2],by linarith [hs.1]⟩
  obtain ⟨r,hr⟩ := negative_representative hθ ⟨hz,by linarith⟩ ht j
  have hmono := energy_monotone (negativeQ_bounds hθ r)
    (show (1/10:ℝ)∈Icc (1/10) (1/4) by norm_num) hs hs.1
  have hleft := at_left_positive hθ ha hz i r
  have hcap : frameCap-(1/10:ℝ)=3/5 := by norm_num [frameCap]
  dsimp [energy] at hmono
  rw [hcap] at hmono
  dsimp [Explicit.stressBase,Explicit.gain]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.FarLowSeparated
end
end
end
