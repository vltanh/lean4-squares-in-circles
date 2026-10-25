module

public import SquaresInCircles.Eight.Owners.BT.CoreDE3Polynomial
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds

/-!
# Eight squares: the high-chart scalar of the return bound

On the high chart the radical of the return bound is removed by one positive square
(`return_root_comparison`). The resulting polynomial `square` of degree six is positive on the
whole interval `[0, 3/10]` by one quadratic bound on its centered coefficients (`square_positive`).
With the marker of the state, this gives the scalar return reserve (`return_marker_reserve`).
-/

section
/-!
## Exact radical transfer for all six DE2 tail scalars

The two positive quadratic envelopes are used only through square
completion.  Their explicit polynomial certificates imply the actual
two-circle inequalities for the full affine multiplier families.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open Polynomial FrameCircleArc

def tailEndpoint (last : Bool) (e m c z : ℝ) : ℝ :=
  Real.pi-z+(3/2)*kappa+2*c+e/2+m+
    (if last then kappa+e*Real.cos z else kappa*Real.cos z+e)-
    R*(tailNorm kappa c (if last then 0 else z)+tailNorm e c (if last then z else 0))

theorem radius_upper : R<1979/1000 := by
  have hh := FrameHighArc.radius_bound
  dsimp [FrameHighArc.radiusUpper] at hh
  linarith

theorem sin7_lower {z : ℝ} (hz : 0≤z) : Arithmetic.sin7 z≤Real.sin z := by
  simpa only [Arithmetic.sin7] using sin_lower_seven hz

/-- One reusable two-norm square completion.  X1 and X2 need no
independent positivity assumption: they dominate the actual squares. -/
theorem two_norm_envelope {N1 N2 X1 X2 P1 P2 L : ℝ}
    (hN1 : 0≤N1) (hN2 : 0≤N2) (hP1 : 0<P1) (hP2 : 0<P2)
    (hX1 : N1^2≤X1) (hX2 : N2^2≤X2)
    (hpoly : 0<2*P1*P2*L-(1979/1000)*
      (P2*(X1+P1^2)+P1*(X2+P2^2))) : R*(N1+N2)<L := by
  have h1 : 2*P1*N1≤X1+P1^2 := by nlinarith [sq_nonneg (N1-P1)]
  have h2 : 2*P2*N2≤X2+P2^2 := by nlinarith [sq_nonneg (N2-P2)]
  have hh1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0≤(1979/1000:ℝ)*P2)
  have hh2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0≤(1979/1000:ℝ)*P1)
  have hprod : 0<2*P1*P2 := by positivity
  have hmain : (1979/1000)*(N1+N2)<L := by
    apply (mul_lt_mul_iff_left₀ hprod).1
    nlinarith only [hpoly,hh1,hh2]
  have hr := mul_le_mul_of_nonneg_right radius_upper.le (add_nonneg hN1 hN2)
  exact hr.trans_lt hmain

theorem first_square_upper (i : Fin 3) (last : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    (tailNorm kappa (aeval z (TailPolynomial.weight i)) (if last then 0 else z))^2≤
      aeval z (TailPolynomial.x1 i last) := by
  have hw := (TailPolynomial.weights_bounds i hz).1
  have hk : 0<kappa := by norm_num [kappa]
  have hs := mul_le_mul_of_nonneg_left (sin7_lower hz.1)
    (show 0≤2*kappa*aeval z (TailPolynomial.weight i) by positivity)
  cases last
  · simp only [Bool.false_eq_true,↓reduceIte]
    rw [tailNorm_sq hk hw hz]
    simp only [TailPolynomial.x1,Bool.false_eq_true,↓reduceIte,map_sub,map_add,map_mul,
      map_pow,aeval_C,TailPolynomial.S7_eval]
    norm_num [kappa] at hs ⊢
    linarith
  · simp only [↓reduceIte]
    rw [tailNorm_sq hk hw (by norm_num [frameCap])]
    simp [TailPolynomial.x1,kappa]

theorem second_square_upper (i : Fin 3) (last : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    (tailNorm (TailPolynomial.e i:ℝ) (aeval z (TailPolynomial.weight i))
      (if last then z else 0))^2≤aeval z (TailPolynomial.x2 i last) := by
  have hw := (TailPolynomial.weights_bounds i hz).1
  have he := TailPolynomial.chart_positive i
  have hs := mul_le_mul_of_nonneg_left (sin7_lower hz.1)
    (show 0≤2*(TailPolynomial.e i:ℝ)*aeval z (TailPolynomial.weight i) by positivity)
  cases last
  · simp only [Bool.false_eq_true,↓reduceIte]
    rw [tailNorm_sq he hw (by norm_num [frameCap])]
    simp [TailPolynomial.x2]
  · simp only [↓reduceIte]
    rw [tailNorm_sq he hw hz]
    simp only [TailPolynomial.x2,↓reduceIte,map_sub,map_add,map_mul,
      map_pow,aeval_C,TailPolynomial.S7_eval,eq_ratCast]
    push_cast
    linarith

theorem endpoint_distance_lower (i : Fin 3) (last : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    aeval z (TailPolynomial.distance i last)≤
      Real.pi-z+(3/2)*kappa+2*aeval z (TailPolynomial.weight i)+(TailPolynomial.e i:ℝ)/2+
        (TailPolynomial.m i:ℝ)+
        (if last then kappa+(TailPolynomial.e i:ℝ)*Real.cos z
          else kappa*Real.cos z+(TailPolynomial.e i:ℝ))-pathThreshold := by
  have hc := cos_lower_six hz.1
  have hk := mul_le_mul_of_nonneg_left hc (show 0≤kappa by norm_num [kappa])
  have he := mul_le_mul_of_nonneg_left hc (TailPolynomial.chart_positive i).le
  have hp := Arithmetic.pi_hand_enclosure.1.le
  cases last <;>
    simp only [TailPolynomial.distance,TailPolynomial.cosinePart,
      Bool.false_eq_true,↓reduceIte,map_add,map_sub,map_mul,
      aeval_C,aeval_X,TailPolynomial.C6_eval,eq_ratCast] <;>
    push_cast <;> dsimp [kappa,pathThreshold] at hk ⊢ <;> linarith

/-- The actual two-circle endpoint scalar, for every intrinsic chart,
both error endpoints and the full affine TD multiplier family. -/
theorem affine_tail_endpoint (i : Fin 3) (last : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    pathThreshold<tailEndpoint last (TailPolynomial.e i:ℝ) (TailPolynomial.m i:ℝ)
      (aeval z (TailPolynomial.weight i)) z := by
  let c : ℝ := aeval z (TailPolynomial.weight i)
  let P1 : ℝ := aeval z (TailPolynomial.p1 i last)
  let P2 : ℝ := aeval z (TailPolynomial.p2 i last)
  let X1 : ℝ := aeval z (TailPolynomial.x1 i last)
  let X2 : ℝ := aeval z (TailPolynomial.x2 i last)
  let L : ℝ := aeval z (TailPolynomial.distance i last)
  have hP := TailPolynomial.envelopes_positive i last hz
  have hcert : 0<2*P1*P2*L-(1979/1000)*(P2*(X1+P1^2)+P1*(X2+P2^2)) := by
    have hh := TailPolynomial.positive i last hz
    simpa [TailPolynomial.certificate,P1,P2,X1,X2,L] using hh
  have hN := two_norm_envelope
    (N1 := tailNorm kappa c (if last then 0 else z))
    (N2 := tailNorm (TailPolynomial.e i:ℝ) c (if last then z else 0))
    (X1 := X1) (X2 := X2) (P1 := P1) (P2 := P2) (L := L)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by dsimp [P1]; linarith [hP.1]) (by dsimp [P2]; linarith [hP.2])
    (first_square_upper i last hz) (second_square_upper i last hz) hcert
  have hd := endpoint_distance_lower i last hz
  dsimp [L,c] at hN
  dsimp [tailEndpoint]
  linarith

end SquaresInCircles.Eight.GlobalBT
end
end
end

section
/-!
## The saturated aligned-prefix scalar for core E

Multiplication by the positive original cosine removes the secant
from the only variable radical.  Its envelope is a fixed positive
quartic and its certificate covers the complete saturated interval.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3

open Polynomial FrameCircleArc

theorem saturated_weight_bounds {t : ℝ} (ht : t∈Icc 0 frameCap) :
    m≤ m/Real.cos t ∧ m/Real.cos t<141/100 := by
  have tr := transport_trig ht
  have hc : 0<Real.cos t := by linarith [tr.1]
  constructor
  · apply (le_div_iff₀ hc).2
    dsimp [m]
    linarith [tr.2.1]
  · apply (div_lt_iff₀ hc).2
    dsimp [m]
    linarith [tr.1]

theorem endpointWeight_bounds {t : ℝ} (ht : t∈Icc 0 frameCap) :
    kappa≤endpointWeight t ∧ endpointWeight t<141/100 ∧
      endpointWeight t*Real.cos t≤ m ∧ endpointWeight t*Real.sin t≤7506931/1000000 := by
  have tr := transport_trig ht
  have hc : Real.cos t≠0 := ne_of_gt (by linarith [tr.1])
  by_cases hsmall : t≤1/5
  · rw [endpointWeight,ite_eq_left hsmall]
    refine ⟨le_rfl,by norm_num [kappa],?_,?_⟩
    · dsimp [kappa,m]
      linarith [tr.2.1]
    · dsimp [kappa]
      linarith [Real.sin_le_one t]
  · rw [endpointWeight,ite_eq_right hsmall]
    have hb := saturated_weight_bounds ht
    have hpos : 0≤ m/Real.cos t := le_trans (by norm_num [m]) hb.1
    have hs := mul_le_mul_of_nonneg_left (Real.sin_le_one t) hpos
    refine ⟨by dsimp [m,kappa] at hb ⊢; linarith [hb.1],hb.2,?_,?_⟩
    · rw [div_mul_cancel₀ m hc]
    · linarith [hb.2]

theorem fixed_first_norm : R*tailNorm kappa (3/5) 0<11369/5000 := by
  have hn := tailNorm_sq (by norm_num [kappa] : 0<kappa)
    (by norm_num : (0:ℝ)<3/5) (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
  have hs : (R*tailNorm kappa (3/5) 0)^2=Q0*(kappa^2+(3/5)^2) := by
    rw [mul_pow,R_sq,hn]
    simp
  have hv : Q0*(kappa^2+(3/5)^2)<(11369/5000:ℝ)^2 := by norm_num [Q0,kappa]
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (hs ▸ hv)

theorem one_norm_envelope {N X P L : ℝ} (hN : 0≤N) (hP : 0<P)
    (hX : N^2≤X) (hpoly : 0<2*P*L-(1979/1000)*(X+P^2)) : R*N<L := by
  have hh : 2*P*N≤X+P^2 := by nlinarith [sq_nonneg (N-P)]
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤1979/1000)
  have hmain : (1979/1000)*N<L := by
    apply (mul_lt_mul_iff_left₀ (show 0<2*P by positivity)).1
    nlinarith only [hpoly,hm]
  exact (mul_le_mul_of_nonneg_right radius_upper.le hN).trans_lt hmain

theorem scaled_norm_square {t : ℝ} (ht : t∈Icc 0 frameCap) :
    (Real.cos t*tailNorm (m/Real.cos t) (3/5) 0)^2=m^2+(9/25)*(Real.cos t)^2 := by
  have hc : 0<Real.cos t := by linarith [(transport_trig ht).1]
  have hn := tailNorm_sq (div_pos (show (0:ℝ) < m by norm_num [m]) hc)
    (by norm_num : (0:ℝ)<3/5) (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
  rw [mul_pow,hn]
  simp only [Real.sin_zero,mul_zero,sub_zero]
  field_simp [hc.ne']
  ring

theorem base_scaled_identity {t : ℝ} (ht : t∈Icc 0 frameCap) :
    Real.cos t*(base t (m/Real.cos t)-pathThreshold)=
      (Real.pi-t+(5/2)*kappa+6/5-R*tailNorm kappa (3/5) 0-pathThreshold+m/2)*Real.cos t+
        m*(1+(13/12)*Real.sin t)-R*(Real.cos t*tailNorm (m/Real.cos t) (3/5) 0) := by
  have hc : Real.cos t≠0 := ne_of_gt (by linarith [(transport_trig ht).1])
  dsimp [base]
  field_simp [hc]
  ring

/-- The concrete saturated base, including its lower endpoint. -/
theorem saturated_base {t : ℝ} (ht : t∈Icc (1/5:ℝ) frameCap) :
    pathThreshold<base t (m/Real.cos t) := by
  have hdom : t∈Icc 0 frameCap := ⟨by linarith [ht.1],ht.2⟩
  have hc : 0<Real.cos t := by linarith [(transport_trig hdom).1]
  let N := Real.cos t*tailNorm (m/Real.cos t) (3/5) 0
  let P : ℝ := aeval t BasePolynomial.P
  let X : ℝ := aeval t BasePolynomial.energy
  let L : ℝ := aeval t BasePolynomial.L
  have hN : 0≤N := mul_nonneg hc.le (Real.sqrt_nonneg _)
  have hP : 0<P := by dsimp [P]; linarith [BasePolynomial.envelope_positive hdom]
  have hU : Real.cos t≤aeval t BasePolynomial.U := by
    have h := cos_upper_four hdom.1
    simp only [BasePolynomial.U,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
      eq_ratCast]
    push_cast
    linarith
  have hUpos : 0≤aeval t BasePolynomial.U := hc.le.trans hU
  have hsq := pow_le_pow_left₀ hc.le hU 2
  have hX : N^2≤X := by
    dsimp [N,X]
    rw [scaled_norm_square hdom]
    simp only [BasePolynomial.energy,map_add,map_mul,map_pow,aeval_C]
    norm_num [m]
    nlinarith only [hsq]
  have hpoly : 0<2*P*L-(1979/1000)*(X+P^2) := by
    simpa [BasePolynomial.H,P,L,X] using BasePolynomial.positive ht
  have hnorm := one_norm_envelope hN hP hX hpoly
  have hcoef := BasePolynomial.coefficient_positive hdom
  have hcos := mul_le_mul_of_nonneg_left (cos_lower_six hdom.1) hcoef.le
  have hpi : aeval t BasePolynomial.coefficient≤
      Real.pi-t+(5/2)*kappa+6/5-R*tailNorm kappa (3/5) 0-pathThreshold+m/2 := by
    have hf := fixed_first_norm
    simp only [kappa] at hf
    norm_num [BasePolynomial.coefficient,kappa,pathThreshold,m,-tailNorm_comm]
    linarith [Arithmetic.pi_hand_enclosure.1,hf]
  have hactual := mul_le_mul_of_nonneg_right hpi hc.le
  have hsin := mul_le_mul_of_nonneg_left (sin7_lower hdom.1)
    (show 0 ≤ m*(13/12) by norm_num [m])
  have hL : L≤
      (Real.pi-t+(5/2)*kappa+6/5-R*tailNorm kappa (3/5) 0-pathThreshold+m/2)*Real.cos t+
        m*(1+(13/12)*Real.sin t) := by
    dsimp [L]
    simp only [BasePolynomial.L,map_add,map_mul,aeval_C,map_one,
      TailPolynomial.C6_eval,TailPolynomial.S7_eval]
    norm_num [m,-tailNorm_comm] at hsin hactual ⊢
    linarith only [hcos,hactual,hsin]
  have hpos : 0<Real.cos t*(base t (m/Real.cos t)-pathThreshold) := by
    rw [base_scaled_identity hdom]
    dsimp [N,L] at hnorm
    dsimp [L] at hL
    linarith only [hnorm,hL]
  have hh := (mul_pos_iff_of_pos_left hc).1 hpos
  linarith

end SquaresInCircles.Eight.GlobalBT.CoreDE3
end
end
end

section
/-!
## Both core-E tails for the complete small-DE interval

The variable prefix is bounded by its explicit two-norm polynomial.
The small DE dependence is concave with its smaller endpoint at zero.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3

open Polynomial FrameCircleArc

theorem prefix_strict {p : ℝ} (hp : p∈Icc 0 frameCap) : pathThreshold<«prefix» p := by
  have hk : 0<kappa := by norm_num [kappa]
  have hc := weight_pos hp
  have hnorm1 := tailNorm_sq hk hc hp
  have hnorm2 := tailNorm_sq hk hc (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
  have hs := mul_le_mul_of_nonneg_left (sin7_lower hp.1)
    (show 0≤2*kappa*weight p by positivity)
  have hX1 : (tailNorm kappa (weight p) p)^2≤aeval p PrefixPolynomial.X1 := by
    rw [hnorm1]
    simp only [PrefixPolynomial.X1,map_sub,map_add,map_mul,map_pow,aeval_C,
      PrefixPolynomial.c_eval,TailPolynomial.S7_eval]
    norm_num [kappa] at hs ⊢
    linarith
  have hX2 : (tailNorm kappa (weight p) 0)^2≤aeval p PrefixPolynomial.X2 := by
    rw [hnorm2]
    simp [PrefixPolynomial.X2,kappa]
  have hP := PrefixPolynomial.envelopes_positive hp
  have hpoly : 0<2*aeval p PrefixPolynomial.P1*aeval p PrefixPolynomial.P2*
      aeval p PrefixPolynomial.L-(1979/1000)*
        (aeval p PrefixPolynomial.P2*(aeval p PrefixPolynomial.X1+(aeval p PrefixPolynomial.P1)^2)+
          aeval p PrefixPolynomial.P1*(aeval p PrefixPolynomial.X2+(aeval p PrefixPolynomial.P2)^2)) := by
    simpa [PrefixPolynomial.H] using PrefixPolynomial.positive hp
  have hn := two_norm_envelope (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (show 0<aeval p PrefixPolynomial.P1 by linarith [hP.1])
    (show 0<aeval p PrefixPolynomial.P2 by linarith [hP.2]) hX1 hX2 hpoly
  have hcos := mul_le_mul_of_nonneg_left (cos_lower_six hp.1) hk.le
  have hL : aeval p PrefixPolynomial.L≤
      Real.pi-p+3*kappa+2*weight p+kappa*Real.cos p-pathThreshold := by
    simp only [PrefixPolynomial.L,map_add,map_sub,map_mul,aeval_C,aeval_X,
      PrefixPolynomial.c_eval,TailPolynomial.C6_eval]
    norm_num [kappa,pathThreshold] at hcos ⊢
    linarith [Arithmetic.pi_hand_enclosure.1]
  have hn' : R*(tailNorm kappa (weight p) p+tailNorm kappa (weight p) 0)<
      aeval p PrefixPolynomial.L := hn
  dsimp only [«prefix»]
  linarith

def smallDE (t : ℝ) : ℝ := -t+(kappa/2)*Real.cos t+kappa*(13/12)*Real.sin t
def smallDED (t : ℝ) : ℝ := -1-(kappa/2)*Real.sin t+kappa*(13/12)*Real.cos t
def smallDEDD (t : ℝ) : ℝ := -(kappa/2)*Real.cos t-kappa*(13/12)*Real.sin t

theorem smallDE_deriv (t : ℝ) : HasDerivAt smallDE (smallDED t) t := by
  have h := (((hasDerivAt_id t).neg).add ((Real.hasDerivAt_cos t).const_mul (kappa/2))).add
    ((Real.hasDerivAt_sin t).const_mul (kappa*(13/12)))
  exact h.congr_deriv (by simp only [smallDED]; ring)

theorem smallDED_deriv (t : ℝ) : HasDerivAt smallDED (smallDEDD t) t := by
  have h := (((Real.hasDerivAt_sin t).const_mul (-(kappa/2))).const_add (-1)).add
    ((Real.hasDerivAt_cos t).const_mul (kappa*(13/12)))
  convert h using 1
  · funext x; simp only [smallDED,Pi.add_apply]; ring
  · simp only [smallDEDD]; ring

theorem smallDE_concave : ConcaveOn ℝ (Icc 0 (1/5:ℝ)) smallDE := by
  apply concave_of_deriv2 (fun t _ => smallDE_deriv t) (fun t _ => smallDED_deriv t)
  intro t ht
  have hd : t∈Icc 0 frameCap := ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  have tr := transport_trig hd
  dsimp [smallDEDD,kappa]
  linarith [tr.1,tr.2.2.1]

theorem smallDE_endpoint : smallDE 0<smallDE (1/5) := by
  have hs := sin_lower_seven (by norm_num : (0:ℝ)≤1/5)
  have hc := cos_lower_six (by norm_num : (0:ℝ)≤1/5)
  norm_num at hs hc
  norm_num [smallDE,kappa]
  linarith

theorem smallDE_lower {t : ℝ} (ht : t∈Icc 0 (1/5:ℝ)) : smallDE 0≤ smallDE t := by
  have hh := smallDE_concave.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 (1/5:ℝ) by norm_num)
    (show (1/5:ℝ)∈Icc 0 (1/5:ℝ) by norm_num) ht
  rw [min_eq_left smallDE_endpoint.le] at hh
  exact hh

theorem last_first_difference (p t : ℝ) :
    last p t kappa-first p t kappa=(kappa-weight p)*(1-Real.cos p) := by
  dsimp [last,first]
  ring

theorem small_endpoints {p t : ℝ} (hp : p∈Icc 0 frameCap)
    (ht : t∈Icc 0 (1/5:ℝ)) :
    pathThreshold<first p t kappa ∧ pathThreshold<last p t kappa := by
  have hg := smallDE_lower ht
  have hfirst : «prefix» p≤first p t kappa := by
    simp only [smallDE,Real.sin_zero,Real.cos_zero,mul_zero,mul_one,neg_zero,add_zero] at hg
    dsimp [«prefix»,first]
    linarith only [hg]
  have hlast : first p t kappa≤last p t kappa := by
    have hm := mul_nonneg (sub_nonneg.mpr (weight_bounds hp).2.2)
      (sub_nonneg.mpr (Real.cos_le_one p))
    rw [← last_first_difference p t] at hm
    linarith
  have hstrict := (prefix_strict hp).trans_le hfirst
  exact ⟨hstrict,hstrict.trans_le hlast⟩

end SquaresInCircles.Eight.GlobalBT.CoreDE3
end
end
end

section
/-!
## Complete positive-BT1 scalar gain

One strictly concave rational polynomial controls the full original
error interval.  Its two endpoint values are fixed positive rational
numbers.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.OnePositive

open Polynomial FramePair FrameCircleArc

def gain (x : ℝ) : ℝ :=
  x+kappa*((c0-1/2)*(1-Real.cos x)-(R-Real.cos x)*Real.sin x)

namespace Certificate

def P : ℚ[X] := C (1-(49/50)*(979/1000))+C ((49/50)*(399/2000))*X-
  C ((49/50)*(1/2-979/6000))*X^2-C ((49/50)*(399/24000))*X^3+
    C ((49/50)*(1/12-979/120000))*X^4-C ((49/50)/240)*X^6
def second : ℚ[X] :=
  C (-2*(49/50)*(1/2-979/6000))-C (6*(49/50)*(399/24000))*X+
    C (12*(49/50)*(1/12-979/120000))*X^2-C (30*(49/50)/240)*X^4

theorem second_identity : P.derivative.derivative=second := by
  ext n
  simp only [coeff_derivative]
  rcases n with _|_|_|_|_|n <;>
    simp only [P,second,coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C] <;>
    norm_num

theorem endpoints : 0<P.eval 0 ∧ 0<P.eval (7/10) := by
  constructor <;> norm_num [P]

theorem second_negative {x : ℝ} (hx : x∈Icc 0 frameCap) :
    aeval x P.derivative.derivative<0 := by
  rw [second_identity]
  have h2 := pow_le_pow_left₀ hx.1 hx.2 2
  have h4 := pow_nonneg hx.1 4
  dsimp [frameCap] at hx h2
  norm_num [second]
  nlinarith only [hx.1,h2,h4]

theorem concave : ConcaveOn ℝ (Icc 0 frameCap) (fun x : ℝ => aeval x P) :=
  concave_of_deriv2 (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt P x)
    (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt P.derivative x)
    (fun _ hx => (second_negative hx).le)

theorem positive {x : ℝ} (hx : x∈Icc 0 frameCap) : 0<aeval x P := by
  apply concave_gt_of_endpoints concave hx
  · norm_num [P]
  · have he : aeval (frameCap:ℝ) P=((P.eval (7/10):ℚ):ℝ) := by
      rw [show (frameCap:ℝ)=((7/10:ℚ):ℝ) by norm_num [frameCap]]
      exact TailPolynomial.rational_aeval _ _
    rw [he]
    exact_mod_cast endpoints.2

theorem identity_eval (x : ℝ) : x*aeval x P=
    x+kappa*((399/1000)*(x^2/2-x^4/24)-
      (979/1000+x^2/2)*(x-x^3/6+x^5/120)) := by
  simp [P,kappa]
  ring

end Certificate

theorem gain_lower {x : ℝ} (hx : x∈Icc 0 frameCap) : x*aeval x Certificate.P≤gain x := by
  have hs := sin_upper_five hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hu := cos_upper_four hx.1
  have tr := transport_trig hx
  have hR : R-Real.cos x≤979/1000+x^2/2 := by linarith [radius_upper]
  have hnegative := mul_le_mul hR hs tr.2.2.1
    (show 0≤(979/1000:ℝ)+x^2/2 by positivity)
  have hdiag : (399/1000:ℝ)≤c0-1/2 := by linarith [FrameHighArc.diagonal_bounds.1]
  have hpositive := mul_le_mul_of_nonneg_right hdiag
    (sub_nonneg.mpr (Real.cos_le_one x))
  have hdrop : x^2/2-x^4/24≤1-Real.cos x := by linarith
  have hdrop' := mul_le_mul_of_nonneg_left hdrop (by norm_num : (0:ℝ)≤399/1000)
  rw [Certificate.identity_eval]
  dsimp [gain,kappa]
  nlinarith only [hnegative,hpositive,hdrop']

theorem gain_nonnegative {x : ℝ} (hx : x∈Icc 0 frameCap) : 0≤gain x :=
  (mul_nonneg hx.1 (Certificate.positive hx).le).trans (gain_lower hx)

end SquaresInCircles.Eight.GlobalBT.OnePositive
end
end
end

section
/-!
## Strengthened TD weights of the BT0/1 tail

The DE2 tail scalars stay strict when the affine TD weight is replaced by its maximum with `3/5`,
`strengthenedWeight` (`strengthened_tail_endpoint`). On the lower interval the weight is the
constant `3/5` and the family is concave (`fixed_endpoint_concave`), joined exactly to the affine
family. These are the weights the negative BT1 prefix comparison needs.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open Polynomial FrameCircleArc

def strengthenedWeight (i : Fin 3) (z : ℝ) : ℝ := max (3/5) (aeval z (TailPolynomial.weight i))
def zeroTargetNormUpper : Fin 3→ℝ := ![111931/100000,99761/100000,87727/100000]

theorem strengthened_bounds (i : Fin 3) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    3/5≤ strengthenedWeight i z ∧ strengthenedWeight i z≤kappa ∧
      strengthenedWeight i z≤(TailPolynomial.e i:ℝ) := by
  have hw := TailPolynomial.weights_bounds i hz
  refine ⟨le_max_left _ _,max_le (by norm_num [kappa]) hw.2.1,?_⟩
  apply max_le _ hw.2.2
  fin_cases i <;> norm_num [TailPolynomial.e]

theorem first_zero_norm : tailNorm kappa (3/5) 0<(114909/100000:ℝ) := by
  rw [tailNorm,Real.sin_zero,Real.sqrt_lt' (by norm_num)]
  norm_num [kappa]

theorem target_zero_norm (i : Fin 3) :
    tailNorm (TailPolynomial.e i:ℝ) (3/5) 0<zeroTargetNormUpper i := by
  have hs := tailNorm_sq (TailPolynomial.chart_positive i) (c := (3/5:ℝ))
    (by norm_num) (z := 0) (by norm_num [frameCap])
  have hn : 0≤tailNorm (TailPolynomial.e i:ℝ) (3/5) 0 := Real.sqrt_nonneg _
  fin_cases i <;> norm_num [TailPolynomial.e,zeroTargetNormUpper] at hs ⊢ <;> nlinarith

theorem zero_tail_endpoint (i : Fin 3) (last : Bool) :
    pathThreshold<tailEndpoint last (TailPolynomial.e i:ℝ) (TailPolynomial.m i:ℝ) (3/5) 0 := by
  have hsum := add_lt_add first_zero_norm (target_zero_norm i)
  have hupper : 0<(114909/100000:ℝ)+zeroTargetNormUpper i := by
    fin_cases i <;> norm_num [zeroTargetNormUpper]
  have hp := (mul_lt_mul_of_pos_left hsum R_pos).trans
    (mul_lt_mul_of_pos_right radius_upper hupper)
  have hpi := Arithmetic.pi_hand_enclosure.1
  cases last <;> simp only [tailEndpoint,Bool.false_eq_true,↓reduceIte,
    sub_zero,Real.cos_zero,mul_one] <;>
    fin_cases i <;> norm_num [TailPolynomial.e,TailPolynomial.m,zeroTargetNormUpper,
      pathThreshold,kappa] at hp ⊢ <;> linarith

theorem fixed_endpoint_concave (last : Bool) {e m c : ℝ} (he : 0<e) (hc : 0<c) :
    ConcaveOn ℝ (Icc 0 frameCap) (tailEndpoint last e m c) := by
  cases last with
  | false =>
      have h := (affine_concave (-1)
        (Real.pi+(3/2)*kappa+2*c+e/2+m+e-R*tailNorm e c 0) 0 frameCap).add
        (normCos_concave (a := kappa) (by norm_num [kappa]) hc)
      convert h using 1
      funext z
      dsimp [tailEndpoint,normCos]
      ring
  | true =>
      have h := (affine_concave (-1)
        (Real.pi+(3/2)*kappa+2*c+e/2+m+kappa-R*tailNorm kappa c 0) 0 frameCap).add
        (normCos_concave he hc)
      convert h using 1
      funext z
      dsimp [tailEndpoint,normCos]
      ring

theorem strengthened_tail_endpoint (i : Fin 3) (last : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    pathThreshold<tailEndpoint last (TailPolynomial.e i:ℝ) (TailPolynomial.m i:ℝ)
      (strengthenedWeight i z) z := by
  by_cases hbefore : z≤(TailPolynomial.join i:ℝ)
  · have hw := TailPolynomial.constant_above_before_join i hbefore
    rw [strengthenedWeight,max_eq_left hw]
    have hjoin := affine_tail_endpoint i last (TailPolynomial.join_domain i)
    rw [TailPolynomial.join_weight] at hjoin
    have hconc := (fixed_endpoint_concave last (m := (TailPolynomial.m i:ℝ))
      (TailPolynomial.chart_positive i) (by norm_num : (0:ℝ)<3/5)).subset
      (Icc_subset_Icc le_rfl (TailPolynomial.join_domain i).2) (convex_Icc _ _)
    exact concave_gt_of_endpoints hconc ⟨hz.1,hbefore⟩ (zero_tail_endpoint i last) hjoin
  · have hw := TailPolynomial.affine_above_after_join i (le_of_not_ge hbefore)
    rw [strengthenedWeight,max_eq_right hw]
    exact affine_tail_endpoint i last hz

end SquaresInCircles.Eight.GlobalBT
end
end
end

section
/-!
## Concentrating the three DE2 tail errors

Both owners of TD reduce to the same two endpoint scalars. The TD error is concentrated first by a
cosine comparison (`cosine_concentration`), and the remaining split by the concavity of the norm
(`tailSplit_concave`); the strengthened weight stays fixed in both comparisons. So the DE2 tail
exceeds `pathThreshold` (`strengthened_de2Tail`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open Polynomial FrameCircleArc

def tailSplit (e m c r t : ℝ) : ℝ :=
  Real.pi-(r+t)+(3/2)*kappa+2*c+e/2+m+normCos kappa c r+normCos e c t
def de2Tail (second : Bool) (e m c r s t : ℝ) : ℝ :=
  Real.pi-(r+s+t)+(3/2)*kappa+c+e/2+m+
    kappa*Real.cos r+c*Real.cos s+e*Real.cos t-
    R*(if second then tailNorm kappa c (r+s)+tailNorm e c t
      else tailNorm kappa c r+tailNorm e c (s+t))

theorem cosine_concentration {c e s t : ℝ} (hc : 0≤c) (hce : c≤e)
    (hs : s∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap) :
    c+e*Real.cos (s+t)≤c*Real.cos s+e*Real.cos t := by
  have trs := transport_trig hs
  have trt := transport_trig ht
  have hcs : 0≤Real.cos s := by linarith [trs.1]
  have hct : 0≤Real.cos t := by linarith [trt.1]
  have hss := trs.2.2.1
  have hst := trt.2.2.1
  have hsumS := one_le_abs_cos_add_abs_sin s
  have hsumT := one_le_abs_cos_add_abs_sin t
  rw [abs_of_nonneg hcs,abs_of_nonneg hss] at hsumS
  rw [abs_of_nonneg hct,abs_of_nonneg hst] at hsumT
  have hdS : 0≤1-Real.cos s := sub_nonneg.mpr (Real.cos_le_one s)
  have hdT : 0≤1-Real.cos t := sub_nonneg.mpr (Real.cos_le_one t)
  have hprod := mul_le_mul (show 1-Real.cos s≤Real.sin s by linarith)
    (show 1-Real.cos t≤Real.sin t by linarith) hdT hss
  have hbase : 0≤Real.cos s+Real.cos t-1-Real.cos (s+t) := by
    rw [Real.cos_add]
    nlinarith only [hprod]
  have hmono : 0≤Real.cos t-Real.cos (s+t) := by
    rw [Real.cos_add]
    nlinarith only [mul_nonneg hct hdS,mul_nonneg hss hst]
  have hfirst := mul_nonneg hc hbase
  have hsecond := mul_nonneg (sub_nonneg.mpr hce) hmono
  nlinarith only [hfirst,hsecond]

theorem tailSplit_concave {e m c z : ℝ} (he : 0<e) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 z) (fun r => tailSplit e m c r (z-r)) := by
  have hfirst := (normCos_concave (a := kappa) (by norm_num [kappa]) hc).subset (Icc_subset_Icc le_rfl hz.2) (convex_Icc 0 z)
  have hsecond := concave_affine_argument (normCos_concave he hc)
    (a := -1) (b := z) (l := 0) (u := z)
    (fun r hr => ⟨by linarith [hr.2],by linarith [hz.2,hr.1]⟩)
  have hconstant := affine_concave 0
    (Real.pi-z+(3/2)*kappa+2*c+e/2+m) 0 z
  convert (hconstant.add hfirst).add hsecond using 1
  funext r
  dsimp [tailSplit]
  rw [show (-1:ℝ)*r+z=z-r by ring]
  ring

theorem tailSplit_zero (e m c z : ℝ) : tailSplit e m c 0 z=tailEndpoint true e m c z := by
  simp [tailSplit,tailEndpoint,normCos]
  ring

theorem tailSplit_last (e m c z : ℝ) : tailSplit e m c z 0=tailEndpoint false e m c z := by
  simp [tailSplit,tailEndpoint,normCos]
  ring

theorem strengthened_tailSplit (i : Fin 3) {r t : ℝ} (hr : 0≤r) (ht : 0≤t)
    (hcap : r+t≤frameCap) :
    pathThreshold<tailSplit (TailPolynomial.e i:ℝ) (TailPolynomial.m i:ℝ)
      (strengthenedWeight i (r+t)) r t := by
  let z : ℝ := r+t
  have hz : z∈Icc 0 frameCap := ⟨add_nonneg hr ht,hcap⟩
  let c := strengthenedWeight i z
  have hc : 0<c := by have hh := (strengthened_bounds i hz).1; dsimp [c]; linarith
  have hconc := tailSplit_concave (m := (TailPolynomial.m i:ℝ))
    (TailPolynomial.chart_positive i) hc hz
  have hleft := strengthened_tail_endpoint i true hz
  have hright := strengthened_tail_endpoint i false hz
  rw [← tailSplit_zero] at hleft
  rw [← tailSplit_last] at hright
  have hh := concave_gt_of_endpoints hconc
    (show r∈Icc 0 z from ⟨hr,by dsimp [z]; linarith⟩)
    (by simpa [c] using hleft) (by simpa [c] using hright)
  simpa [c,z] using hh

/-- The DE2 tail exceeds `pathThreshold` for either owner of TD and all nonnegative negative-error
parts `r`, `s`, `t` with `r + s + t ≤ frameCap`. -/
theorem strengthened_de2Tail (i : Fin 3) (second : Bool) {r s t : ℝ}
    (hr : 0≤r) (hs : 0≤ s) (ht : 0≤t) (hcap : r+s+t≤frameCap) :
    pathThreshold<de2Tail second (TailPolynomial.e i:ℝ) (TailPolynomial.m i:ℝ)
      (strengthenedWeight i (r+s+t)) r s t := by
  let c := strengthenedWeight i (r+s+t)
  have htotal : r+s+t∈Icc 0 frameCap := ⟨by positivity,hcap⟩
  have hweights := strengthened_bounds i htotal
  have hc : 0≤c := by dsimp [c]; linarith [hweights.1]
  have hrange : r∈Icc 0 frameCap := ⟨hr,by linarith⟩
  have hsrange : s∈Icc 0 frameCap := ⟨hs,by linarith⟩
  have htrange : t∈Icc 0 frameCap := ⟨ht,by linarith⟩
  cases second with
  | false =>
      have hcos := cosine_concentration hc hweights.2.2 hsrange htrange
      have hsplit := strengthened_tailSplit i hr (add_nonneg hs ht)
        (by linarith : r+(s+t)≤frameCap)
      have hsame : r+(s+t)=r+s+t := by ring
      rw [hsame] at hsplit
      dsimp [tailSplit,normCos,de2Tail]
      dsimp [tailSplit,normCos] at hsplit
      dsimp [c] at hcos
      linarith
  | true =>
      have hcos := cosine_concentration hc hweights.2.1 hsrange hrange
      rw [add_comm s r] at hcos
      have hsplit := strengthened_tailSplit i (add_nonneg hr hs) ht hcap
      dsimp [tailSplit,normCos] at hsplit
      dsimp [de2Tail]
      dsimp [c] at hcos
      linarith

end SquaresInCircles.Eight.GlobalBT
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open Polynomial FramePair FrameCircleArc FrameMidArc
open GlobalOuterAnchor GlobalZeroSign GlobalQuarterSign

def returnCut : ℝ := 29843/50000
def returnDistance (z : ℝ) : ℝ :=
  238500487341/250000000000-(249557/500000)*z-(9/200)*z^2-(3/200)*z^3

namespace ReturnPolynomial

def distance : ℚ[X] := C (238500487341/250000000000)-C (249557/500000)*X-
  C (9/200)*X^2-C (3/200)*X^3
def square : ℚ[X] := distance^2-C ((8898/15625)^2)*
  (C (9789/2500)-(C (29843/50000+1/2)+X)^2)
def centered : ℚ[X] := DirectedPowerBounds.shift (12157/50000) square

/-- The seven coefficients of `centered`, by evaluation. -/
private lemma r28_centered_eq : centered=
    C (630136309413119704774301519041/625000000000000000000000000000000)+
    C (553216145273364169069039/6250000000000000000000000000)*X+
    C (25283894063212796284427/50000000000000000000000)*X^2+
    C (8423736731825037/250000000000000000)*X^3+
    C (376782701523/20000000000000)*X^4+C (1678239/1000000000)*X^5+C (9/40000)*X^6 := by
  apply Polynomial.funext
  intro r
  simp only [centered,DirectedPowerBounds.shift,square,distance,eval_comp,eval_sub,eval_add,
    eval_mul,eval_pow,eval_C,eval_X]
  ring

private lemma r28_coeffs :
    centered.coeff 0=630136309413119704774301519041/625000000000000000000000000000000 ∧
    centered.coeff 1=553216145273364169069039/6250000000000000000000000000 ∧
    centered.coeff 2=25283894063212796284427/50000000000000000000000 ∧
    centered.coeff 3=8423736731825037/250000000000000000 ∧
    centered.coeff 4=376782701523/20000000000000 ∧
    centered.coeff 5=1678239/1000000000 ∧ centered.coeff 6=9/40000 := by
  rw [r28_centered_eq]
  simp only [coeff_add,coeff_C,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num

private lemma r28_c0 : centered.coeff 0=
    630136309413119704774301519041/625000000000000000000000000000000 := r28_coeffs.1
private lemma r28_c1 : centered.coeff 1=553216145273364169069039/6250000000000000000000000000 :=
  r28_coeffs.2.1
private lemma r28_c2 : centered.coeff 2=25283894063212796284427/50000000000000000000000 :=
  r28_coeffs.2.2.1
private lemma r28_c3 : centered.coeff 3=8423736731825037/250000000000000000 := r28_coeffs.2.2.2.1
private lemma r28_c4 : centered.coeff 4=376782701523/20000000000000 := r28_coeffs.2.2.2.2.1
private lemma r28_c5 : centered.coeff 5=1678239/1000000000 := r28_coeffs.2.2.2.2.2.1
private lemma r28_c6 : centered.coeff 6=9/40000 := r28_coeffs.2.2.2.2.2.2

theorem centered_identity : centered=C (centered.coeff 0)+C (centered.coeff 1)*X+
    C (centered.coeff 2)*X^2+PowerTailBounds.tail centered 3 4 := by
  simp only [PowerTailBounds.tail,Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,
    Fin.val_succ,Nat.reduceAdd,zero_add,r28_c0,r28_c1,r28_c2,r28_c3,r28_c4,r28_c5,r28_c6]
  conv_lhs => rw [r28_centered_eq]
  ring

theorem centered_reserves : (1/1000:ℚ)<centered.coeff 0 ∧
    |centered.coeff 1|<1/10000 ∧
    0≤centered.coeff 2-PowerTailBounds.norm centered 3 4 (1/4) := by
  simp only [PowerTailBounds.norm,Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,
    Fin.val_succ,Nat.reduceAdd,zero_add,r28_c0,r28_c1,r28_c2,r28_c3,r28_c4,r28_c5,r28_c6]
  norm_num [abs_of_pos]

theorem square_positive {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ)) : 0<aeval z square := by
  have hx : |z-(12157/50000:ℝ)|≤((1/4:ℚ):ℝ) := by
    rw [abs_le]; push_cast; constructor <;> linarith [hz.1,hz.2]
  have hl := PowerTailBounds.quadratic_lower centered_identity
    (by norm_num : (0:ℚ)≤1/4) hx
  have h0 : (1/1000:ℝ)<(centered.coeff 0:ℝ) := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr centered_reserves.1
    push_cast at h; exact h
  have h1 : |(centered.coeff 1:ℝ)|≤(1/10000:ℝ) := by
    have h := (Rat.cast_le (K:=ℝ)).mpr centered_reserves.2.1.le
    push_cast at h; exact h
  have h2 : 0≤(centered.coeff 2:ℝ)-(PowerTailBounds.norm centered 3 4 (1/4):ℝ) := by
    have h := (Rat.cast_le (K:=ℝ)).mpr centered_reserves.2.2
    push_cast at h; exact h
  have hx' : |z-(12157/50000:ℝ)|≤1/4 := by push_cast at hx; exact hx
  have hprod := mul_le_mul h1 hx' (abs_nonneg (z-(12157/50000:ℝ)))
    (by norm_num : (0:ℝ)≤1/10000)
  have hlin : -(1/40000:ℝ)≤(centered.coeff 1:ℝ)*(z-12157/50000) := by
    rw [← abs_mul] at hprod
    have hh := (abs_le.mp hprod).1
    linarith
  have hquad := mul_nonneg h2 (sq_nonneg (z-(12157/50000:ℝ)))
  have he : aeval (z-12157/50000) centered=aeval z square := by
    simp only [centered,DirectedPowerBounds.shift_eval]
    congr 1
    push_cast
    ring_nf
  rw [he] at hl
  linarith

theorem distance_eval (z : ℝ) : aeval z distance=returnDistance z := by
  simp [distance,returnDistance]

theorem square_eval (z : ℝ) : aeval z square=
    (returnDistance z)^2-FrameHighArc.u^2*(Q0-(returnCut+z+1/2)^2) := by
  simp only [square,map_sub,map_mul,map_pow,aeval_C,distance_eval]
  norm_num [FrameHighArc.u,Q0,returnCut]
  ring

end ReturnPolynomial

theorem return_distance_positive {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ)) :
    0<returnDistance z := by
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  have h3 := pow_le_pow_left₀ hz.1 hz.2 3
  dsimp [returnDistance]
  norm_num at h2 h3
  nlinarith [hz.2]

theorem return_root_comparison {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ))
    (hb : returnCut+z∈Icc 0 c0) :
    FrameHighArc.u*(A (returnCut+z)+1/2)<returnDistance z := by
  have hp := ReturnPolynomial.square_positive hz
  rw [ReturnPolynomial.square_eval] at hp
  have hc := A_circle hb
  have ha := A_shift_pos hb
  have hd := return_distance_positive hz
  dsimp [FrameHighArc.u] at *
  nlinarith

theorem frameCost_cubic_lower {z : ℝ} (hz : 0≤z) :
    z/2-z^2/4-z^3/12≤frameCost z := by
  have hs := Real.sin_ge_sub_cube hz
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  dsimp [frameCost]
  linarith

theorem return_distance_identity (z : ℝ) :
    returnDistance z=3*(8833/10000)+(314159/100000)/4+
      (FrameHighArc.u-FrameHighArc.v)*(449607/500000)-
      (kappa-FrameHighArc.v)*(returnCut+z)+FrameHighArc.u/2+
      (9/50)*(z/2-z^2/4-z^3/12)-returnThreshold := by
  norm_num [returnDistance,returnCut,FrameHighArc.u,FrameHighArc.v,
    kappa,returnThreshold]
  ring

theorem high_short_scalar {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ))
    (hb : returnCut+z∈Icc 0 c0) :
    returnThreshold<3*(8833/10000)+FrameHighArc.H (returnCut+z)-
      kappa*(returnCut+z)+(9/50)*frameCost z := by
  have hh := return_root_comparison hz hb
  rw [return_distance_identity] at hh
  have hw := frameCost_cubic_lower hz.1
  have hc := FrameHighArc.diagonal_bounds.1
  have hp := Arithmetic.pi_hand_enclosure.1
  dsimp [FrameHighArc.H,FrameHighArc.k,FrameHighArc.u,FrameHighArc.v] at hh ⊢
  nlinarith only [hh,hw,hc,hp]

theorem returnCut_mem : returnCut∈Icc b2 c0 := by
  dsimp [returnCut]
  constructor <;> linarith [b2_bounds.2,c0_bounds.1]

theorem high_return_below_cut {b gain : ℝ} (hb : b∈Icc b2 c0)
    (hcut : b≤returnCut) (hg : 0≤gain) :
    returnThreshold<3*(8833/10000)+FrameHighArc.H b-kappa*b+(9/50)*gain := by
  have hzero := high_short_scalar (z := 0) (by norm_num)
    (by simpa using And.intro (b2_mem.1.trans returnCut_mem.1) returnCut_mem.2)
  simp only [add_zero,frameCost_zero,mul_zero] at hzero
  have hmono := FrameHighArc.loss_antitone
    (lambda := kappa) (by norm_num [kappa,FrameHighArc.u,FrameHighArc.v])
    hb returnCut_mem hcut
  linarith

theorem high_return_large {b gain : ℝ} (hb : b∈Icc b2 c0)
    (hg : frameCost (3/10)≤gain) :
    returnThreshold<3*(8833/10000)+FrameHighArc.H b-kappa*b+(9/50)*gain := by
  have hmono := FrameHighArc.loss_antitone
    (lambda := kappa) (by norm_num [kappa,FrameHighArc.u,FrameHighArc.v])
    hb ⟨b2_mem.2,le_rfl⟩ hb.2
  simp only [FrameHighArc.H_c0] at hmono
  have hw := frameCost_cubic_lower (by norm_num : (0:ℝ)≤3/10)
  have hc := FrameHighArc.diagonal_bounds.2
  have hp := Arithmetic.pi_hand_enclosure.1
  dsimp [returnThreshold,kappa] at *
  norm_num at hw
  linarith

/-- The scalar return reserve. The premise for short errors, `R ≤ 3/10 → s.b ≤ 4 c0 - 3 + R`, is
the endpoint inequality of the three projections. -/
theorem return_marker_reserve (s : State) {R gain : ℝ}
    (hR : 0≤R) (hgain : frameCost (min R (3/10))≤gain)
    (hendpoint : R≤3/10 → s.b≤4*c0-3+R) :
    returnThreshold<3*(8833/10000)+ZeroPrimary.unsigned s-kappa*s.b+(9/50)*gain := by
  have hg0 : 0≤gain := by
    have hz : min R (3/10)∈Icc 0 (Real.pi/4) :=
      ⟨le_min hR (by norm_num),by linarith [min_le_right R (3/10:ℝ),Real.pi_gt_three]⟩
    exact (frameCost_nonneg hz).trans hgain
  cases hs : s.branch with
  | coreSide | coreCorner =>
      have hc : s.branch.type=0 := by simp [hs,Branch.type]
      have ha := (core_bounds s hc).1
      have hb := s.b_nonneg
      dsimp [ZeroPrimary.unsigned]
      rw [hs]
      dsimp [FramePair.label,kappa,returnThreshold]
      nlinarith
  | low =>
      have hm := marker_linear_lower s
      have ht : 4*s.b≤ s.a := by simpa [hs,TypeMem] using s.type_mem
      have hu := (ZeroPrimary.coordinates s).2.1
      dsimp [kappa,returnThreshold]
      linarith
  | middle =>
      have hm := marker_linear_lower s
      have htype : s.a≤4*s.b ∧ 7*s.b≤3*s.a := by
        simpa [hs,TypeMem] using s.type_mem
      have ht := htype.2
      have hu := (ZeroPrimary.coordinates s).2.1
      dsimp [kappa,returnThreshold]
      linarith
  | high =>
      have hb := FrameHighArc.state_high_chart s hs
      have hlabel : ZeroPrimary.unsigned s=FrameHighArc.H s.b := by
        dsimp [ZeroPrimary.unsigned]
        rw [hs,hb.1]
        dsimp [FramePair.label,FrameHighArc.H,FrameHighArc.k,
          FrameHighArc.u,FrameHighArc.v]
        ring
      rw [hlabel]
      by_cases hlarge : 3/10≤R
      · apply high_return_large hb.2
        simpa only [min_eq_right hlarge] using hgain
      · have hsmall : R≤3/10 := le_of_not_ge hlarge
        have he := hendpoint hsmall
        by_cases hcut : s.b≤returnCut
        · exact high_return_below_cut hb.2 hcut hg0
        · have hz0 : 0≤ s.b-returnCut := by linarith
          have hzR : s.b-returnCut≤R := by
            have hc := FrameHighArc.diagonal_bounds.2
            dsimp [returnCut]
            linarith
          have hz : s.b-returnCut∈Icc 0 (3/10:ℝ) := ⟨hz0,hzR.trans hsmall⟩
          have hpoint : returnCut+(s.b-returnCut)=s.b := by ring
          have hscalar := high_short_scalar hz
            (by rw [hpoint]; exact ⟨b2_mem.1.trans hb.2.1,hb.2.2⟩)
          rw [hpoint] at hscalar
          have hm := frameCost_monotone
            (show s.b-returnCut∈Icc 0 (Real.pi/4) from
              ⟨hz0,by linarith [hz.2,Real.pi_gt_three]⟩)
            (show R∈Icc 0 (Real.pi/4) from
              ⟨hR,by linarith [hsmall,Real.pi_gt_three]⟩) hzR
          rw [min_eq_left hsmall] at hgain
          linarith

end SquaresInCircles.Eight.GlobalBT
end
end
end
