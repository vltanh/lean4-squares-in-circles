module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2CoefficientDomain

/-!
# Concentrating both remaining signed totals after negative A and TD2

Uncompiled transcription of Section 3 of the angle companion. Both
actual totals are preserved by the simplex reductions. The remaining
common total then reaches either its pure endpoint or the simultaneous
budgets h-z and h-s. Both possible signs of z-s are included.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Concentration
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open PositiveTD.Hybrid

variable {ι : Type*} [DecidableEq ι]

theorem reverse_ordinary_line_concave {R p q t : ℝ}
    (hp : 0≤p) (hq : 0≤q) (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t)) (fun N => mixedBlock R p q (t+N) N) := by
  let f (N : ℝ) := p*(PositiveAngularEnvelope.phi (t+N)-1)+q*(Real.cos N-1)-
    R*(pairNorm p q t-pairNorm p q 0)
  have he (N : ℝ) : mixedBlock R p q (t+N) N=f N := by
    dsimp [mixedBlock,f]
    rw [show t+N-N=t by ring]
  simp_rw [he]
  apply concave_of_deriv2
    (f':=fun N => p*(Real.cos (t+N)-Real.sin (t+N))-q*Real.sin N)
    (f'':=fun N => -p*PositiveAngularEnvelope.phi (t+N)-q*Real.cos N)
  · intro N hN
    have hc := (Real.hasDerivAt_cos (t+N)).comp N ((hasDerivAt_id N).const_add t)
    have hs := (Real.hasDerivAt_sin (t+N)).comp N ((hasDerivAt_id N).const_add t)
    have hh := ((((hc.add hs).sub_const 1).const_mul p).add
      (((Real.hasDerivAt_cos N).sub_const 1).const_mul q)).sub_const
        (R*(pairNorm p q t-pairNorm p q 0))
    convert hh using 1
    · rfl
    · ring
  · intro N hN
    have hc := (Real.hasDerivAt_cos (t+N)).comp N ((hasDerivAt_id N).const_add t)
    have hs := (Real.hasDerivAt_sin (t+N)).comp N ((hasDerivAt_id N).const_add t)
    convert ((hc.sub hs).const_mul p).sub ((Real.hasDerivAt_sin N).const_mul q) using 1
    · rfl
    · dsimp [PositiveAngularEnvelope.phi]
      ring
  · intro N hN
    have hNN : N∈Icc 0 frameCap := ⟨hN.1,by linarith [hN.2,ht.1]⟩
    have hNP : t+N∈Icc 0 frameCap := ⟨by linarith [hN.1,ht.1],by linarith [hN.2]⟩
    have hphi : 0≤PositiveAngularEnvelope.phi (t+N) := by
      dsimp [PositiveAngularEnvelope.phi]
      linarith [(transport_trig hNP).1,(transport_trig hNP).2.2.1]
    have hcos : 0≤Real.cos N := by linarith [(transport_trig hNN).1]
    nlinarith [mul_nonneg hp hphi,mul_nonneg hq hcos]

theorem reverse_same_line_concave {R a t : ℝ} {p q : ι→ℝ} {d i : ι}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t))
      (fun N => block R a p q d i (t+N) N) := by
  by_cases hi : i=d
  · have hlin : ConcaveOn ℝ (Icc 0 (frameCap-t)) (fun N : ℝ => -a*(t+N)) := by
      refine ⟨convex_Icc 0 (frameCap-t),?_⟩
      intro x hx y hy u v hu hv huv
      simp only [smul_eq_mul]
      nlinarith [congrArg (fun x : ℝ => x*(a*t)) huv]
    have hV := (V_concave hR hQ hp hpq hqp).subset
      (Icc_subset_Icc le_rfl (by linarith [ht.1])) (convex_Icc 0 (frameCap-t))
    convert hlin.add hV using 1
    funext N
    simp only [block,hi,↓reduceIte,Pi.add_apply]
  · simpa only [block,hi,↓reduceIte] using
      reverse_ordinary_line_concave (R:=R) hp.le (hp.trans_le hpq).le ht

theorem reverse_separated_line_concave {R a t : ℝ} {p q : ι→ℝ} {d i j : ι}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hpi : 0<p i) (hpqi : p i≤q i) (hqpi : q i≤2*p i)
    (hpj : 0<p j) (hpqj : p j≤q j) (hqpj : q j≤2*p j)
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t))
      (fun N => positive R a p q d i (t+N)+V R (p j) (q j) N) := by
  have hU := concave_affine_argument (positive_concave (a:=a) (d:=d) hR hQ hpi hpqi hqpi)
    (a:=1) (b:=t) (l:=0) (u:=frameCap-t)
    (fun N hN => ⟨by linarith [hN.1,ht.1],by linarith [hN.2]⟩)
  have hV := (V_concave hR hQ hpj hpqj hqpj).subset
    (Icc_subset_Icc le_rfl (by linarith [ht.1])) (convex_Icc 0 (frameCap-t))
  convert hU.add hV using 1
  funext N
  simp only [Pi.add_apply,one_mul,add_comm N t]

def pure (R a : ℝ) (p q : ι→ℝ) (d i j : ι) (s z : ℝ) : ℝ :=
  if s≤z then V R (p j) (q j) (z-s) else positive R a p q d i (s-z)
def saturated (R a : ℝ) (p q : ι→ℝ) (d i j : ι) (s z : ℝ) : ℝ :=
  if i=j then block R a p q d i (frameCap-z) (frameCap-s)
  else positive R a p q d i (frameCap-z)+V R (p j) (q j) (frameCap-s)

theorem concentrate [Fintype ι] [Nonempty ι]
    (R a : ℝ) (p q P N : ι→ℝ) (d : ι) {s z : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀i,0<p i) (hpq : ∀i,p i≤q i) (hqp : ∀i,q i≤2*p i)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hPbudget : (∑i,P i)≤frameCap-z) (hNbudget : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=z-s) :
    ∃i j,min (pure R a p q d i j s z) (saturated R a p q d i j s z)≤
      ∑k,block R a p q d k (P k) (N k) := by
  have hPt : (∑i,P i)≤frameCap := by linarith [hz.1]
  have hNt : (∑i,N i)≤frameCap := by linarith [hs.1]
  obtain ⟨i,j,hij⟩ := both_signs_concentrate R a p q P N d hR hQ hp hpq hqp hP hN hPt hNt
  refine ⟨i,j,?_⟩
  by_cases hsz : s≤z
  · have ht : z-s∈Icc 0 frameCap := ⟨by linarith,by linarith [hz.2,hs.1]⟩
    have htotal : (∑i,P i)∈Icc 0 (frameCap-z) :=
      ⟨Finset.sum_nonneg (fun i _ => hP i),hPbudget⟩
    have hspan : 0≤frameCap-z := by linarith [hz.2]
    have hbalance' : (∑i,N i)=(z-s)+(∑i,P i) := by linarith
    have he : (z-s)+(frameCap-z)=frameCap-s := by ring
    by_cases heq : i=j
    · subst j
      simp only [pure,hsz,saturated,↓reduceIte]
      simp only [↓reduceIte,hbalance'] at hij
      have hconc := (same_block_line_concave (a:=a) (d:=d) hR hQ (hp i) (hpq i) (hqp i)
        ht).subset (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-z))
      have hmin := hconc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      rw [add_zero,block_zero_left,he] at hmin
      exact hmin.trans hij
    · simp only [pure,hsz,saturated,heq,↓reduceIte]
      simp only [heq,↓reduceIte,hbalance'] at hij
      have hconc := (separated_line_concave (a:=a) (d:=d) hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-z))
      have hmin := hconc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [positive_zero,zero_add,add_zero,he] at hmin
      exact hmin.trans hij
  · have ht : s-z∈Icc 0 frameCap := ⟨by linarith,by linarith [hs.2,hz.1]⟩
    have htotal : (∑i,N i)∈Icc 0 (frameCap-s) :=
      ⟨Finset.sum_nonneg (fun i _ => hN i),hNbudget⟩
    have hspan : 0≤frameCap-s := by linarith [hs.2]
    have hbalance' : (∑i,P i)=(s-z)+(∑i,N i) := by linarith
    have he : (s-z)+(frameCap-s)=frameCap-z := by ring
    by_cases heq : i=j
    · subst j
      simp only [pure,hsz,saturated,↓reduceIte]
      simp only [↓reduceIte,hbalance'] at hij
      have hconc := (reverse_same_line_concave (a:=a) (d:=d) hR hQ
        (hp i) (hpq i) (hqp i) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hz.1])) (convex_Icc 0 (frameCap-s))
      have hmin := hconc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      rw [add_zero,block_zero_right,he] at hmin
      exact hmin.trans hij
    · simp only [pure,hsz,saturated,heq,↓reduceIte]
      simp only [heq,↓reduceIte,hbalance'] at hij
      have hconc := (reverse_separated_line_concave (a:=a) (d:=d) hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hz.1])) (convex_Icc 0 (frameCap-s))
      have hmin := hconc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [V_zero,add_zero,he] at hmin
      exact hmin.trans hij

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Concentration
