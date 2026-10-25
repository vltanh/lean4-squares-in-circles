module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcentration
public import SquaresInCircles.Eight.Owners.GA.ChargedPairs
public import SquaresInCircles.Eight.Owners.GA.Sorted.Support

/-!
# Eight squares: signed concentration with the sorted-D minorant

In the sum of the blocks `block`, the distinguished block `d` has the linear positive increment
`-a * P` and an ordinary negative increment; the other blocks keep their coupled two-angle norms
(`mixedBlock`). Both sign totals are kept through the two simplex reductions
(`both_signs_concentrate`), before the common total is sent to an intrinsic endpoint
(`concentrate`). The concentration acts on the masses of the scalar sum; no geometric angle of the
cycle is concentrated.
-/

section
/-!
## Two-error bounds on the original high-GA support points

The two signed error budgets come directly from the
original seven-cycle variations.  The support identity is exact for the
actual point and does not assume a maximizing radial state.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.Secondary
open Candidate PositiveAngularEnvelope

def pairF (p q a b : ℝ) : ℝ := q*Real.cos b+p*Real.sin a
def pairG (p q a b : ℝ) : ℝ := p*Real.cos a+q*Real.sin b

def pairIncrement (p q a b : ℝ) (P : SignedPoint) : ℝ :=
  p*(edgeWidth a-1)+q*(edgeWidth b-1)-
    (pairF p q a b*P.a+pairG p q a b*P.y)+
    fullSupport q p+charge*(a+b)

theorem pair_force_norm (p q a b : ℝ) :
    Real.sqrt ((pairF p q a b)^2+(pairG p q a b)^2)=pairNorm p q (a+b) := by
  simpa [rotatedPair,pairF,pairG,pairNorm_symm,add_comm] using
    rotatedPair_norm q p a b

theorem pair_full_identity {p q a b : ℝ}
    (ha : |a|≤frameCap) (hb : |b|≤frameCap) :
    p*(edgeWidth a-1)+q*(edgeWidth b-1)-
      fullSupport (pairF p q a b) (pairG p q a b)+
      fullSupport q p+charge*(a+b)=chargedPair p q a b := by
  rw [fullSupport_pair p q]
  unfold fullSupport
  rw [pair_force_norm]
  have ha' := width_add_half_phi ha
  have hb' := width_add_half_phi hb
  dsimp [chargedPair,pairF,pairG,PositiveAngularEnvelope.phi] at *
  nlinarith [congrArg (fun x : ℝ => p*x) ha',
    congrArg (fun x : ℝ => q*x) hb']

theorem actual_pair_lower {r p q a b : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (ha : |a|≤frameCap) (hb : |b|≤frameCap) :
    chargedPair p q a b≤pairIncrement p q a b P := by
  have hs := actual_full_support (f:=pairF p q a b) (g:=pairG p q a b) hy hc hr
  rw [← pair_full_identity ha hb]
  dsimp [pairIncrement]
  linarith

theorem two_positive_errors_le (θ : Vertex → ℝ) {i j : Vertex} (hij : i≠j) :
    positivePart (delta θ i)+positivePart (delta θ j)≤positiveVariation θ := by
  classical
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (s:=({i,j}:Finset Vertex)) (t:=Finset.univ)
    (f:=fun v => positivePart (delta θ v))
    (by simp) (fun v _ _ => positivePart_nonneg (delta θ v))
  simpa [positiveVariation,hij] using h

theorem two_negative_errors_le (θ : Vertex → ℝ) {i j : Vertex} (hij : i≠j) :
    negativePart (delta θ i)+negativePart (delta θ j)≤negativeVariation θ := by
  classical
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (s:=({i,j}:Finset Vertex)) (t:=Finset.univ)
    (f:=fun v => negativePart (delta θ v))
    (by simp) (fun v _ _ => negativePart_nonneg (delta θ v))
  simpa [negativeVariation,hij] using h

theorem pair_error_bounds {a b : ℝ}
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    |a|≤frameCap ∧ |b|≤frameCap ∧ |a+b|≤frameCap := by
  have ha := positive_sub_negative a
  have hb := positive_sub_negative b
  have hpa := positivePart_nonneg a
  have hpb := positivePart_nonneg b
  have hna := negativePart_nonneg a
  have hnb := negativePart_nonneg b
  exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,
    abs_le.mpr ⟨by linarith,by linarith⟩,
    abs_le.mpr ⟨by linarith,by linarith⟩⟩

theorem original_pair_budgets {θ : Vertex → ℝ} {i j : Vertex}
    (hP : positiveVariation θ≤frameCap)
    (hN : negativeVariation θ≤frameCap) (hij : i≠j) :
    positivePart (delta θ i)+positivePart (delta θ j)≤frameCap ∧
      negativePart (delta θ i)+negativePart (delta θ j)≤frameCap :=
  ⟨(two_positive_errors_le θ hij).trans hP,
    (two_negative_errors_le θ hij).trans hN⟩

theorem original_error_bound {θ : Vertex → ℝ}
    (hP : positiveVariation θ≤frameCap) (hN : negativeVariation θ≤frameCap)
    (i : Vertex) : |delta θ i|≤frameCap := by
  have hp := (positive_error_le_variation θ i).trans hP
  have hn := (negative_error_le_variation θ i).trans hN
  have he := positive_sub_negative (delta θ i)
  exact abs_le.mpr ⟨by linarith [positivePart_nonneg (delta θ i)],
    by linarith [negativePart_nonneg (delta θ i)]⟩

theorem actual_G_pair {r a b : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    -(576/10000:ℝ)<pairIncrement k l a b P := by
  have he := pair_error_bounds hP hN
  exact (G_pair_lower hP hN).trans_le (actual_pair_lower hy hc hr he.1 he.2.1)

theorem actual_H_pair {r a b : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    -(22/10000:ℝ)<pairIncrement k 1 a b P := by
  have he := pair_error_bounds hP hN
  exact (H_pair_lower hP hN).trans_le (actual_pair_lower hy hc hr he.1 he.2.1)

theorem actual_B_pair {r a b : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    -(44/10000:ℝ)<pairIncrement l 2 a b P := by
  have he := pair_error_bounds hP hN
  exact (B_pair_lower hP hN).trans_le (actual_pair_lower hy hc hr he.1 he.2.1)

end SquaresInCircles.Eight.GlobalGA.Secondary
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.PositiveTD.Hybrid
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration

variable {ι : Type*} [DecidableEq ι]

def block (R a : ℝ) (p q : ι → ℝ) (d i : ι) (P N : ℝ) : ℝ :=
  if i=d then -a*P+V R (p i) (q i) N else mixedBlock R (p i) (q i) P N

def positive (R a : ℝ) (p q : ι → ℝ) (d i : ι) (P : ℝ) : ℝ :=
  if i=d then -a*P else U R (p i) (q i) P

def saturated (R a : ℝ) (p q : ι → ℝ) (d i : ι) (z : ℝ) : ℝ :=
  if i=d then -a*(frameCap-z)+V R (p i) (q i) frameCap
  else M R (p i) (q i) z

@[simp] theorem block_zero_right (R a : ℝ) (p q : ι → ℝ) (d i : ι) (P : ℝ) :
    block R a p q d i P 0=positive R a p q d i P := by
  by_cases hi : i=d <;> simp [block,positive,hi]

@[simp] theorem block_zero_left (R a : ℝ) (p q : ι → ℝ) (d i : ι) (N : ℝ) :
    block R a p q d i 0 N=V R (p i) (q i) N := by
  by_cases hi : i=d <;> simp [block,hi]

@[simp] theorem positive_zero (R a : ℝ) (p q : ι → ℝ) (d i : ι) :
    positive R a p q d i 0=0 := by
  by_cases hi : i=d <;> simp [positive,hi]

theorem block_saturated (R a : ℝ) (p q : ι → ℝ) (d i : ι) (z : ℝ) :
    block R a p q d i (frameCap-z) (z+(frameCap-z))=saturated R a p q d i z := by
  by_cases hi : i=d
  · simp [block,saturated,hi]
  · simp only [block,saturated,ite_eq_right hi]
    exact mixedBlock_saturated R (p i) (q i) z

theorem block_concave_positive {R a : ℝ} {p q : ι → ℝ} {d i : ι} {N : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (hN : N∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun P => block R a p q d i P N) := by
  by_cases hi : i=d
  · simp only [block,ite_eq_left hi]
    refine ⟨convex_Icc 0 frameCap,?_⟩
    intro x hx y hy u v hu hv huv
    simp only [smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ => t*V R (p i) (q i) N) huv]
  · simpa only [block,ite_eq_right hi] using
      mixedBlock_concave_positive hR hQ hp hpq hqp hN

theorem block_concave_negative {R a : ℝ} {p q : ι → ℝ} {d i : ι} {P : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (hP : P∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (block R a p q d i P) := by
  by_cases hi : i=d
  · have he : block R a p q d i P=fun N => V R (p i) (q i) N+-a*P := by
      funext N
      simp only [block,hi,↓reduceIte]
      ring
    rw [he]
    exact (V_concave hR hQ hp hpq hqp).add_const (-a*P)
  · have he : block R a p q d i P=mixedBlock R (p i) (q i) P := by
      funext N
      simp only [block,hi,↓reduceIte]
    rw [he]
    exact mixedBlock_concave_negative hR hQ hp hpq hqp hP

theorem positive_concave {R a : ℝ} {p q : ι → ℝ} {d i : ι}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i) :
    ConcaveOn ℝ (Icc 0 frameCap) (positive R a p q d i) := by
  simpa only [block_zero_right] using block_concave_positive (d:=d)
    hR hQ hp hpq hqp (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])

theorem same_block_line_concave {R a z : ℝ} {p q : ι → ℝ} {d i : ι}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (hz : z∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-z))
      (fun P => block R a p q d i P (z+P)) := by
  by_cases hi : i=d
  · have hlin : ConcaveOn ℝ (Icc 0 (frameCap-z)) (fun P : ℝ => -a*P+0) :=
      affine_concave (-a) 0 0 (frameCap-z)
    have hV := concave_affine_argument (V_concave hR hQ hp hpq hqp)
      (a:=1) (b:=z) (l:=0) (u:=frameCap-z)
      (fun P hP => ⟨by linarith [hP.1,hz.1],by linarith [hP.2]⟩)
    have hfun : (fun P => block R a p q d i P (z+P))=
        (fun P : ℝ => -a*P+0)+(fun x => V R (p i) (q i) (1*x+z)) := by
      funext P
      simp only [block,hi,↓reduceIte,Pi.add_apply,one_mul,add_zero,add_comm z P]
    rw [hfun]
    exact hlin.add hV
  · have he : (fun P => block R a p q d i P (z+P))=
        (fun P => mixedBlock R (p i) (q i) P (z+P)) := by
      funext P
      simp only [block,hi,↓reduceIte]
    rw [he]
    exact sameBlockLine_concave (R:=R) hp.le (hp.trans_le hpq).le hz

theorem separated_line_concave {R a z : ℝ} {p q : ι → ℝ} {d i j : ι}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hpi : 0<p i) (hpqi : p i≤q i) (hqpi : q i≤2*p i)
    (hpj : 0<p j) (hpqj : p j≤q j) (hqpj : q j≤2*p j)
    (hz : z∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-z))
      (fun P => positive R a p q d i P+V R (p j) (q j) (z+P)) := by
  have hU := (positive_concave (a:=a) (d:=d) hR hQ hpi hpqi hqpi).subset
    (Icc_subset_Icc le_rfl (by linarith [hz.1])) (convex_Icc 0 (frameCap-z))
  have hV := concave_affine_argument (V_concave hR hQ hpj hpqj hqpj)
    (a:=1) (b:=z) (l:=0) (u:=frameCap-z)
    (fun P hP => ⟨by linarith [hP.1,hz.1],by linarith [hP.2]⟩)
  have hfun : (fun P => positive R a p q d i P+V R (p j) (q j) (z+P))=
      positive R a p q d i+(fun x => V R (p j) (q j) (1*x+z)) := by
    funext P
    simp only [Pi.add_apply,one_mul,add_comm z P]
  rw [hfun]
  exact hU.add hV

theorem concentrated_sum [Fintype ι] (R a : ℝ) (p q : ι → ℝ)
    (d i j : ι) (P N : ℝ) :
    (∑ k,block R a p q d k (massAt i P k) (massAt j N k))=
      if i=j then block R a p q d i P N
      else positive R a p q d i P+V R (p j) (q j) N := by
  by_cases hij : i=j
  · subst j
    have he (k : ι) : block R a p q d k (massAt i P k) (massAt i N k)=
        if k=i then block R a p q d i P N else 0 := by
      by_cases hki : k=i
      · subst k
        simp [massAt]
      · simp [massAt,hki]
    simp_rw [he]
    simp
  · have he (k : ι) : block R a p q d k (massAt i P k) (massAt j N k)=
        (if k=i then positive R a p q d i P else 0)+
        (if k=j then V R (p j) (q j) N else 0) := by
      by_cases hki : k=i
      · subst k
        simp [massAt,hij]
      · by_cases hkj : k=j
        · subst k
          simp [massAt,hki]
        · simp [massAt,hki,hkj]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp [hij]

theorem both_signs_concentrate [Fintype ι] [Nonempty ι]
    (R a : ℝ) (p q P N : ι → ℝ) (d : ι)
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hqp : ∀ i,q i≤2*p i)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hPt : (∑ i,P i)≤frameCap) (hNt : (∑ i,N i)≤frameCap) :
    ∃ i j, (if i=j then block R a p q d i (∑ k,P k) (∑ k,N k)
      else positive R a p q d i (∑ k,P k)+V R (p j) (q j) (∑ k,N k))≤
        ∑ k,block R a p q d k (P k) (N k) := by
  have hPi (i : ι) : P i∈Icc 0 frameCap := by
    refine ⟨hP i,?_⟩
    exact (Finset.single_le_sum (fun k _ => hP k) (Finset.mem_univ i)).trans hPt
  obtain ⟨j,hj⟩ := concave_sum_concentrates
    (fun i => block R a p q d i (P i)) N hN rfl hNt
    (fun i => block_concave_negative hR hQ (hp i) (hpq i) (hqp i) (hPi i))
  have hNm (i : ι) : massAt j (∑ k,N k) i∈Icc 0 frameCap :=
    massAt_mem ⟨Finset.sum_nonneg (fun i _ => hN i),hNt⟩
  obtain ⟨i,hi⟩ := concave_sum_concentrates
    (fun i x => block R a p q d i x (massAt j (∑ k,N k) i)) P hP rfl hPt
    (fun i => block_concave_positive hR hQ (hp i) (hpq i) (hqp i) (hNm i))
  refine ⟨i,j,?_⟩
  rw [← concentrated_sum]
  exact hi.trans hj

/-- The three intrinsic alternatives are the pure negative, the saturated
same block, and the saturated separated pair.  The D same-block value
is its linear-positive/ordinary-negative expression. -/
theorem concentrate [Fintype ι] [Nonempty ι]
    (R a : ℝ) (p q P N : ι → ℝ) (d : ι) {z : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hqp : ∀ i,q i≤2*p i)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hz : z∈Icc 0 frameCap) (hbudget : (∑ i,P i)≤frameCap-z)
    (hbalance : (∑ i,N i)=z+∑ i,P i) :
    ∃ i j, min (V R (p j) (q j) z)
      (if i=j then saturated R a p q d i z
       else positive R a p q d i (frameCap-z)+V R (p j) (q j) frameCap)≤
        ∑ k,block R a p q d k (P k) (N k) := by
  have hPt : (∑ i,P i)≤frameCap := by linarith [hz.1]
  have hNt : (∑ i,N i)≤frameCap := by rw [hbalance]; linarith
  obtain ⟨i,j,hij⟩ := both_signs_concentrate R a p q P N d hR hQ hp hpq hqp hP hN hPt hNt
  have htotal : (∑ i,P i)∈Icc 0 (frameCap-z) :=
    ⟨Finset.sum_nonneg (fun i _ => hP i),hbudget⟩
  have hspan : 0≤frameCap-z := by linarith [hz.2]
  refine ⟨i,j,?_⟩
  by_cases he : i=j
  · subst j
    simp only [↓reduceIte] at hij ⊢
    rw [hbalance] at hij
    have hconc := same_block_line_concave (a:=a) (d:=d) hR hQ (hp i) (hpq i) (hqp i) hz
    have hmin := hconc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
    rw [add_zero,block_zero_left,block_saturated] at hmin
    exact hmin.trans hij
  · simp only [he,↓reduceIte] at hij ⊢
    rw [hbalance] at hij
    have hconc := separated_line_concave (a:=a) (d:=d) hR hQ
      (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) hz
    have hmin := hconc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
    simp only [positive_zero,zero_add,add_zero,
      show z+(frameCap-z)=frameCap by ring] at hmin
    exact hmin.trans hij

end SquaresInCircles.Eight.GlobalGA.PositiveTD.Hybrid
end
end
end
