module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2Concentration

/-!
# A charged distinguished block with the two original signed budgets

Uncompiled concentration used by the genuine negative-EH companions.
The two simplex reductions preserve each signed total. The affine
charge on positive mass is retained before the common-mass endpoint
step, so it appears at the actual pure or saturated endpoint, rather
than being discarded or bounded by an unrelated budget.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ChargedHybridConcentration
open PositiveAngularEnvelope OrdinaryAngleConcavity PositiveTD.Hybrid
open GlobalGA.NegativeAPositiveTD.Concentration

variable {ι : Type*} [DecidableEq ι]

def positive (R a ε : ℝ) (p q : ι→ℝ) (d i : ι) (P : ℝ) : ℝ :=
  PositiveTD.Hybrid.positive R a p q d i P-ε*P
def block (R a ε : ℝ) (p q : ι→ℝ) (d i : ι) (P N : ℝ) : ℝ :=
  PositiveTD.Hybrid.block R a p q d i P N-ε*P
def pure (R a ε : ℝ) (p q : ι→ℝ) (d i j : ι) (s θ : ℝ) : ℝ :=
  if s≤θ then V R (p j) (q j) (θ-s) else positive R a ε p q d i (s-θ)
def saturated (R a ε : ℝ) (p q : ι→ℝ) (d i j : ι) (s θ : ℝ) : ℝ :=
  if i=j then block R a ε p q d i (frameCap-θ) (frameCap-s)
  else positive R a ε p q d i (frameCap-θ)+V R (p j) (q j) (frameCap-s)

theorem subtract_affine {S : Set ℝ} {f : ℝ→ℝ} (hf : ConcaveOn ℝ S f) (a b : ℝ) :
    ConcaveOn ℝ S (fun x => f x-(a*x+b)) := by
  refine ⟨hf.1,?_⟩
  intro x hx y hy u v hu hv huv
  have hh := hf.2 hx hy hu hv huv
  simp only [smul_eq_mul] at hh ⊢
  have hconst := congrArg (fun z : ℝ => z*b) huv
  nlinarith

@[simp] theorem block_zero_left (R a ε : ℝ) (p q : ι→ℝ) (d i : ι) (N : ℝ) :
    block R a ε p q d i 0 N=V R (p i) (q i) N := by
  simp [block]
@[simp] theorem block_zero_right (R a ε : ℝ) (p q : ι→ℝ) (d i : ι) (P : ℝ) :
    block R a ε p q d i P 0=positive R a ε p q d i P := by
  simp [block,positive]
@[simp] theorem positive_zero (R a ε : ℝ) (p q : ι→ℝ) (d i : ι) :
    positive R a ε p q d i 0=0 := by simp [positive]

theorem forward_same_concave {R a ε t : ℝ} {p q : ι→ℝ} {d i : ι}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t)) (fun P => block R a ε p q d i P (t+P)) := by
  simpa only [block,add_zero] using
    subtract_affine (same_block_line_concave (d:=d) hR hQ hp hpq hqp ht) ε 0

theorem forward_separated_concave {R a ε t : ℝ} {p q : ι→ℝ} {d i j : ι}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (hp' : 0<p j) (hpq' : p j≤q j) (hqp' : q j≤2*p j)
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t))
      (fun P => positive R a ε p q d i P+V R (p j) (q j) (t+P)) := by
  have hh := subtract_affine
    (separated_line_concave (d:=d) hR hQ hp hpq hqp hp' hpq' hqp' ht) ε 0
  simpa only [positive,add_zero,sub_add_eq_add_sub] using hh

theorem backward_same_concave {R a ε t : ℝ} {p q : ι→ℝ} {d i : ι}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t)) (fun N => block R a ε p q d i (t+N) N) := by
  have hh := subtract_affine (reverse_same_line_concave (d:=d) hR hQ hp hpq hqp ht) ε (ε*t)
  simpa only [block,mul_add,add_comm (ε*t)] using hh

theorem backward_separated_concave {R a ε t : ℝ} {p q : ι→ℝ} {d i j : ι}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (hp' : 0<p j) (hpq' : p j≤q j) (hqp' : q j≤2*p j)
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t))
      (fun N => positive R a ε p q d i (t+N)+V R (p j) (q j) N) := by
  have hh := subtract_affine
    (reverse_separated_line_concave (d:=d) hR hQ hp hpq hqp hp' hpq' hqp' ht) ε (ε*t)
  simpa only [positive,mul_add,add_comm (ε*t),sub_add_eq_add_sub] using hh

theorem concentrate [Fintype ι] [Nonempty ι]
    (R a ε : ℝ) (p q P N : ι→ℝ) (d : ι) {s θ : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀i,0<p i) (hpq : ∀i,p i≤q i) (hqp : ∀i,q i≤2*p i)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hs : s∈Icc 0 frameCap) (hθ : θ∈Icc 0 frameCap)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,min (pure R a ε p q d i j s θ) (saturated R a ε p q d i j s θ)≤
      ∑k,block R a ε p q d k (P k) (N k) := by
  have hPt : (∑i,P i)≤frameCap := by linarith [hθ.1]
  have hNt : (∑i,N i)≤frameCap := by linarith [hs.1]
  obtain ⟨i,j,hij⟩ := PositiveTD.Hybrid.both_signs_concentrate
    R a p q P N d hR hQ hp hpq hqp hP hN hPt hNt
  have hcharge := sub_le_sub_right hij (ε*∑i,P i)
  have hsum : (∑k,block R a ε p q d k (P k) (N k))=
      (∑k,PositiveTD.Hybrid.block R a p q d k (P k) (N k))-ε*∑k,P k := by
    simp [block,Finset.sum_sub_distrib,Finset.mul_sum]
  refine ⟨i,j,?_⟩
  rw [hsum]
  by_cases horder : s≤θ
  · have ht : θ-s∈Icc 0 frameCap := ⟨by linarith,by linarith [hθ.2,hs.1]⟩
    have htotal : (∑i,P i)∈Icc 0 (frameCap-θ) :=
      ⟨Finset.sum_nonneg (fun i _ => hP i),hPb⟩
    have hspan : 0≤frameCap-θ := by linarith [hθ.2]
    have heq : (∑i,N i)=(θ-s)+(∑i,P i) := by linarith
    have hlast : (θ-s)+(frameCap-θ)=frameCap-s := by ring
    by_cases hsame : i=j
    · subst j
      simp only [pure,if_pos horder,saturated,if_pos rfl] at ⊢
      simp only [if_pos rfl,heq] at hcharge
      have hc := (forward_same_concave (ε:=ε) (d:=d) hR hQ (hp i) (hpq i) (hqp i) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-θ))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      rw [add_zero,block_zero_left,hlast] at hh
      exact hh.trans hcharge
    · simp only [pure,if_pos horder,saturated,if_neg hsame] at ⊢
      simp only [if_neg hsame,heq] at hcharge
      have hc := (forward_separated_concave (ε:=ε) (d:=d) hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-θ))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [positive_zero,zero_add,add_zero,hlast] at hh
      dsimp only [positive] at hh
      linarith
  · have ht : s-θ∈Icc 0 frameCap := ⟨by linarith,by linarith [hs.2,hθ.1]⟩
    have htotal : (∑i,N i)∈Icc 0 (frameCap-s) :=
      ⟨Finset.sum_nonneg (fun i _ => hN i),hNb⟩
    have hspan : 0≤frameCap-s := by linarith [hs.2]
    have heq : (∑i,P i)=(s-θ)+(∑i,N i) := by linarith
    have hlast : (s-θ)+(frameCap-s)=frameCap-θ := by ring
    by_cases hsame : i=j
    · subst j
      simp only [pure,if_neg horder,saturated,if_pos rfl] at ⊢
      simp only [if_pos rfl,heq] at hcharge
      have hc := (backward_same_concave (ε:=ε) (d:=d) hR hQ (hp i) (hpq i) (hqp i) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hθ.1])) (convex_Icc 0 (frameCap-s))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      rw [add_zero,block_zero_right,hlast] at hh
      exact hh.trans hcharge
    · simp only [pure,if_neg horder,saturated,if_neg hsame] at ⊢
      simp only [if_neg hsame,heq] at hcharge
      have hc := (backward_separated_concave (ε:=ε) (d:=d) hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hθ.1])) (convex_Icc 0 (frameCap-s))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [V_zero,add_zero,hlast] at hh
      dsimp only [positive] at hh
      linarith

end SquaresInCircles.Eight.TableFree.ChargedHybridConcentration
