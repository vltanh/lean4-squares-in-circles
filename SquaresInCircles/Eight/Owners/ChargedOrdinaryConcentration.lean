module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Concentration

/-!
# Eight squares: four ordinary blocks with both signed budgets and an affine charge

No distinguished
linear block is inserted: every original block retains its full norm.
The positive-mass charge is subtracted before either endpoint reduction.
-/

section
/-!
## A charged distinguished block with two signed budgets

The two simplex reductions keep each signed total. The affine charge on the positive mass is kept
through the endpoint step of the common mass, so it appears at the pure or the saturated endpoint
of the concentration (`pure`, `saturated`, `concentrate`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ChargedHybridConcentration
open PositiveAngularEnvelope OrdinaryAngleConcavity GlobalGA.PositiveTD.Hybrid
open GlobalGA.NegativeAPositiveTD.Concentration

variable {ι : Type*} [DecidableEq ι]

def positive (R a ε : ℝ) (p q : ι→ℝ) (d i : ι) (P : ℝ) : ℝ :=
  GlobalGA.PositiveTD.Hybrid.positive R a p q d i P-ε*P
def block (R a ε : ℝ) (p q : ι→ℝ) (d i : ι) (P N : ℝ) : ℝ :=
  GlobalGA.PositiveTD.Hybrid.block R a p q d i P N-ε*P
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
    (separated_line_concave (a:=a) (d:=d) hR hQ hp hpq hqp hp' hpq' hqp' ht) ε 0
  simpa only [positive,add_zero,sub_add_eq_add_sub] using hh


theorem backward_same_concave {R a ε t : ℝ} {p q : ι→ℝ} {d i : ι}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t)) (fun N => block R a ε p q d i (t+N) N) := by
  have hh := subtract_affine (reverse_same_line_concave (a:=a) (d:=d) hR hQ hp hpq hqp ht) ε (ε*t)
  simpa only [block,mul_add,add_comm (ε*t)] using hh


theorem backward_separated_concave {R a ε t : ℝ} {p q : ι→ℝ} {d i j : ι}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (hp' : 0<p j) (hpq' : p j≤q j) (hqp' : q j≤2*p j)
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t))
      (fun N => positive R a ε p q d i (t+N)+V R (p j) (q j) N) := by
  have hh := subtract_affine
    (reverse_separated_line_concave (a:=a) (d:=d) hR hQ hp hpq hqp hp' hpq' hqp' ht) ε (ε*t)
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
  obtain ⟨i,j,hij⟩ := GlobalGA.PositiveTD.Hybrid.both_signs_concentrate
    R a p q P N d hR hQ hp hpq hqp hP hN hPt hNt
  have hsum : (∑k,block R a ε p q d k (P k) (N k))=
      (∑k,GlobalGA.PositiveTD.Hybrid.block R a p q d k (P k) (N k))-ε*∑k,P k := by
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
      rw [pure,saturated,ite_eq_left horder,ite_eq_left rfl]
      rw [ite_eq_left rfl,heq] at hij
      have hc := (forward_same_concave (a:=a) (ε:=ε) (d:=d) hR hQ (hp i) (hpq i) (hqp i)
        ht).subset (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-θ))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [add_zero,ChargedHybridConcentration.block_zero_left,hlast] at hh
      refine hh.trans ?_
      simp only [ChargedHybridConcentration.block]
      linarith
    · rw [pure,saturated,ite_eq_left horder,ite_eq_right hsame]
      rw [ite_eq_right hsame,heq] at hij
      have hc := (forward_separated_concave (a:=a) (ε:=ε) (d:=d) hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-θ))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [ChargedHybridConcentration.positive_zero,zero_add,add_zero,hlast] at hh
      refine hh.trans ?_
      simp only [ChargedHybridConcentration.positive]
      linarith
  · have ht : s-θ∈Icc 0 frameCap := ⟨by linarith,by linarith [hs.2,hθ.1]⟩
    have htotal : (∑i,N i)∈Icc 0 (frameCap-s) :=
      ⟨Finset.sum_nonneg (fun i _ => hN i),hNb⟩
    have hspan : 0≤frameCap-s := by linarith [hs.2]
    have heq : (∑i,P i)=(s-θ)+(∑i,N i) := by linarith
    have hlast : (s-θ)+(frameCap-s)=frameCap-θ := by ring
    by_cases hsame : i=j
    · subst j
      rw [pure,saturated,ite_eq_right horder,ite_eq_left rfl]
      rw [ite_eq_left rfl,heq] at hij
      rw [heq]
      have hc := (backward_same_concave (a:=a) (ε:=ε) (d:=d) hR hQ (hp i) (hpq i) (hqp i)
        ht).subset (Icc_subset_Icc le_rfl (by linarith [hθ.1])) (convex_Icc 0 (frameCap-s))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [add_zero,ChargedHybridConcentration.block_zero_right,hlast] at hh
      refine hh.trans ?_
      simp only [ChargedHybridConcentration.block]
      linarith
    · rw [pure,saturated,ite_eq_right horder,ite_eq_right hsame]
      rw [ite_eq_right hsame,heq] at hij
      rw [heq]
      have hc := (backward_separated_concave (a:=a) (ε:=ε) (d:=d) hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hθ.1])) (convex_Icc 0 (frameCap-s))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [V_zero,add_zero,hlast] at hh
      refine hh.trans ?_
      simp only [ChargedHybridConcentration.positive]
      linarith

end SquaresInCircles.Eight.ChargedHybridConcentration
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ChargedOrdinaryConcentration
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open GlobalGA.NegativeAPositiveTD.Concentration (reverse_ordinary_line_concave)
open ChargedHybridConcentration (subtract_affine)

variable {ι : Type*} [DecidableEq ι]

def positive (R ε : ℝ) (p q : ι→ℝ) (i : ι) (P : ℝ) : ℝ :=
  U R (p i) (q i) P-ε*P
def block (R ε : ℝ) (p q : ι→ℝ) (i : ι) (P N : ℝ) : ℝ :=
  mixedBlock R (p i) (q i) P N-ε*P
def pure (R ε : ℝ) (p q : ι→ℝ) (i j : ι) (s θ : ℝ) : ℝ :=
  if s≤θ then V R (p j) (q j) (θ-s) else positive R ε p q i (s-θ)
def saturated (R ε : ℝ) (p q : ι→ℝ) (i j : ι) (s θ : ℝ) : ℝ :=
  if i=j then block R ε p q i (frameCap-θ) (frameCap-s)
  else positive R ε p q i (frameCap-θ)+V R (p j) (q j) (frameCap-s)

omit [DecidableEq ι] in
@[simp] theorem block_zero_left (R ε : ℝ) (p q : ι→ℝ) (i : ι) (N : ℝ) :
    block R ε p q i 0 N=V R (p i) (q i) N := by simp [block]
omit [DecidableEq ι] in
@[simp] theorem block_zero_right (R ε : ℝ) (p q : ι→ℝ) (i : ι) (P : ℝ) :
    block R ε p q i P 0=positive R ε p q i P := by simp [block,positive]
omit [DecidableEq ι] in
@[simp] theorem positive_zero (R ε : ℝ) (p q : ι→ℝ) (i : ι) :
    positive R ε p q i 0=0 := by simp [positive]

theorem forward_same_concave {R ε p q t : ℝ}
    (hp : 0≤p) (hq : 0≤q) (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t))
      (fun P => mixedBlock R p q P (t+P)-ε*P) := by
  simpa only [add_zero] using
    subtract_affine (sameBlockLine_concave (R:=R) hp hq ht) ε 0

theorem backward_same_concave {R ε p q t : ℝ}
    (hp : 0≤p) (hq : 0≤q) (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t))
      (fun N => mixedBlock R p q (t+N) N-ε*(t+N)) := by
  have hh := subtract_affine (reverse_ordinary_line_concave (R:=R) hp hq ht) ε (ε*t)
  simpa only [mul_add,add_comm (ε*t)] using hh

theorem forward_separated_concave {R ε p q p' q' t : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hp' : 0<p') (hpq' : p'≤q') (hqp' : q'≤2*p')
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t))
      (fun P => U R p q P-ε*P+V R p' q' (t+P)) := by
  have hh := subtract_affine
    (separatedLine_concave hR hQ hp hpq hqp hp' hpq' hqp' ht) ε 0
  simpa only [add_zero,sub_add_eq_add_sub] using hh

theorem backward_separated_concave {R ε p q p' q' t : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hp' : 0<p') (hpq' : p'≤q') (hqp' : q'≤2*p')
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t))
      (fun N => U R p q (t+N)-ε*(t+N)+V R p' q' N) := by
  have hU := concave_affine_argument (U_concave hR hQ hp hpq hqp)
    (a:=1) (b:=t) (l:=0) (u:=frameCap-t)
    (fun N hN => ⟨by linarith [hN.1,ht.1],by linarith [hN.2]⟩)
  have hV := (V_concave hR hQ hp' hpq' hqp').subset
    (Icc_subset_Icc le_rfl (by linarith [ht.1])) (convex_Icc 0 (frameCap-t))
  have hh := subtract_affine (hU.add hV) ε (ε*t)
  convert hh using 1
  funext N
  simp only [Pi.add_apply]
  ring_nf

theorem concentrate [Fintype ι] [Nonempty ι]
    (R ε : ℝ) (p q P N : ι→ℝ) {s θ : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀i,0<p i) (hpq : ∀i,p i≤q i) (hqp : ∀i,q i≤2*p i)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hs : s∈Icc 0 frameCap) (hθ : θ∈Icc 0 frameCap)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,min (pure R ε p q i j s θ) (saturated R ε p q i j s θ)≤
      ∑k,block R ε p q k (P k) (N k) := by
  have hPt : (∑i,P i)≤frameCap := by linarith [hθ.1]
  have hNt : (∑i,N i)≤frameCap := by linarith [hs.1]
  obtain ⟨i,j,hij⟩ := both_signs_concentrate R p q P N
    hR hQ hp hpq hqp hP hN hPt hNt
  have hsum : (∑k,block R ε p q k (P k) (N k))=
      (∑k,mixedBlock R (p k) (q k) (P k) (N k))-ε*∑k,P k := by
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
      rw [pure,saturated,ite_eq_left horder,ite_eq_left rfl]
      rw [ite_eq_left rfl,heq] at hij
      have hc := (forward_same_concave (R:=R) (ε:=ε)
        (hp i).le ((hp i).trans_le (hpq i)).le ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-θ))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [add_zero,mixedBlock_zero_left,mul_zero,sub_zero,hlast] at hh
      refine hh.trans ?_
      linarith
    · rw [pure,saturated,ite_eq_left horder,ite_eq_right hsame]
      rw [ite_eq_right hsame,heq] at hij
      have hc := (forward_separated_concave (ε:=ε) hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-θ))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [U_zero,mul_zero,sub_zero,zero_add,add_zero,hlast] at hh
      dsimp only [positive]
      linarith
  · have ht : s-θ∈Icc 0 frameCap := ⟨by linarith,by linarith [hs.2,hθ.1]⟩
    have htotal : (∑i,N i)∈Icc 0 (frameCap-s) :=
      ⟨Finset.sum_nonneg (fun i _ => hN i),hNb⟩
    have hspan : 0≤frameCap-s := by linarith [hs.2]
    have heq : (∑i,P i)=(s-θ)+(∑i,N i) := by linarith
    have hlast : (s-θ)+(frameCap-s)=frameCap-θ := by ring
    by_cases hsame : i=j
    · subst j
      rw [pure,saturated,ite_eq_right horder,ite_eq_left rfl]
      rw [ite_eq_left rfl,heq] at hij
      rw [heq]
      have hc := (backward_same_concave (R:=R) (ε:=ε)
        (hp i).le ((hp i).trans_le (hpq i)).le ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hθ.1])) (convex_Icc 0 (frameCap-s))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [add_zero,mixedBlock_zero_right,hlast] at hh
      refine hh.trans ?_
      linarith
    · rw [pure,saturated,ite_eq_right horder,ite_eq_right hsame]
      rw [ite_eq_right hsame,heq] at hij
      rw [heq]
      have hc := (backward_separated_concave (ε:=ε) hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hθ.1])) (convex_Icc 0 (frameCap-s))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [V_zero,add_zero,hlast] at hh
      dsimp only [positive]
      linarith

end SquaresInCircles.Eight.ChargedOrdinaryConcentration
end
end
end
