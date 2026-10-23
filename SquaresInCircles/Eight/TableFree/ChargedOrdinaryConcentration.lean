module

public import SquaresInCircles.Eight.TableFree.ChargedHybridConcentration

/-!
# Four ordinary blocks with both signed budgets and an affine charge

Uncompiled simplex and common-mass concentration. No distinguished
linear block is inserted: every original block retains its full norm.
The positive-mass charge is subtracted before either endpoint reduction.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ChargedOrdinaryConcentration
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

@[simp] theorem block_zero_left (R ε : ℝ) (p q : ι→ℝ) (i : ι) (N : ℝ) :
    block R ε p q i 0 N=V R (p i) (q i) N := by simp [block]
@[simp] theorem block_zero_right (R ε : ℝ) (p q : ι→ℝ) (i : ι) (P : ℝ) :
    block R ε p q i P 0=positive R ε p q i P := by simp [block,positive]
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
  simpa only [one_mul,add_comm t,mul_add,add_comm (ε*t),sub_add_eq_add_sub] using hh

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
  have hcharge := sub_le_sub_right hij (ε*∑i,P i)
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
      simp only [pure,if_pos horder,saturated,if_pos rfl]
      simp only [if_pos rfl,heq] at hcharge
      have hc := (forward_same_concave (R:=R) (ε:=ε)
        (hp i).le ((hp i).trans_le (hpq i)).le ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-θ))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [add_zero,mixedBlock_zero_left,mul_zero,sub_zero,hlast] at hh
      exact hh.trans hcharge
    · simp only [pure,if_pos horder,saturated,if_neg hsame]
      simp only [if_neg hsame,heq] at hcharge
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
      simp only [pure,if_neg horder,saturated,if_pos rfl]
      simp only [if_pos rfl,heq] at hcharge
      have hc := (backward_same_concave (R:=R) (ε:=ε)
        (hp i).le ((hp i).trans_le (hpq i)).le ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hθ.1])) (convex_Icc 0 (frameCap-s))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [add_zero,mixedBlock_zero_right,hlast] at hh
      exact hh.trans hcharge
    · simp only [pure,if_neg horder,saturated,if_neg hsame]
      simp only [if_neg hsame,heq] at hcharge
      have hc := (backward_separated_concave (ε:=ε) hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hθ.1])) (convex_Icc 0 (frameCap-s))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [V_zero,add_zero,hlast] at hh
      dsimp only [positive]
      linarith

end SquaresInCircles.Eight.TableFree.ChargedOrdinaryConcentration
