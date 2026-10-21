module

public import SquaresInCircles.Eight.TableFree.NegativeOrdinaryEnvelope
public import SquaresInCircles.Eight.TableFree.LowSecantTransfer

/-!
# Joint concentration of ordinary and modified one-angle blocks

Uncompiled source. The modified one-angle lower bound is linear in
positive mass and concave in negative mass. It therefore joins the
ordinary blocks in the same exact finite-simplex argument. The resulting
concentrations are analytic lower bounds on the original signed angles.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.FlatPrimaryConcentration
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open PositiveStressCoefficients NegativeEOneAngle

def F (modified : Bool) (p q s P N : ℝ) : ℝ :=
  if modified then -gamma s*P+V (Real.sqrt qCap) k 1 N
  else mixedBlock (Real.sqrt qCap) p q P N

def U' (modified : Bool) (p q s P : ℝ) : ℝ :=
  if modified then -gamma s*P else U (Real.sqrt qCap) p q P

def V' (modified : Bool) (p q N : ℝ) : ℝ :=
  if modified then V (Real.sqrt qCap) k 1 N else V (Real.sqrt qCap) p q N

@[simp] theorem F_zero (m : Bool) (p q s : ℝ) : F m p q s 0 0=0 := by cases m <;> simp [F]
@[simp] theorem F_zero_right (m : Bool) (p q s P : ℝ) : F m p q s P 0=U' m p q s P := by
  cases m <;> simp [F,U']
@[simp] theorem F_zero_left (m : Bool) (p q s N : ℝ) : F m p q s 0 N=V' m p q N := by
  cases m <;> simp [F,V']
@[simp] theorem U'_zero (m : Bool) (p q s : ℝ) : U' m p q s 0=0 := by cases m <;> simp [U']
@[simp] theorem V'_zero (m : Bool) (p q : ℝ) : V' m p q 0=0 := by cases m <;> simp [V']

theorem canonical_concave : ConcaveOn ℝ (Icc 0 frameCap) (V (Real.sqrt qCap) k 1) :=
  V_concave (Real.sqrt_nonneg _) (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
    (by norm_num [k]) (by norm_num [k]) (by norm_num [k])

theorem F_concave_P {m : Bool} {p q s N : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hN : N∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun P => F m p q s P N) := by
  cases m
  · exact mixedBlock_concave_positive (Real.sqrt_nonneg _)
      (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hp hpq hqp hN
  · exact NegativeOrdinaryEnvelope.affine_concave (-gamma s) (V (Real.sqrt qCap) k 1 N) 0 frameCap

theorem F_concave_N {m : Bool} {p q s P : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hP : P∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun N => F m p q s P N) := by
  cases m
  · exact mixedBlock_concave_negative (Real.sqrt_nonneg _)
      (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hp hpq hqp hP
  · exact canonical_concave.const_add (-gamma s*P)

theorem U'_concave {m : Bool} {p q s : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    ConcaveOn ℝ (Icc 0 frameCap) (U' m p q s) := by
  simpa only [F_zero_right] using F_concave_P (m := m) (s := s) hp hpq hqp
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])

theorem V'_concave {m : Bool} {p q : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    ConcaveOn ℝ (Icc 0 frameCap) (V' m p q) := by
  simpa only [F_zero_left] using F_concave_N (m := m) (s := 0) hp hpq hqp
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])

theorem negative_line_concave {m : Bool} {p q s z : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hz : z∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-z)) (fun P => F m p q s P (z+P)) := by
  cases m
  · exact sameBlockLine_concave hp.le (hp.trans_le hpq).le hz
  · have hv := concave_affine_argument canonical_concave
      (a := 1) (b := z) (l := 0) (u := frameCap-z)
      (fun x hx => ⟨by linarith [hz.1,hx.1],by linarith [hx.2]⟩)
    have hl := NegativeOrdinaryEnvelope.affine_concave (-gamma s) 0 0 (frameCap-z)
    convert hl.add hv using 1
    funext P
    simp [F,add_comm]

theorem concentrated_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → Bool) (p q : ι → ℝ) (s : ℝ) (i j : ι) (P N : ℝ) :
    (∑ a,F (m a) (p a) (q a) s (massAt i P a) (massAt j N a))=
      if i=j then F (m i) (p i) (q i) s P N
      else U' (m i) (p i) (q i) s P+V' (m j) (p j) (q j) N := by
  by_cases hij : i=j
  · subst j
    have he (a : ι) : F (m a) (p a) (q a) s (massAt i P a) (massAt i N a)=
        if a=i then F (m i) (p i) (q i) s P N else 0 := by
      by_cases hai : a=i
      · subst a; simp [massAt]
      · simp [massAt,hai]
    simp_rw [he]
    simp
  · have he (a : ι) : F (m a) (p a) (q a) s (massAt i P a) (massAt j N a)=
        (if a=i then U' (m i) (p i) (q i) s P else 0)+
        (if a=j then V' (m j) (p j) (q j) N else 0) := by
      by_cases hai : a=i
      · subst a; simp [massAt,hij]
      · by_cases haj : a=j
        · subst a; simp [massAt,hai]
        · simp [massAt,hai,haj]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp [hij]

theorem both_signs {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (m : ι → Bool) (p q P N : ι → ℝ) (s : ℝ)
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hqp : ∀ i,q i≤2*p i)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hPt : (∑ i,P i)≤frameCap) (hNt : (∑ i,N i)≤frameCap) :
    ∃ i j, (if i=j then F (m i) (p i) (q i) s (∑ a,P a) (∑ a,N a)
      else U' (m i) (p i) (q i) s (∑ a,P a)+V' (m j) (p j) (q j) (∑ a,N a))≤
        ∑ a,F (m a) (p a) (q a) s (P a) (N a) := by
  have hPi (i : ι) : P i∈Icc 0 frameCap :=
    ⟨hP i,(Finset.single_le_sum (fun a _ => hP a) (Finset.mem_univ i)).trans hPt⟩
  obtain ⟨j,hj⟩ := concave_sum_concentrates
    (fun i n => F (m i) (p i) (q i) s (P i) n) N hN rfl hNt
    (fun i => F_concave_N (hp i) (hpq i) (hqp i) (hPi i))
  have hNT : (∑ a,N a)∈Icc 0 frameCap := ⟨Finset.sum_nonneg (fun a _ => hN a),hNt⟩
  obtain ⟨i,hi⟩ := concave_sum_concentrates
    (fun a p' => F (m a) (p a) (q a) s p' (massAt j (∑ b,N b) a)) P hP rfl hPt
    (fun a => F_concave_P (hp a) (hpq a) (hqp a) (massAt_mem hNT))
  refine ⟨i,j,?_⟩
  rw [concentrated_sum] at hi
  exact hi.trans hj

theorem negative_endpoints {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (m : ι → Bool) (p q P N : ι → ℝ) {d s : ℝ}
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hqp : ∀ i,q i≤2*p i)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hd : d∈Icc 0 frameCap) (hs : s∈Icc 0 d)
    (hbudget : (∑ i,P i)≤frameCap-d)
    (hbalance : (∑ i,N i)=d-s+∑ i,P i) :
    ∃ i j, min (V' (m j) (p j) (q j) (d-s))
      (if i=j then F (m i) (p i) (q i) s (frameCap-d) (frameCap-s)
       else U' (m i) (p i) (q i) s (frameCap-d)+V' (m j) (p j) (q j) (frameCap-s))≤
        ∑ a,F (m a) (p a) (q a) s (P a) (N a) := by
  have hz : d-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hd.2,hs.1]⟩
  obtain ⟨i,j,hij⟩ := both_signs m p q P N s hp hpq hqp hP hN
    (by linarith [hd.1]) (by rw [hbalance]; linarith [hs.1])
  have htotal : (∑ a,P a)∈Icc 0 (frameCap-d) :=
    ⟨Finset.sum_nonneg (fun a _ => hP a),hbudget⟩
  have hspan : 0≤frameCap-d := by linarith [hd.2]
  have hsub : Icc (0:ℝ) (frameCap-d)⊆Icc 0 (frameCap-(d-s)) :=
    Icc_subset_Icc le_rfl (by linarith [hs.1])
  refine ⟨i,j,?_⟩
  by_cases he : i=j
  · subst j
    simp only [if_pos rfl] at hij ⊢
    rw [hbalance] at hij
    have hc := (negative_line_concave (m := m i) (s := s)
      (hp i) (hpq i) (hqp i) hz).subset hsub (convex_Icc 0 (frameCap-d))
    have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
    rw [add_zero,F_zero_left,show d-s+(frameCap-d)=frameCap-s by ring] at hh
    exact hh.trans hij
  · simp only [if_neg he] at hij ⊢
    rw [hbalance] at hij
    have hU := (U'_concave (m := m i) (s := s) (hp i) (hpq i) (hqp i)).subset
      (Icc_subset_Icc le_rfl (by linarith [hd.1])) (convex_Icc 0 (frameCap-d))
    have hV := concave_affine_argument
      (V'_concave (m := m j) (hp j) (hpq j) (hqp j))
      (a := 1) (b := d-s) (l := 0) (u := frameCap-d)
      (fun x hx => ⟨by linarith [hz.1,hx.1],by linarith [hs.1,hx.2]⟩)
    have hh := (hU.add hV).min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
    simp only [one_mul,U'_zero,zero_add,add_zero,
      show frameCap-d+(d-s)=frameCap-s by ring] at hh
    exact hh.trans (by convert hij using 1 <;> congr 1 <;> ring)

end SquaresInCircles.Eight.TableFree.FlatPrimaryConcentration
