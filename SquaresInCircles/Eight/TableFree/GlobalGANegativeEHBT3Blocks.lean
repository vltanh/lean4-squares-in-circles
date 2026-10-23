module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3Endpoints
public import SquaresInCircles.Eight.TableFree.ChargedOrdinaryConcentration
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3Balanced
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2FarHigh

/-!
# Original four-block coefficients for the EH1/BT3 scalar reductions

Uncompiled Sections 3, 5 and 7. The fourth block is ordinary and retains
both original arguments. The small-high coefficients are exactly the
already proved nonnegative-total family at e=0. Far-high coefficients
are the original far-EH family with the unrotated and tilted D weights
kept in their correct roles.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Blocks
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

abbrev p (f : Family) (θ z : ℝ) : Fin 4→ℝ :=
  PositiveBT3.pWeights (Explicit.k f θ) (Explicit.l f θ) (Explicit.m f θ) (Explicit.c f θ z)
abbrev q (f : Family) (θ z : ℝ) : Fin 4→ℝ :=
  PositiveBT3.qWeights (Explicit.k f θ) (Explicit.l f θ) (Explicit.m f θ) (Explicit.c f θ z)
def positive (f : Family) (θ z P : ℝ) (i : Fin 4) : ℝ :=
  ChargedOrdinaryConcentration.positive R (epsilon f) (p f θ z) (q f θ z) i P
def negative (f : Family) (θ z N : ℝ) (i : Fin 4) : ℝ := V R (p f θ z i) (q f θ z i) N
def block (f : Family) (θ z P N : ℝ) (i : Fin 4) : ℝ :=
  ChargedOrdinaryConcentration.block R (epsilon f) (p f θ z) (q f θ z) i P N
def pure (f : Family) (θ z s : ℝ) (i j : Fin 4) : ℝ :=
  ChargedOrdinaryConcentration.pure R (epsilon f) (p f θ z) (q f θ z) i j s θ
def saturated (f : Family) (θ z s : ℝ) (i j : Fin 4) : ℝ :=
  ChargedOrdinaryConcentration.saturated R (epsilon f) (p f θ z) (q f θ z) i j s θ

def ordinaryP (f : Family) (θ : ℝ) : Fin 3→ℝ :=
  ![Explicit.k f θ,Explicit.k f θ,min (Explicit.l f θ) (Explicit.m f θ)]
def ordinaryQ (f : Family) (θ : ℝ) : Fin 3→ℝ :=
  ![1,Explicit.l f θ,max (Explicit.l f θ) (Explicit.m f θ)]
def ordinaryV (f : Family) (θ : ℝ) (i : Fin 3) (t : ℝ) : ℝ :=
  V R (ordinaryP f θ i) (ordinaryQ f θ i) t

@[simp] lemma negative_ordinary (f : Family) (θ z t : ℝ) (i : Fin 3) :
    negative f θ z t i.castSucc=ordinaryV f θ i t := by fin_cases i <;> rfl

lemma small_high_domain {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    NonnegativeTotals.Explicit.Domain .triangle (θ-1/6) 0 := by
  dsimp [NonnegativeTotals.Explicit.Domain]
  exact ⟨by linarith [hθ.1],le_rfl,by linarith [hθ.2]⟩

lemma small_high_pairs {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (i : Fin 4) :
    0<p .smallHigh θ z i ∧ p .smallHigh θ z i≤q .smallHigh θ z i ∧
      (2/3)*q .smallHigh θ z i≤p .smallHigh θ z i := by
  have hh := PositiveBT3.Balanced.pair_domain .triangle (small_high_domain hθ)
    (show z∈Icc 0 (NonnegativeTotals.Explicit.theta .triangle (θ-1/6) 0) by
      simpa [NonnegativeTotals.Explicit.theta] using hz) i
  have heP : PositiveBT3.pWeights (NonnegativeTotals.Explicit.k .triangle (θ-1/6) 0)
      (NonnegativeTotals.Explicit.l .triangle (θ-1/6) 0)
      (NonnegativeTotals.Explicit.c .triangle (θ-1/6) 0)
      (NonnegativeTotals.Explicit.tilted .triangle (θ-1/6) 0 z) i=p .smallHigh θ z i := by
    simp [p,Explicit.k,Explicit.l,Explicit.m,Explicit.c,L,
      NonnegativeTotals.Explicit.k,NonnegativeTotals.Explicit.l,NonnegativeTotals.Explicit.c,
      NonnegativeTotals.Explicit.tilted,NonnegativeTotals.Explicit.tilt,PositiveBT3.tilted]
  have heQ : PositiveBT3.qWeights (NonnegativeTotals.Explicit.k .triangle (θ-1/6) 0)
      (NonnegativeTotals.Explicit.l .triangle (θ-1/6) 0)
      (NonnegativeTotals.Explicit.c .triangle (θ-1/6) 0)
      (NonnegativeTotals.Explicit.tilted .triangle (θ-1/6) 0 z) i=q .smallHigh θ z i := by
    simp [q,Explicit.k,Explicit.l,Explicit.m,Explicit.c,L,
      NonnegativeTotals.Explicit.k,NonnegativeTotals.Explicit.l,NonnegativeTotals.Explicit.c,
      NonnegativeTotals.Explicit.tilted,NonnegativeTotals.Explicit.tilt,PositiveBT3.tilted]
  rw [heP,heQ] at hh
  exact ⟨hh.1,hh.2.1,by linarith [hh.2.2]⟩

lemma small_high_scale {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (i : Fin 4) :
    min 1 (Explicit.l .smallHigh θ)≤q .smallHigh θ z i ∧
      q .smallHigh θ z i≤(6/5)*min 1 (Explicit.l .smallHigh θ) := by
  have hh := PositiveBT3.Balanced.scale_bounds .triangle (small_high_domain hθ)
    (show z∈Icc 0 (NonnegativeTotals.Explicit.theta .triangle (θ-1/6) 0) by
      simpa [NonnegativeTotals.Explicit.theta] using hz) i
  simpa [q,Explicit.k,Explicit.l,Explicit.m,Explicit.c,L,
    NonnegativeTotals.Explicit.k,NonnegativeTotals.Explicit.l,NonnegativeTotals.Explicit.c,
    NonnegativeTotals.Explicit.tilted,NonnegativeTotals.Explicit.tilt,PositiveBT3.tilted] using hh

lemma far_high_pairs {θ z : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (i : Fin 4) :
    (3/5:ℝ)≤p .farHigh θ z i ∧ p .farHigh θ z i≤q .farHigh θ z i ∧
      q .farHigh θ z i≤(5/3)*p .farHigh θ z i ∧ q .farHigh θ z i≤1 := by
  have h0 : (0:ℝ)∈Icc 0 θ := ⟨le_rfl,by linarith [hθ.1]⟩
  have hp := NegativeEHPositiveTD.Explicit.far_pairs .high hθ h0
  have hq := NegativeEHPositiveTD.Explicit.far_high_q_le_one hθ h0
  have hr := NegativeEHPositiveTD.Explicit.far_high_ranges hθ
  have hc := NegativeEHPositiveTD.Explicit.far_high_tilted hθ hz
  have hck : Explicit.k .farHigh θ<Explicit.c .farHigh θ z := by
    simpa [Explicit.k,Explicit.c,Explicit.m,PositiveBT3.tilted,
      NegativeEHPositiveTD.Explicit.k,NegativeEHPositiveTD.Explicit.m,
      NegativeEHPositiveTD.Explicit.c,NegativeEHPositiveTD.Explicit.eta,
      NegativeDEPositiveTD.Explicit.eta,PositiveTD.eta] using (lt_min_iff.mp hc.2.2.1).2
  have hc1 : Explicit.c .farHigh θ z<1 := by
    simpa [Explicit.c,Explicit.m,PositiveBT3.tilted,NegativeEHPositiveTD.Explicit.m,
      NegativeEHPositiveTD.Explicit.c,NegativeEHPositiveTD.Explicit.eta,
      NegativeDEPositiveTD.Explicit.eta,PositiveTD.eta] using (max_lt_iff.mp hc.2.2.2.1).2
  have hkn : (121/200:ℝ)≤Explicit.k .farHigh θ := hr.1.1
  fin_cases i
  · exact ⟨(hp 0).1,(hp 0).2.1,(hp 0).2.2,hq 0⟩
  · exact ⟨(hp 1).1,(hp 1).2.1,(hp 1).2.2,hq 1⟩
  · simpa [p,q,PositiveBT3.pWeights,PositiveBT3.qWeights,Explicit.k,Explicit.l,Explicit.m,
      NegativeEHPositiveTD.Explicit.p,NegativeEHPositiveTD.Explicit.q,
      NegativeEHPositiveTD.Explicit.k,NegativeEHPositiveTD.Explicit.l,
      NegativeEHPositiveTD.Explicit.m,NegativeEHPositiveTD.Explicit.c] using
      (show _ from ⟨(hp 2).1,(hp 2).2.1,(hp 2).2.2,hq 2⟩)
  · simp only [p,q,PositiveBT3.pWeights,PositiveBT3.qWeights,
      Matrix.cons_val_succ,Matrix.cons_val_zero,min_eq_right hc1.le,max_eq_left hc1.le]
    exact ⟨by linarith,hc1.le,by linarith,le_rfl⟩

lemma concentrate (f : Family) {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hpair : ∀i,0<p f θ z i ∧ p f θ z i≤q f θ z i ∧ q f θ z i≤2*p f θ z i)
    (hθ : θ∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,min (pure f θ z s i j) (saturated f θ z s i j)≤∑k,block f θ z (P k) (N k) k := by
  exact ChargedOrdinaryConcentration.concentrate R (epsilon f) (p f θ z) (q f θ z) P N
    (Real.sqrt_nonneg qCap) radius_sq.le (fun i => (hpair i).1)
    (fun i => (hpair i).2.1) (fun i => (hpair i).2.2) hP hN hs hθ hPb hNb hbalance

/-- The D-negative comparison only requires a positive k, not a high-family
lower cutoff. It therefore also applies to the actual far-EH coefficients. -/
lemma D_redundant {k c t : ℝ} (hk : k∈Ioc (0:ℝ) 1)
    (hkc : k≤c) (hc : c≤6/5) (ht : t∈Icc 0 frameCap) :
    V R k 1 t≤V R (min 1 c) (max 1 c) t := by
  by_cases hc1 : c≤1
  · rw [min_eq_right hc1,max_eq_left hc1]
    exact PositiveTD.V_first_coefficient (by norm_num) hk.1 hkc (by linarith) ht
  · have hc1' : 1≤c := (lt_of_not_ge hc1).le
    rw [min_eq_left hc1',max_eq_right hc1']
    have hh := PositiveTD.V_first_coefficient (by norm_num : (0:ℝ)<1)
      hk.1 hk.2 (by norm_num : (1:ℝ)≤2) ht
    exact hh.trans (PositiveATD0.balanced_second_coefficient
      (by norm_num) le_rfl hc1' (by linarith) ht)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Blocks
