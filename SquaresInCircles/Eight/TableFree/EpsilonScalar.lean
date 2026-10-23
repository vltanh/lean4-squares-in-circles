module

public import SquaresInCircles.Eight.TableFree.EpsilonTangent

/-!
# Both epsilon-zero endpoint cap sums decrease with the original E tangent

Uncompiled draft.  The derivative is nonpositive whenever the D cap is
active.  Past its intrinsic clipping point only the decreasing H cap
remains.  This proves the full comparison with b=0, including a weak tie
at the diagonal cap, without assuming a stationary E tangent.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EpsilonScalar
open EpsilonCapCalculus EpsilonTangent

def raw (a t u b : ℝ) : ℝ := H t (1+b)+H u (g a b)
def value (a t u b : ℝ) : ℝ := H t (1+b)+H u (max (diagonalCoordinate qCap) (g a b))

theorem shifted_primary {b : ℝ} (hb : b∈Icc (0:ℝ) (31/200)) :
    1+b∈Icc (1/2 : ℝ) (231/200) := ⟨by linarith [hb.1],by linarith [hb.2]⟩

theorem g_primary {a b : ℝ} (ha : a∈Icc 0 (11/50 : ℝ))
    (hb : b∈Icc (0:ℝ) (31/200)) : g a b∈Icc (1/2 : ℝ) (231/200) := by
  have hh := g_bounds ha hb
  exact ⟨hh.1.le,by linarith [hh.2,hb.1]⟩

theorem raw_hasDerivAt {a t u b : ℝ}
    (ha : a∈Icc 0 (11/50 : ℝ)) (ht : t∈Icc 0 (11/50 : ℝ))
    (hu : u∈Icc 0 (11/50 : ℝ)) (hb : b∈Icc (0:ℝ) (31/200)) :
    HasDerivAt (raw a t u) (-K t (1+b)+K u (g a b)*decrease a b) b := by
  have hH := (H_x_hasDerivAt ht (shifted_primary hb)).comp b ((hasDerivAt_id b).const_add 1)
  have hD := (H_x_hasDerivAt hu (g_primary ha hb)).comp b (g_hasDerivAt hb)
  convert hH.add hD using 1
  · rfl
  · ring

theorem raw_derivative_nonpos {a t u b : ℝ}
    (ha : a∈Icc 0 (11/50 : ℝ)) (hb : b∈Icc (0:ℝ) (31/200))
    (hend : (t=0 ∧ u=a) ∨ (t=a ∧ u=0))
    (hactive : diagonalCoordinate qCap≤g a b) :
    -K t (1+b)+K u (g a b)*decrease a b≤0 := by
  have hK := active_K ha hb hactive
  have hdec := decrease_bounds ha hb
  rcases hend with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have hmono := K_monotone (show (0:ℝ)∈Icc 0 (11/50) by norm_num)
      (show (1:ℝ)∈Icc (1/2) (231/200) by norm_num) (shifted_primary hb) (by linarith [hb.1])
    have hmul := mul_le_mul_of_nonneg_left hdec.2 (K_pos ha (g_primary ha hb)).le
    nlinarith [hK.1]
  · have hmono := K_monotone ha (show (1:ℝ)∈Icc (1/2) (231/200) by norm_num)
      (shifted_primary hb) (by linarith [hb.1])
    have hmul := mul_le_mul_of_nonneg_left hdec.2
      (K_pos (show (0:ℝ)∈Icc 0 (11/50) by norm_num) (g_primary ha hb)).le
    nlinarith [hK.2]

theorem active_raw_nonincrease {a t u b : ℝ}
    (ha : a∈Icc 0 (11/50 : ℝ)) (hb : b∈Icc (0:ℝ) (31/200))
    (hend : (t=0 ∧ u=a) ∨ (t=a ∧ u=0))
    (hactive : diagonalCoordinate qCap≤g a b) : raw a t u b≤raw a t u 0 := by
  have ht : t∈Icc 0 (11/50 : ℝ) := by rcases hend with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> simp_all
  have hu : u∈Icc 0 (11/50 : ℝ) := by rcases hend with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp_all
  have hsub (z : ℝ) (hz : z∈Icc (0:ℝ) b) : z∈Icc (0:ℝ) (31/200) :=
    ⟨hz.1,hz.2.trans hb.2⟩
  have hm : AntitoneOn (raw a t u) (Icc (0:ℝ) b) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun z hz => (raw_hasDerivAt ha ht hu (hsub z hz)).continuousAt.continuousWithinAt
    · exact fun z hz => raw_hasDerivAt ha ht hu (hsub z (Ioo_subset_Icc_self hz))
    · intro z hz
      have hzg := g_antitone ha (hsub z (Ioo_subset_Icc_self hz)) hb hz.2.le
      exact raw_derivative_nonpos ha (hsub z (Ioo_subset_Icc_self hz)) hend (hactive.trans hzg)
  exact hm ⟨le_rfl,hb.1⟩ ⟨hb.1,le_rfl⟩ hb.1

theorem value_eq_raw {a t u b : ℝ} (hactive : diagonalCoordinate qCap≤g a b) :
    value a t u b=raw a t u b := by simp [value,raw,max_eq_right hactive]

theorem nonincrease {a t u b : ℝ}
    (ha : a∈Icc 0 (11/50 : ℝ)) (hb : b∈Icc (0:ℝ) (31/200))
    (hend : (t=0 ∧ u=a) ∨ (t=a ∧ u=0)) : value a t u b≤value a t u 0 := by
  have ht : t∈Icc 0 (11/50 : ℝ) := by rcases hend with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> simp_all
  have hb0 : (0:ℝ)∈Icc 0 (31/200) := by norm_num
  have hgb := g_antitone ha hb0 hb hb.1
  by_cases h0 : g a 0≤diagonalCoordinate qCap
  · have hbc := hgb.trans h0
    have hm := H_antitone ht (shifted_primary hb0) (shifted_primary hb) (by linarith [hb.1])
    simp only [value,max_eq_left hbc,max_eq_left h0,add_zero]
    simpa using add_le_add_right hm (H u (diagonalCoordinate qCap))
  · have h0a : diagonalCoordinate qCap≤g a 0 := (le_of_not_ge h0)
    by_cases hba : diagonalCoordinate qCap≤g a b
    · rw [value_eq_raw hba,value_eq_raw h0a]
      exact active_raw_nonincrease ha hb hend hba
    · have hbl : g a b<diagonalCoordinate qCap := lt_of_not_ge hba
      have hcont : ContinuousOn (fun z => -g a z) (Icc (0:ℝ) b) := fun z hz =>
        (g_hasDerivAt (show z∈Icc (0:ℝ) (31/200) from ⟨hz.1,hz.2.trans hb.2⟩)).neg.continuousAt.continuousWithinAt
      obtain ⟨z,hz,hzeq⟩ := intermediate_value_Icc hb.1 hcont
        (show -diagonalCoordinate qCap∈Icc (-g a 0) (-g a b) by constructor <;> linarith)
      have hz' : z∈Icc (0:ℝ) (31/200) := ⟨hz.1,hz.2.trans hb.2⟩
      have hzg : g a z=diagonalCoordinate qCap := by linarith
      have hzvalue : value a t u z≤value a t u 0 := by
        rw [value_eq_raw hzg.ge,value_eq_raw h0a]
        exact active_raw_nonincrease ha hz' hend hzg.ge
      have hH := H_antitone ht (shifted_primary hz') (shifted_primary hb) (by linarith [hz.2])
      have hvalue : value a t u b≤value a t u z := by
        simp only [value,max_eq_left hbl.le,hzg,max_self]
        exact add_le_add_right hH _
      exact hvalue.trans hzvalue

theorem diagonal_self : f (diagonalCoordinate qCap)=diagonalCoordinate qCap := by
  have hc : diagonalCoordinate qCap∈Icc (1/2 : ℝ) (231/200) := by
    constructor <;> linarith [EpsilonActiveRates.diagonal_bounds.1,EpsilonActiveRates.diagonal_bounds.2]
  have hr := R_sq hc
  have hp := R_pos hc
  have hs := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have hn := Real.sqrt_nonneg (qCap/2)
  dsimp [diagonalCoordinate] at hr ⊢
  dsimp [f]
  nlinarith

theorem f_one : f 1=EZeroFunctions.capped 0 := by
  have hc : diagonalCoordinate qCap∈Icc (1/2 : ℝ) (231/200) := by
    constructor <;> linarith [EpsilonActiveRates.diagonal_bounds.1,EpsilonActiveRates.diagonal_bounds.2]
  have hmono := f_antitone hc (show (1:ℝ)∈Icc (1/2) (231/200) by norm_num)
    (show diagonalCoordinate qCap≤1 by linarith [EpsilonActiveRates.diagonal_bounds.2])
  rw [diagonal_self] at hmono
  have hh : EZeroFunctions.h 0=f 1 := by
    norm_num [EZeroFunctions.h,EZeroFunctions.rho,EZeroFunctions.u,f,R]
  simp [EZeroFunctions.capped,hh,min_eq_right hmono]

theorem f_g_zero (a : ℝ) : f (g a 0)=EZeroFunctions.h a := by
  rw [g_zero]
  simp only [f,R,sub_add_cancel,EZeroFunctions.h,EZeroFunctions.rho]

theorem clipped_initial {a : ℝ} (ha : a∈Icc 0 (11/50 : ℝ)) :
    f (max (diagonalCoordinate qCap) (g a 0))=EZeroFunctions.capped a := by
  have hc : diagonalCoordinate qCap∈Icc (1/2 : ℝ) (231/200) := by
    constructor <;> linarith [EpsilonActiveRates.diagonal_bounds.1,EpsilonActiveRates.diagonal_bounds.2]
  have hg := g_primary ha (show (0:ℝ)∈Icc 0 (31/200) by norm_num)
  by_cases hcg : diagonalCoordinate qCap≤g a 0
  · have hm := f_antitone hc hg hcg
    rw [diagonal_self,f_g_zero] at hm
    simp [max_eq_right hcg,f_g_zero,EZeroFunctions.capped,min_eq_right hm]
  · have hgc : g a 0≤diagonalCoordinate qCap := le_of_not_ge hcg
    have hm := f_antitone hg hc hgc
    rw [diagonal_self,f_g_zero] at hm
    simp [max_eq_left hgc,diagonal_self,EZeroFunctions.capped,min_eq_left hm]

theorem initial_value {a t u : ℝ} (ha : a∈Icc 0 (11/50 : ℝ)) :
    value a t u 0=
      HardSplitCap.cap qCap (3/2-EZeroFunctions.capped 0) t+
        HardSplitCap.cap qCap (3/2-EZeroFunctions.capped a) u := by
  simp only [value,add_zero,cap_eq,f_one,clipped_initial ha]

theorem strict_bound {a t u b : ℝ}
    (ha : a∈Icc 0 (11/50 : ℝ)) (hb : b∈Icc (0:ℝ) (31/200))
    (hend : (t=0 ∧ u=a) ∨ (t=a ∧ u=0)) : value a t u b<2 := by
  apply (nonincrease ha hb hend).trans_lt
  rw [initial_value ha]
  rcases hend with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · simpa using EZeroCapEndpoints.first_endpoint (show (0:ℝ)≤0 by norm_num) ha.1
      (show (0:ℝ)+a≤7/10 by linarith [ha.2])
  · simpa using EZeroCapEndpoints.second_endpoint (show (0:ℝ)≤0 by norm_num) ha.1
      (show (0:ℝ)+a≤7/10 by linarith [ha.2])

end SquaresInCircles.Eight.TableFree.EpsilonScalar
