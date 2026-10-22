module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroOppositePositiveStationaryData

/-!
# Both positive-source-coefficient stationary exclusions

Uncompiled transcription of equations (17)--(18). The two bounds concern
the original coupled source and target at angular stationarity. Row 4
first uses the sign of the angular curvature to obtain b < 1/5; all
subsequent estimates use that same b and its actual target circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Stationary
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open SecondWord (U W outer_domain outer_zero_mem U_positive UW_circle)

lemma source_slope_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    l 1 b<(10033/10000:ℝ) ∧ l 4 b<(213/200:ℝ) := by
  have hr := (SecondWord.outer_ratio_bounds hb).1
  norm_num [l,q,p]
  constructor <;> linarith

lemma fine_target_ratio {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (5223/20000:ℝ)<ratio B := by
  have hh := Positive.ratio_monotone outer_zero_mem hB hB.1
  rw [Same.Axial.zero_ratio] at hh
  exact Same.PositiveCoefficient.rho_bounds.1.trans_le hh

lemma target_sum_lower {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (2414575671/1000000000:ℝ)<U B+W B := by
  linarith [original_sum_lower hB,ShortOuterZero.fine_axial_bounds.1]

lemma reciprocal_lower {L U₀ M : ℝ} (hL : 0<L) (hU : L<U₀)
    (hM : 0≤M) (hcheck : M*U₀^2<1) : M<1/L^2 := by
  apply (lt_div_iff₀ (pow_pos hL 2)).2
  have hs := pow_le_pow_left₀ hL.le hU.le 2
  have hm := mul_le_mul_of_nonneg_left hs hM
  nlinarith

lemma row_one_mass {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (993/1000:ℝ)<mass 1 b := by
  have hi := reciprocal_lower (l_positive 1 hb) (source_slope_upper hb).1
    (by norm_num : (0:ℝ)≤993/1000) (by norm_num)
  dsimp [mass]
  linarith [sq_nonneg (z b)]

lemma fifth_mem : (1/5:ℝ)∈Icc 0 outerDiagonal :=
  ⟨by norm_num,by linarith [outer_endpoint_bounds.2.2.1]⟩

lemma fifth_references : (617/1000:ℝ)<ratioD (1/5) ∧ l 4 (1/5)<201/200 := by
  have hc := UW_circle (outer_domain fifth_mem)
  have hu := U_positive (outer_domain fifth_mem)
  have hU : (37/20:ℝ)<U (1/5) ∧ U (1/5)<1851/1000 := by
    norm_num [W,Q0] at hc
    constructor <;> nlinarith
  have hR : (189/500:ℝ)<ratio (1/5) := by
    change (189/500:ℝ)<((1/5:ℝ)+1/2)/U (1/5)
    apply (lt_div_iff₀ hu).2
    linarith [hU.2]
  have hD : (617/1000:ℝ)<ratioD (1/5) := by
    change (617/1000:ℝ)<Q0/(U (1/5))^3
    apply (lt_div_iff₀ (pow_pos hu 3)).2
    have hh := pow_le_pow_left₀ hu.le hU.2.le 3
    norm_num [Q0] at *
    nlinarith
  exact ⟨hD,by norm_num [l,p,q]; linarith⟩

/-- The sign condition in (16) excludes the entire source interval [1/5,d]. -/
lemma row_four_source {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (hG : 0≤G 4 b) : b<1/5 := by
  by_contra! hlarge
  have hR := Positive.ratio_monotone fifth_mem hb hlarge
  have hD := Positive.ratioD_monotone fifth_mem hb hlarge
  have hL : l 4 b<201/200 := by
    have hh : l 4 b≤l 4 (1/5) := by norm_num [l,p,q] at *; linarith
    exact hh.trans_lt fifth_references.2
  have hl := l_positive 4 hb
  have hlpow := pow_le_pow_left₀ hl.le hL.le 3
  have hdlo : (617/1000:ℝ)<ratioD b := fifth_references.1.trans_le hD
  have hquot : (3/10:ℝ)<p 4*ratioD b/(l 4 b)^3 := by
    apply (lt_div_iff₀ (pow_pos hl 3)).2
    norm_num [p]
    nlinarith
  dsimp [G,z] at hG
  linarith

lemma row_four_mass {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (hG : 0≤G 4 b) :
    (19433/20000:ℝ)<mass 4 b := by
  have hcut := row_four_source hb hG
  have hz : (3/10:ℝ)<z b := by dsimp [z]; linarith
  have hi := reciprocal_lower (l_positive 4 hb) (source_slope_upper hb).2
    (by norm_num : (0:ℝ)≤17633/20000) (by norm_num)
  dsimp [mass]
  nlinarith

lemma actual_U_one {B x : ℝ} (hd : PlusDomain B x) (hstat : plusAngle 1 B x=0) :
    (189/100:ℝ)<U B := by
  have hm := row_one_mass hd.2.2
  have he := actual_sum 1 hd hstat
  have hS : U B+W B≤(Q0+2-993/1000)/2 := by
    dsimp [sumCoordinate] at he
    linarith
  exact original_U_lower hd.1 hS (by linarith [target_sum_lower hd.1])
    (by norm_num [Q0])

lemma actual_U_four {B x : ℝ} (hd : PlusDomain B x) (hstat : plusAngle 4 B x=0)
    (hG : 0≤G 4 (plus B x)) : (9459/5000:ℝ)<U B := by
  have hm := row_four_mass hd.2.2 hG
  have he := actual_sum 4 hd hstat
  have hS : U B+W B≤(Q0+2-19433/20000)/2 := by
    dsimp [sumCoordinate] at he
    linarith
  exact original_U_lower hd.1 hS (by linarith [target_sum_lower hd.1])
    (by norm_num [Q0])

lemma fraction_upper (r : Row) {B x u₀ m₀ : ℝ} (hd : PlusDomain B x)
    (hu₀ : 0<u₀) (hm₀ : 0<m₀) (hu : u₀≤U B) (hm : m₀≤mass r (plus B x)) :
    (Q0-(U B+W B))/(U B*mass r (plus B x))≤
      (Q0-2414575671/1000000000)/(u₀*m₀) := by
  have hden := mul_le_mul hu hm hm₀.le (U_positive (outer_domain hd.1)).le
  have hpos := mul_pos (U_positive (outer_domain hd.1)) (mass_positive r hd.2.2)
  have hn : Q0-(U B+W B)≤Q0-2414575671/1000000000 := by
    linarith [target_sum_lower hd.1]
  exact (div_le_div_of_nonneg_right hn hpos.le).trans
    (div_le_div_of_nonneg_left (by norm_num [Q0]) (mul_pos hu₀ hm₀) hden)

lemma row_one_target_positive {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle 1 B x=0) (hG : 0≤G 1 (plus B x)) :
    (147/1000:ℝ)<plusTarget 1 B x := by
  have hl := target_lower 1 (Or.inl rfl) hd hstat hG
  have hf := fraction_upper 1 hd (by norm_num : (0:ℝ)<189/100)
    (by norm_num : (0:ℝ)<993/1000) (actual_U_one hd hstat).le (row_one_mass hd.2.2).le
  have he : (147/1000:ℝ)<t 1-
      (Q0-2414575671/1000000000)/((189/100)*(993/1000)) := by norm_num [t,Q0]
  norm_num [v] at hl
  linarith

lemma row_four_target_positive {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle 4 B x=0) (hG : 0≤G 4 (plus B x)) :
    (67/50000:ℝ)<plusTarget 4 B x := by
  have hl := target_lower 4 (Or.inr rfl) hd hstat hG
  have hf := fraction_upper 4 hd (by norm_num : (0:ℝ)<9459/5000)
    (by norm_num : (0:ℝ)<19433/20000) (actual_U_four hd hstat hG).le
    (row_four_mass hd.2.2 hG).le
  have hr := fine_target_ratio hd.1
  have he : (67/50000:ℝ)<t 4-v 4*(5223/20000)-
      (Q0-2414575671/1000000000)/((9459/5000)*(19433/20000)) := by norm_num [t,v,Q0]
  norm_num [t,v] at hl he
  linarith

/-- Both positive-p rows have a genuine descent at every angular stationary point. -/
theorem stationary_descent (r : Row) (hr : r=1 ∨ r=4) {B x : ℝ}
    (hd : PlusDomain B x) (hstat : plusAngle r B x=0) :
    angleSecond r B x<0 ∨ 0<plusTarget r B x := by
  by_cases hG : 0≤G r (plus B x)
  · right
    rcases hr with rfl | rfl
    · linarith [row_one_target_positive hd hstat hG]
    · linarith [row_four_target_positive hd hstat hG]
  · left
    rw [actual_second r hd hstat]
    exact mul_neg_of_pos_of_neg (l_positive r hd.2.2) (lt_of_not_ge hG)

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Stationary
