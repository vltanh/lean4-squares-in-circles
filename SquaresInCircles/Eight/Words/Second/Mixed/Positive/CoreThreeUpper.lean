module

public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeSupport
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreTwoLower
public import SquaresInCircles.Eight.Words.Second.Mixed.Primary.SupportThird
public import SquaresInCircles.Eight.Words.Second.Mixed.Primary.ZeroCurve
public import SquaresInCircles.Eight.Words.Second.Mixed.TSmallEnvelope

/-!
# Eight squares: all upper owners from the original aligned relaxation

The relaxed aligned bound holds on the entire outer arc. The exact
finite displacement bounds of the two feasible owners therefore pay
their target-coordinate losses on the complete closed upper half.
-/

section
/-!
## The three complete transverse support intervals

The early multiplier is larger than the label coefficient. Two global
tangents and the sharper initial-arc line then give unsquared circle
supports, each strictly concave on its entire angle interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle)
open MixedTransverseSupport

def early (φ : ℝ) : ℝ := lower (26/25) (779/1000) (-c-13/250) φ
def middle (φ : ℝ) : ℝ := lower g (701151/1000000) (-c-37853/500000) φ
def late (φ : ℝ) : ℝ := lower g (31/50) (-c-1109/10000) φ

private lemma reference_lower {G p C φ sl cl n : ℝ}
    (hG : 0<G) (hp : 0≤p) (hpg : p≤(4/5)*G)
    (hs : sl≤Real.sin φ) (hc : cl≤Real.cos φ) (hn : 0<n)
    (hsq : G^2+p^2-2*G*p*cl<n^2)
    (hscore : γ<φ+C+(G+p)/2+G*sl-(1979/1000)*n) :
    γ<lower G p C φ := by
  have he := lower_sq hG hp hpg φ
  have hNp : 0<lowerN G p φ := CircularNorm.norm_pos (lower_domain hG hp hpg φ)
  have hcos := mul_le_mul_of_nonneg_left hc (by positivity : 0≤2*G*p)
  have hN : lowerN G p φ<n := by nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 hn)
  have hsin := mul_le_mul_of_nonneg_left hs hG.le
  dsimp [lower]
  linarith

private lemma interval_lower {G p C l u φ : ℝ}
    (hG : 0<G) (hp : 0≤p) (hpg : p≤(4/5)*G)
    (hdom : Icc l u⊆Icc lowerAngle (Real.pi/2))
    (hl : γ<lower G p C l) (hu : γ<lower G p C u) (hφ : φ∈Icc l u) :
    γ<lower G p C φ := by
  have hh : ConcaveOn ℝ (Icc l u) (lower G p C) :=
    concave_of_deriv2 (fun x _ => lower_hasDerivAt hG hp hpg C x)
      (fun x _ => lowerD_hasDerivAt hG hp hpg x)
      (fun x hx => (lower_curvature hG hp hpg (hdom hx)).le)
  exact concave_gt_of_endpoints hh hφ hl hu

lemma one_trig : (8414709/10000000:ℝ)≤Real.sin 1 ∧ (5403023/10000000:ℝ)≤Real.cos 1 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (1:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (1:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hc
  exact ⟨by linarith,by linarith⟩

lemma transition_trig :
    (1178111/1250000:ℝ)≤Real.sin (123/100) ∧ (3342377/10000000:ℝ)≤Real.cos (123/100) := by
  have hs := HighOrderTaylor.S15_le_sin (x := (123/100:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (123/100:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hc
  exact ⟨by linarith,by linarith⟩

lemma early_left : γ<early 1 :=
  reference_lower (n := (450827/500000:ℝ)) (by norm_num) (by norm_num) (by norm_num)
    one_trig.1 one_trig.2 (by norm_num) (by norm_num) (by norm_num [γ,c])

lemma early_right : γ<early (123/100) :=
  reference_lower (n := (26773/25000:ℝ)) (by norm_num) (by norm_num) (by norm_num)
    transition_trig.1 transition_trig.2 (by norm_num) (by norm_num) (by norm_num [γ,c])

lemma middle_left : γ< middle (123/100) :=
  reference_lower (n := (972847/1000000:ℝ)) (by norm_num [g]) (by norm_num) (by norm_num [g])
    transition_trig.1 transition_trig.2 (by norm_num) (by norm_num [g]) (by norm_num [g,γ,c])

lemma middle_right : γ< middle (7/5) :=
  reference_lower (n := (134912/125000:ℝ)) (by norm_num [g]) (by norm_num) (by norm_num [g])
    PrimaryZero.terminal_trig.1 PrimaryZero.terminal_trig.2.2.1 (by norm_num)
    (by norm_num [g]) (by norm_num [g,γ,c])

lemma late_left : γ<late (7/5) :=
  reference_lower (n := (1041071/1000000:ℝ)) (by norm_num [g]) (by norm_num) (by norm_num [g])
    PrimaryZero.terminal_trig.1 PrimaryZero.terminal_trig.2.2.1 (by norm_num)
    (by norm_num [g]) (by norm_num [g,γ,c])

lemma late_aligned : (9/10:ℝ)<late (Real.pi/2) := by
  have he := lower_sq (g := g) (p := (31/50:ℝ))
    (by norm_num [g]) (by norm_num) (by norm_num [g]) (Real.pi/2)
  have hp : 0<lowerN g (31/50) (Real.pi/2) := CircularNorm.norm_pos
    (lower_domain (by norm_num [g]) (by norm_num) (by norm_num [g]) (Real.pi/2))
  simp only [late,lower,Real.sin_pi_div_two]
  generalize lowerN g (31/50) (Real.pi/2) = n at he hp ⊢
  rw [Real.cos_pi_div_two] at he
  norm_num [g] at he
  have hN : n<(566501/500000:ℝ) := by nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<566501/500000))
  dsimp [g,c]
  linarith [pi_hand_enclosure.1]

theorem early_lower {φ : ℝ} (hφ : φ∈Icc (1:ℝ) (123/100)) : γ<early φ :=
  interval_lower (by norm_num) (by norm_num) (by norm_num)
    (fun x hx => ⟨by dsimp [lowerAngle]; linarith [hx.1,pi_hand_enclosure.2],
      by linarith [hx.2,pi_hand_enclosure.1]⟩) early_left early_right hφ

theorem middle_lower {φ : ℝ} (hφ : φ∈Icc (123/100:ℝ) (7/5)) : γ< middle φ :=
  interval_lower (by norm_num [g]) (by norm_num) (by norm_num [g])
    (fun x hx => ⟨by dsimp [lowerAngle]; linarith [hx.1,pi_hand_enclosure.2],
      by linarith [hx.2,pi_hand_enclosure.1]⟩) middle_left middle_right hφ

theorem late_lower {φ : ℝ} (hφ : φ∈Icc (7/5:ℝ) (Real.pi/2)) : γ<late φ :=
  interval_lower (by norm_num [g]) (by norm_num) (by norm_num [g])
    (fun x hx => ⟨by dsimp [lowerAngle]; linarith [hx.1,pi_hand_enclosure.2],hx.2⟩)
    late_left ((show γ<9/10 by norm_num [γ]).trans late_aligned) hφ

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
end
end
end

section
/-!
## The entire late primary support and aligned relaxation

The primary support is strictly concave on the whole short angle arc,
so its two exact endpoint bounds suffice. The aligned relaxed cost is
bounded for every original outer point, including primary coordinates
below one.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open MixedPrimarySupport

def p : ℝ := 31/50
def k : ℝ := 1109/10000
def K : ℝ := Real.pi/2-c-k+(g+p)/2-γ

lemma K_bounds : (1296701326/1000000000:ℝ)<K ∧ K<(1296701327/1000000000:ℝ) := by
  dsimp [K,c,k,g,p,γ]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]

lemma radius_fine : CommonQuarter.radius<(494697/250000:ℝ) := by
  have hh := radius_sq
  norm_num [Q0] at hh
  nlinarith [radius_bounds.1]

lemma primary_zero : 0< minus g p K 0 := by
  have he := N_sq (g := g) (p := p) (x := (0:ℝ)) (by norm_num [g])
  have hp := N_positive (g := g) (p := p) (x := (0:ℝ)) (by norm_num [g])
  simp only [minus,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero,sub_zero]
  generalize N g p 0 = n at he hp ⊢
  norm_num [g,p] at he ⊢
  have hN : n<(566501/500000:ℝ) := by nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
    (mul_lt_mul_of_pos_right radius_fine (by norm_num : (0:ℝ)<566501/500000))
  linarith [K_bounds.1]

lemma primary_right : 0< minus g p K (171/1000) := by
  have ht := PointProducts.trig (show (0:ℝ)≤171/1000 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  have hs : (170167/1000000:ℝ)<Real.sin (171/1000) := by linarith [ht.1.1]
  have hc : (492707/500000:ℝ)<Real.cos (171/1000) := by linarith [ht.2.1]
  have hcu : Real.cos (171/1000)<(123177/125000:ℝ) := by linarith [ht.2.2]
  have he := N_sq (g := g) (p := p) (x := (171/1000:ℝ)) (by norm_num [g])
  have hp := N_positive (g := g) (p := p) (x := (171/1000:ℝ)) (by norm_num [g])
  have hcos2 : (Real.cos (171/1000))^2<(123177/125000:ℝ)^2 := by nlinarith
  have hKC := mul_le_mul
    (show (1296701326/1000000000:ℝ)-171/1000≤K-171/1000 by linarith [K_bounds.1]) hc.le
    (by norm_num : (0:ℝ)≤492707/500000) (by linarith [K_bounds.1] : 0≤K-171/1000)
  simp only [minus]
  generalize N g p (171/1000) = n at he hp ⊢
  have hN : n<(14101/12500:ℝ) := by
    norm_num [g,p] at he
    nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
    (mul_lt_mul_of_pos_right radius_fine (by norm_num : (0:ℝ)<14101/12500))
  have hsp := mul_le_mul_of_nonneg_left hs.le (show 0≤g*(13/12) by norm_num [g])
  norm_num [g] at hsp ⊢
  linarith

lemma primary_curvature {x : ℝ} (hx : x∈Icc (0:ℝ) (171/1000)) : minusDD g p K x<0 := by
  have ht := positive_trig (show x∈Icc (0:ℝ) (7/10) from ⟨hx.1,by linarith [hx.2]⟩)
  have hs : Real.sin x≤(171/1000:ℝ) := ht.2.2.2.2.1.trans hx.2
  have hs2 := pow_le_pow_left₀ ht.2.2.1 hs 2
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hc : (1-(171/1000:ℝ)^2/2)≤Real.cos x := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hKC := mul_le_mul
    (show (12967/10000:ℝ)-171/1000≤K-x by linarith [K_bounds.1,hx.2]) hc
    (by norm_num : (0:ℝ)≤1-(171/1000:ℝ)^2/2) (by linarith [K_bounds.1,hx.2] : 0≤K-x)
  have hn := negative_curvature_upper (g := g) (p := p) (x := x) (by norm_num [g])
  have hnorm : -NDD g p x≤p^2/g+p^4*(171/1000)^2/g^3 := by
    norm_num [g,p] at hn ⊢
    nlinarith
  have hpaid := (mul_le_mul_of_nonneg_left hnorm (by linarith [radius_bounds.1] : 0≤CommonQuarter.radius)).trans_lt
    (mul_lt_mul_of_pos_right radius_fine (by norm_num [g,p] : 0<p^2/g+p^4*(171/1000)^2/g^3))
  have hsp := mul_le_mul_of_nonneg_left hs (show 0≤2-13*g/12 by norm_num [g])
  dsimp [minusDD,g,p] at *
  nlinarith

theorem primary_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (171/1000)) : 0< minus g p K x := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (171/1000)) (minus g p K) :=
    concave_of_deriv2 (fun _ _ => minus_hasDerivAt (by norm_num [g]))
      (fun _ _ => minusD_hasDerivAt (by norm_num [g]))
      (fun _ hx => (primary_curvature hx).le)
  exact concave_gt_of_endpoints hc hx primary_zero primary_right

lemma aligned_initial {b : ℝ} (hb : b∈Icc (0:ℝ) (7/10)) : (9/10:ℝ)<aligned b := by
  have hs := ShortOuterOne.SameContact.arc_state
    (show b∈Icc 0 outerDiagonal from ⟨hb.1,hb.2.trans MixedTSmall.seven_mem.2⟩)
  have hT := MixedTSmall.upper hb
  dsimp [MixedTSmall.k,MixedTEnvelope.k,MixedTSmall.q] at hT
  have hc := outer_circle_lower (X := -g) (Y := -(31/50)) hs
  have he : Real.sqrt ((-g)^2+(-(31/50:ℝ))^2)=MixedTransverseSupport.lowerN g (31/50) (Real.pi/2) := by
    simp [MixedTransverseSupport.lowerN,CircularNorm.norm,CircularNorm.energy]
  rw [he] at hc
  have hh := late_aligned
  simp only [late,MixedTransverseSupport.lower,Real.sin_pi_div_two,mul_one] at hh
  dsimp [aligned]
  linarith

theorem aligned_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : (9/10:ℝ)<aligned b := by
  by_cases he : b≤7/10
  · exact aligned_initial ⟨hb.1,he⟩
  · have hm := aligned_monotone
      (show (7/10:ℝ)∈Icc (7/10:ℝ) outerDiagonal from ⟨le_rfl,MixedTSmall.seven_mem.2⟩)
      (show b∈Icc (7/10:ℝ) outerDiagonal from ⟨by linarith,hb.2⟩) (by linarith)
    exact (aligned_initial (show (7/10:ℝ)∈Icc (0:ℝ) (7/10) by norm_num)).trans_le hm

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
end
end
end

section
/-!
## Complete upper owners by finite original-coordinate comparison

The secondary and primary separators permit at most .4*x and .53*x
of displacement from alignment.  The already proved P-label bounds
pay these losses on the entire upper half, including zero coordinates
and the aligned endpoint.  Both core pieces remain in the domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic

lemma upper_primary_displacement {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x-B*Real.cos x) :
    B≤a-1+(53/100)*x := by
  have htr := positive_trig hx
  have hcos : 0<Real.cos x := by linarith [htr.1]
  have hA := mul_le_mul_of_nonneg_right (CoreAngleEndpoint.state_bounds ht).2.1 htr.2.2.1
  have hz : 0≤1-Real.cos x := by linarith [htr.2.1]
  have haxial := mul_le_mul_of_nonneg_right
    (show a-1/2≤183/200 by linarith [(NegativeTwo.primary_mem hs).2,outer_endpoint_bounds.2.1]) hz
  have hprod := mul_nonneg hx.1 (show 0≤7/10-x by linarith [hx.2])
  have hzbound : 1-Real.cos x≤(7/20)*x := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hzpaid := mul_le_mul_of_nonneg_left hzbound (by norm_num : (0:ℝ)≤183/200)
  have hspaid := mul_le_mul_of_nonneg_left htr.2.2.2.2.1 (by norm_num : (0:ℝ)≤1/12)
  have hcpay := mul_le_mul_of_nonneg_left htr.1.le
    (mul_nonneg (by norm_num : (0:ℝ)≤53/100) hx.1)
  apply (mul_le_mul_iff_left₀ hcos).mp
  linarith

theorem upper_secondary {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a*Real.cos x+b*Real.sin x-B) :
    γ<value b B (Real.pi/2+x) := by
  have hcut : B≤OppositeTwo.upperCut a b x := by
    dsimp [OppositeTwo.upperCut]
    nlinarith
  have hdisp := OppositeTwo.upper_secondary_displacement hs hx
  have hh := upper_displacement_cost hs (CoreAngleEndpoint.state_bounds ht).2.2.1 hx.1
    (k := (2/5:ℝ)) (by norm_num) (by norm_num) (by linarith)
  dsimp [γ]
  linarith

theorem upper_primary {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x-B*Real.cos x) :
    γ<value b B (Real.pi/2+x) := by
  have hh := upper_displacement_cost hs (CoreAngleEndpoint.state_bounds ht).2.2.1 hx.1
    (k := (53/100:ℝ)) (by norm_num) le_rfl (upper_primary_displacement hs ht hx hsep)
  dsimp [γ]
  linarith

theorem upper_second {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a*Real.sin x-b*Real.cos x+A) :
    γ<value b B (Real.pi/2+x) := by
  have htr := positive_trig hx
  have hA := (CoreAngleEndpoint.state_bounds ht).2.1
  have ha : a<(283/200:ℝ) := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
  have has := mul_le_mul_of_nonneg_right ha.le htr.2.2.1
  have hbc := mul_nonneg hs.1 (by linarith [htr.1] : 0≤Real.cos x)
  have hxlo : (2/5:ℝ)<x := by
    by_contra hn
    have hsin : Real.sin x≤(2/5:ℝ) := htr.2.2.2.2.1.trans (le_of_not_gt hn)
    have hs2 := pow_le_pow_left₀ htr.2.2.1 hsin 2
    have hcos : (229/250:ℝ)<Real.cos x := by
      nlinarith [Real.sin_sq_add_cos_sq x,htr.1]
    nlinarith
  have hb : b<(2/5:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left htr.1.le hs.1
    nlinarith [htr.2.2.2.1]
  have hB : B<(559/1000:ℝ) :=
    (CoreAngleEndpoint.state_bounds ht).2.2.2.2.trans_lt
      (by linarith [CoreAngleEndpoint.diagonal_bounds.2])
  have hP := P_chord (NegativeTwo.source_mem hs)
  dsimp [value,e,g,γ]
  linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic

lemma upper_displacement_cost {a b B x k : ℝ} (hs : OuterState a b) (hx : 0≤x)
    (hk : k≤53/100) (hdisp : B≤a-1+k*x) : γ<value b B (Real.pi/2+x) := by
  have hh := aligned_lower (NegativeTwo.source_mem hs)
  dsimp [aligned] at hh
  rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hh
  have hp := mul_le_mul_of_nonneg_left hdisp (show 0≤g by norm_num [g])
  have hgk : 0≤1-g*k := by dsimp [g]; linarith
  have hpay := mul_nonneg hgk hx
  dsimp [value,γ]
  nlinarith

theorem upper_secondary {a b A B x : ℝ} (hs : OuterState a b) (_ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a*Real.cos x+b*Real.sin x-B) :
    γ<value b B (Real.pi/2+x) := by
  have hcut : B≤OppositeTwo.upperCut a b x := by
    dsimp [OppositeTwo.upperCut]
    nlinarith
  have hh := OppositeTwo.upper_secondary_displacement hs hx
  exact upper_displacement_cost hs hx.1 (k := (2/5:ℝ)) (by norm_num) (by linarith)

theorem upper_primary {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x-B*Real.cos x) :
    γ<value b B (Real.pi/2+x) :=
  upper_displacement_cost hs hx.1 (k := (53/100:ℝ)) le_rfl
    (MixedTwo.PositiveCore.upper_primary_displacement hs ht hx hsep)

theorem upper_second {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a*Real.sin x-b*Real.cos x+A) :
    γ<value b B (Real.pi/2+x) := by
  have htr := positive_trig hx
  have hA := (CoreAngleEndpoint.state_bounds ht).2.1
  have ha : a<(283/200:ℝ) := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
  have has := mul_le_mul_of_nonneg_right ha.le htr.2.2.1
  have hbc := mul_nonneg hs.1 (by linarith [htr.1] : 0≤Real.cos x)
  have hxlo : (2/5:ℝ)<x := by
    by_contra hn
    have hsin : Real.sin x≤(2/5:ℝ) := htr.2.2.2.2.1.trans (le_of_not_gt hn)
    have hs2 := pow_le_pow_left₀ htr.2.2.1 hsin 2
    have hcos : (229/250:ℝ)<Real.cos x := by
      nlinarith [Real.sin_sq_add_cos_sq x,htr.1]
    nlinarith
  have hb : b<(2/5:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left htr.1.le hs.1
    nlinarith [htr.2.2.2.1]
  have hB : B<(559/1000:ℝ) :=
    (CoreAngleEndpoint.state_bounds ht).2.2.2.2.trans_lt
      (by linarith [CoreAngleEndpoint.diagonal_bounds.2])
  have hT := MixedTEnvelope.upper (NegativeTwo.source_mem hs)
  dsimp [MixedTEnvelope.k,MixedTEnvelope.q] at hT
  dsimp [value,c,g,γ]
  linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
end
end
end
