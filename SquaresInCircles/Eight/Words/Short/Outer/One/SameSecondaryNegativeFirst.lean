module

public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryUpperAxial
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryUpperDiagonalData
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryFirstZero

/-!
# Eight squares: the first negative secondary owner

Compactness on the initial strip leaves alignment, the moving zero-source boundary or the
diagonal target (`original_strip`). The stationary angular derivative excludes every other
minimum, including at the final angle. The single multiplier support covers all later angles
(`original`).
-/

section
/-!
## The four upper primary owners whose minimum is at the lower contact

Convexity in the state coordinate
and positivity of the actual lower-endpoint derivative reduce every
original contact to its axial or diagonal reference curve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio)

theorem projection_whole {x : ℝ} (hx : x∈Icc 0 (7/10)) : (233/250:ℝ)<projection x := by
  have hconcave : ConcaveOn ℝ (Icc (0:ℝ) (7/10)) projection := by
    apply concave_of_deriv2 (fun y _ => projection_hasDerivAt y)
      (f'':=fun y => -projection y)
    · intro y _
      have h := (Real.hasDerivAt_sin y).neg.fun_add ((Real.hasDerivAt_cos y).const_mul rho)
      convert h using 1
      · funext w
        rfl
      · simp only [projection]
        ring
    · intro y hy
      have ht := positive_trig hy
      have hp := mul_nonneg (by linarith [rho_bounds.1] : 0≤rho) ht.2.2.1
      dsimp [projection]
      linarith [ht.1]
  apply concave_gt_of_endpoints hconcave hx
  · norm_num [projection]
  · have hs := RoleFour.fine_cap_trig
    have hp := mul_le_mul rho_bounds.1.le
      (show (161/250:ℝ)≤Real.sin (7/10) by linarith [hs.1]) (by norm_num)
      (by linarith [rho_bounds.1] : 0≤rho)
    dsimp [projection]
    linarith [hs.2.2.1]

theorem diagonal_support (r : Row) {x : ℝ} (hx : DiagonalDomain x) :
    -CommonQuarter.radius*Real.sqrt ((P r)^2+(t r)^2)≤P r*V x-t r*U x := by
  have hs := Real.sq_sqrt (show 0≤(P r)^2+(t r)^2 by positivity)
  have hn := Real.sqrt_nonneg ((P r)^2+(t r)^2)
  have hR := radius_bounds
  have hnorm : (CommonQuarter.radius*Real.sqrt ((P r)^2+(t r)^2))^2=Q0*((P r)^2+(t r)^2) := by
    rw [mul_pow,radius_sq,hs]
  have hidentity : (P r*V x-t r*U x)^2+(P r*U x+t r*V x)^2=
      ((P r)^2+(t r)^2)*Q0 := by
    nlinarith [diagonal_circle hx]
  have hp : 0≤CommonQuarter.radius*Real.sqrt ((P r)^2+(t r)^2) := mul_nonneg (by linarith) hn
  nlinarith [sq_nonneg (P r*U x+t r*V x)]

theorem simple_norm_reserve (r : Row) (hr : r=2∨r=5) :
    CommonQuarter.radius*Real.sqrt ((P r)^2+(t r)^2)+(1/20:ℝ)<(p r+q r)*(969/500:ℝ) := by
  have hs := Real.sq_sqrt (show 0≤(P r)^2+(t r)^2 by positivity)
  have hn := Real.sqrt_nonneg ((P r)^2+(t r)^2)
  have hnorm : (CommonQuarter.radius*Real.sqrt ((P r)^2+(t r)^2))^2=Q0*((P r)^2+(t r)^2) := by
    rw [mul_pow,radius_sq,hs]
  have hp : 0≤CommonQuarter.radius*Real.sqrt ((P r)^2+(t r)^2) :=
    mul_nonneg (by linarith [radius_bounds.1]) hn
  rcases hr with rfl | rfl <;> norm_num [p,q,P,t,Q0] at hnorm ⊢ <;> nlinarith

theorem J_norm_positive (r : Row) (hr : r=2∨r=5) {x : ℝ} (hx : DiagonalDomain x) :
    0<J r x := by
  have hc := diagonal_coordinate_bounds hx
  have hrT := diagonal_radical hx
  have hU : 0<U x := by linarith [hc.1]
  have he : J r x*U x=(p r+q r)*T x+P r*V x-t r*U x := by
    have hp := (diagonal_projection hx).1
    have hVU : V x/U x*U x=V x := div_mul_cancel₀ _ hU.ne'
    dsimp only [J]
    linear_combination (p r+q r)*hp+((p r+q r)*Real.sin x+P r)*hVU
  have hL : 0<p r+q r := by linarith [(coefficients r).2.2.1]
  have hprod := mul_lt_mul_of_pos_left hrT.1 hL
  have hs := diagonal_support r hx
  have hn := simple_norm_reserve r hr
  have hpositive : 0<J r x*U x := by linarith
  exact (mul_pos_iff_of_pos_right hU).1 hpositive

theorem J_three_positive {x : ℝ} (hx : DiagonalDomain x) : 0<J 3 x := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hp := mul_le_mul_of_nonneg_left (diagonal_ratio hx).2 ht.2.2.1
  have hg := projection_whole (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  dsimp [projection] at hg
  norm_num [J,p,q,P,t]
  nlinarith

theorem diagonal_small_sine_ratio {x : ℝ} (hx : DiagonalDomain x)
    (hs : Real.sin x<(197/1000:ℝ)) : V x/U x<(11/25:ℝ) := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hr := diagonal_radical hx
  have hc := diagonal_coordinate_bounds hx
  have hz0 : 0<z x ∧ z x<(2/5:ℝ) := by
    dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z,SecondWord.SameZero.PJ.Diagonal.z₀]
    constructor <;> linarith [ShortMixedZero.fine_diagonal_bounds.1,
      ShortMixedZero.fine_diagonal_bounds.2,ht.2.2.1]
  have hfirst := mul_le_mul hs.le
    (hr.2.1.trans ShortWord.MixedQuarter.Reference.radius_fine.2.le)
    (by linarith [hr.1] : 0≤T x) (by norm_num)
  have hsecond := mul_le_mul_of_nonneg_left ht.2.1 hz0.1.le
  have hV : V x<(79/100:ℝ) := by
    dsimp [V,SecondWord.SameZero.PJ.Diagonal.vertical]
    nlinarith
  have hU : (181/100:ℝ)<U x := by
    have hcircle := diagonal_circle hx
    norm_num [Q0] at hcircle
    nlinarith [hc.1,hc.2.2.1]
  apply (div_lt_iff₀ (by linarith : 0<U x)).2
  linarith

theorem J_four_positive {x : ℝ} (hx : DiagonalDomain x) : 0<J 4 x := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hc := diagonal_coordinate_bounds hx
  have hrho := (diagonal_ratio hx).2
  by_cases hsign : 0≤q 4*Real.sin x+P 4
  · have hh := mul_le_mul_of_nonneg_left hrho hsign
    have hg := projection_whole (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
    dsimp [projection] at hg
    norm_num [J,p,q,P,t] at hsign hh ⊢
    nlinarith [rho_bounds.2]
  · have hs : Real.sin x<(197/1000:ℝ) := by
      norm_num [q,P] at hsign
      linarith
    have hcos : (49/50:ℝ)<Real.cos x := by
      nlinarith [Real.sin_sq_add_cos_sq x,ht.1,ht.2.2.1]
    have hratio := diagonal_small_sine_ratio hx hs
    have hh := mul_le_mul_of_nonpos_left hratio.le (le_of_lt (lt_of_not_ge hsign))
    norm_num [J,p,q,P,t] at hh ⊢
    nlinarith [ht.2.2.1]

theorem J_simple_positive (r : Row) (hr : r=2∨r=3∨r=4∨r=5)
    {x : ℝ} (hx : DiagonalDomain x) : 0<J r x := by
  rcases hr with rfl | rfl | rfl | rfl
  · exact J_norm_positive 2 (Or.inl rfl) hx
  · exact J_three_positive hx
  · exact J_four_positive hx
  · exact J_norm_positive 5 (Or.inr rfl) hx

theorem after_simple (r : Row) (hr : r=2∨r=3∨r=4∨r=5)
    {B e x : ℝ} (he : IsEvent e) (hd : Domain B x) (hx : e≤x) :
    (4489/5000:ℝ)<value r B x := by
  have hxD := after_diagonal_domain he ⟨hx,hd.2.1.2⟩
  have hD := diagonal_contact_domain hxD
  have hJ := J_simple_positive r hr hxD
  rw [J_first r hxD] at hJ
  have hminimum := endpoint_minimum r hD hd (diagonal_lower_target hd hxD) hJ.le
  have hinc := G_simple_increasing r (Or.inr hr) he
    ⟨le_rfl,(event_bounds he).2.2.2⟩ ⟨hx,hd.2.1.2⟩ hx
  rw [G_at_event r he,G_value r hxD] at hinc
  have hF : (4489/5000:ℝ)<F r e := by
    by_cases hpair : r=3∨r=4
    · exact F_pair_lower r hpair he ⟨by linarith [(event_bounds he).1],le_rfl⟩
    · have hs : r=2∨r=5 := by rcases hr with h | h | h | h <;> tauto
      have hh := F_simple_lower r hs he ⟨by linarith [(event_bounds he).1],le_rfl⟩
      linarith
  exact hF.trans_le (hinc.trans hminimum)

theorem simple_contact (r : Row) (hr : r=2∨r=3∨r=4∨r=5)
    {B x : ℝ} (hd : Domain B x) : (4489/5000:ℝ)<value r B x := by
  obtain ⟨e,he⟩ := exists_event
  rcases le_total x e with hx | hx
  · exact before_simple r hr he hd hx
  · exact after_simple r hr he hd hx

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
end
end
end

section
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstStrip
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)

lemma diagonal_lower {x : ℝ} (hx : x∈Icc 0 strip) :
    (8981/10000:ℝ)<Negative.cost 0 outerDiagonal x := by
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
  have hdom : ∀y∈Icc 0 strip,Domain outerDiagonal y :=
    fun y hy => ⟨hdiag,hy,(contact_target_diagonal hy).1.le⟩
  have hm : MonotoneOn (Negative.cost 0 outerDiagonal) (Icc 0 strip) := monoOn_of_hasDeriv_nonneg
    (fun y hy => (cost_angle_hasDerivAt 0 (wide_domain (hdom y hy))).continuousAt.continuousWithinAt)
    (fun y hy => cost_angle_hasDerivAt 0 (wide_domain (hdom y (Ioo_subset_Icc_self hy))))
    (fun y hy => (diagonal_first_positive (Ioo_subset_Icc_self hy)).le)
  have h0 : (0:ℝ)∈Icc 0 strip := by norm_num [strip]
  exact (initial_lower (hdom 0 h0)).trans_le (hm h0 hx hx.1)

lemma interior_not_minimum {B x : ℝ} (hd : Domain B x)
    (hx : 0<x) (hB : B<outerDiagonal) (hb : 0<contact B x)
    (hmin : ∀C y,Domain C y→Negative.cost 0 B x≤Negative.cost 0 C y) : False := by
  let T : Set ℝ := Ioo 0 outerDiagonal ∩ (fun C => contact C x) ⁻¹' Ioi 0
  have hcontactT : Continuous (fun C => contact C x) := by dsimp [contact,arc]; fun_prop
  have hT : IsOpen T := isOpen_Ioo.inter (isOpen_Ioi.preimage hcontactT)
  have hmemT : B∈T := ⟨⟨by linarith [target_lower hd],hB⟩,hb⟩
  have hlocalT : IsLocalMin (fun C => Negative.cost 0 C x) B := by
    filter_upwards [hT.mem_nhds hmemT] with C hC
    exact hmin C x ⟨Ioo_subset_Icc_self hC.1,hd.2.1,hC.2.le⟩
  have hstat : targetFirst 0 B x=0 :=
    hlocalT.hasDerivAt_eq_zero (cost_target_hasDerivAt 0 (wide_domain hd))
  have hfirst : 0<Negative.first 0 B x := by
    rw [stationary_first hd hstat]
    exact transport_positive hd
  let O : Set ℝ := Ioi 0 ∩ (contact B) ⁻¹' Ioi 0
  have hcontactO : Continuous (contact B) := by unfold contact; fun_prop
  have hO : IsOpen O := isOpen_Ioi.inter (isOpen_Ioi.preimage hcontactO)
  have hmemO : x∈O := ⟨hx,hb⟩
  obtain ⟨ε,hε,hsub⟩ := exists_closed_interval_in_open hO hmemO
  have hdom {y : ℝ} (hy : y∈Icc (x-ε) x) : Domain B y := by
    have hh := hsub (show y∈Icc (x-ε) (x+ε) from ⟨hy.1,by linarith [hy.2]⟩)
    exact ⟨hd.1,⟨hh.1.le,hy.2.trans hd.2.1.2⟩,hh.2.le⟩
  have hn := ContactMinimumDerivatives.right_endpoint (show x-ε<x by linarith)
    (first_continuousAt hd) (fun y hy => cost_angle_hasDerivAt 0 (wide_domain (hdom hy)))
    (fun y hy => hmin B y (hdom hy))
  linarith

lemma minimum_lower {B x : ℝ} (hd : Domain B x)
    (hmin : ∀C y,Domain C y→Negative.cost 0 B x≤Negative.cost 0 C y) :
    (8981/10000:ℝ)<Negative.cost 0 B x := by
  by_cases hx : x=0
  · subst x
    exact initial_lower hd
  by_cases hb : contact B x=0
  · exact Zero.original_lower hd hb
  by_cases hB : B=outerDiagonal
  · subst B
    exact diagonal_lower hd.2.1
  exact (interior_not_minimum hd (lt_of_le_of_ne hd.2.1.1 (Ne.symm hx))
    (lt_of_le_of_ne hd.1.2 hB) (lt_of_le_of_ne hd.2.2 (Ne.symm hb)) hmin).elim

theorem contact_lower {B x : ℝ} (hd : Domain B x) :
    (8981/10000:ℝ)<Negative.cost 0 B x := by
  let guard : ℝ×ℝ→ℝ := fun z => contact z.1 z.2
  let objective : ℝ×ℝ→ℝ := fun z => Negative.cost 0 z.1 z.2
  have hg : Continuous guard := by dsimp [guard,contact,arc]; fun_prop
  have hf : Continuous objective := by dsimp [objective,Negative.cost,target,targetCost,contact,arc]; fun_prop
  obtain ⟨z,hz,hbetter,hmin⟩ := contact_region_minimum hg hf
    (p₀:=(B,x)) ⟨hd.1,hd.2.1,hd.2.2⟩
  have hzd : Domain z.1 z.2 := ⟨hz.1,hz.2.1,hz.2.2⟩
  have hh := minimum_lower hzd (fun C y hCy => hmin (C,y) hCy.1 hCy.2.1 hCy.2.2)
  exact hh.trans_le hbetter

theorem original_strip {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 strip)
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x) :
    (8981/10000:ℝ)<Real.pi/2-x+c 0-P 0*a+t 0*b+p 0*A-q 0*B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hrequired : contact B x≤b := by
    dsimp [contact]
    rw [(SameContact.actual_arc ht).1]
    linarith
  have hcost : Real.pi/2-x+c 0+target 0 b+targetCost 0 B=
      Real.pi/2-x+c 0-P 0*a+t 0*b+p 0*A-q 0*B := by
    have hh := Secondary.original_cost 0 hs ht
    linarith
  rw [←hcost]
  by_cases hactive : 0≤contact B x
  · have hd : Domain B x := ⟨hB,hx,hactive⟩
    have hsource := target_monotone 0 (source_mem hd) hb hrequired
    have hh := contact_lower hd
    dsimp [Negative.cost] at hh
    linarith
  · have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
      ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
    have hc : Continuous (fun D => contact D x) := by dsimp [contact,arc]; fun_prop
    obtain ⟨D,hD,he⟩ := intermediate_value_Icc hB.2 hc.continuousOn
      (show (0:ℝ)∈Icc (contact B x) (contact outerDiagonal x) from
        ⟨by linarith,(contact_target_diagonal hx).1.le⟩)
    beta_reduce at he
    have hDouter : D∈Icc 0 outerDiagonal := ⟨hB.1.trans hD.1,hD.2⟩
    have htarget := targetCost_antitone 0 hB hDouter hD.1
    have hsource := target_monotone 0 (show (0:ℝ)∈Icc 0 outerDiagonal from
      ⟨le_rfl,hdiag.1⟩) hb hb.1
    have hh := contact_lower (show Domain D x from ⟨hDouter,hx,he.ge⟩)
    dsimp [Negative.cost] at hh
    rw [he] at hh
    linarith

theorem original {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x) :
    (449/500:ℝ)<Real.pi/2-x+c 0-P 0*a+t 0*b+p 0*A-q 0*B := by
  by_cases hsmall : x≤ strip
  · linarith [original_strip hs ht ⟨hx.1,hsmall⟩ hm]
  · have hh := FirstNorm.original_later hs ht
      (show x∈Icc (3/100:ℝ) (7/10) from ⟨by dsimp [strip] at hsmall; linarith,hx.2⟩) hm
    linarith

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstStrip
end
end
end
