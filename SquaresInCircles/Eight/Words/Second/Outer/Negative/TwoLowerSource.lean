module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoPrimaryBound

/-!
# Eight squares: the original lower source-primary weak owner

The source contact increases. Its active cost increases because the original target circle gives
a strict speed reserve. An exact intermediate-value contact therefore compares the original pair
to alignment or to the physical diagonal boundary (`original_lower_source_primary`). The original
target and its common circle are kept throughout.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic

def lowerSpeed (A B x : ℝ) : ℝ :=
  (B-1/2)*Real.sin x+(A+1/2)*Real.cos x

lemma lowerSource_zero (A B : ℝ) : lowerSource A B 0=1-B := by
  norm_num [lowerSource]
  ring

lemma lowerSource_hasDerivAt (A B x : ℝ) :
    HasDerivAt (lowerSource A B) (lowerSpeed A B x) x := by
  have h := (((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).add
    ((Real.hasDerivAt_sin x).const_mul (A+1/2))
  show HasDerivAt (fun y => 1/2+(1/2-B)*Real.cos y+(A+1/2)*Real.sin y)
    (lowerSpeed A B x) x
  exact h.congr_deriv (by dsimp [lowerSpeed]; ring)

lemma lowerSpeed_positive {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) : 0<lowerSpeed A B x := by
  have hh := positive_trig hx
  have hmain := mul_nonneg
    (show 0≤A+1/2-1399/1000 by
      linarith [(primary_mem ht).1,fine_outer_endpoint_bounds.2])
    (show 0≤Real.cos x by linarith [hh.1])
  have hsmall := mul_nonneg ht.1 hh.2.2.1
  dsimp [lowerSpeed]
  nlinarith [hh.1,hh.2.2.2.1]

lemma lowerSource_monotone {A B : ℝ} (ht : OuterState A B) :
    MonotoneOn (lowerSource A B) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (lowerSource_hasDerivAt A B x).continuousAt.continuousWithinAt)
    (fun x _ => lowerSource_hasDerivAt A B x)
    (fun x hx => (lowerSpeed_positive ht (Ioo_subset_Icc_self hx)).le)

lemma lowerSource_norm {A B : ℝ} (ht : OuterState A B) (x : ℝ) :
    (lowerSource A B x-1/2)^2+(lowerSpeed A B x)^2=Q0-2*B := by
  dsimp [lowerSource,lowerSpeed]
  linear_combination ht.2.2+
    ((B-1/2)^2+(A+1/2)^2)*(Real.sin_sq_add_cos_sq x)

lemma lower_active_speed {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (ha : lowerSource A B x∈Icc outerDiagonal outerAxial) :
    1<PPrimaryLabel.d1 (lowerSource A B x)*lowerSpeed A B x := by
  have hv := lowerSpeed_positive ht hx
  have hn := lowerSource_norm ht x
  have hcenter : 0≤lowerSource A B x-1/2 ∧ lowerSource A B x-1/2<183/200 := by
    constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.1]
  have hB : B<(9/10:ℝ) := (source_mem ht).2.trans_lt outer_endpoint_bounds.2.2.2
  have hspeed : (11/10:ℝ)<lowerSpeed A B x := by
    norm_num [Q0] at hn
    nlinarith
  have hM := OppositeTwo.M_first_lower ha
  have hh := mul_lt_mul hM hspeed.le (by norm_num : (0:ℝ)<11/10)
    (by linarith [hM] : 0≤PPrimaryLabel.d1 (lowerSource A B x))
  norm_num at hh
  linarith

lemma lowerSource_cap {A B : ℝ} (ht : OuterState A B) :
    outerDiagonal<lowerSource A B (7/10) := by
  have htr := CommonQuarter.cap_trig
  have hcos0 : 0≤Real.cos (7/10:ℝ) := by linarith [htr.2.2.1]
  have hsin0 : 0≤Real.sin (7/10:ℝ) := by linarith [htr.1]
  have hlow := mul_nonneg
    (show 0≤1/2-B+2/5 by linarith [(source_mem ht).2,outer_endpoint_bounds.2.2.2]) hcos0
  have hhigh := mul_nonneg
    (show 0≤A+1/2-1399/1000 by linarith [(primary_mem ht).1,fine_outer_endpoint_bounds.2]) hsin0
  dsimp [lowerSource]
  nlinarith [htr.2.2.2,htr.1,outer_endpoint_bounds.2.2.2]

lemma lower_active_monotone {A B l u : ℝ} (ht : OuterState A B)
    (hl : l∈Icc 0 (7/10)) (hu : u∈Icc 0 (7/10)) (_hlu : l≤u)
    (hleft : outerDiagonal≤lowerSource A B l)
    (hright : lowerSource A B u≤outerAxial) :
    MonotoneOn (fun t => -t+PPrimaryLabel.outer (lowerSource A B t)) (Icc l u) := by
  have hdom (t : ℝ) (htime : t∈Icc l u) :
      t∈Icc 0 (7/10) ∧ lowerSource A B t∈Icc outerDiagonal outerAxial := by
    have htf : t∈Icc 0 (7/10) := ⟨hl.1.trans htime.1,htime.2.trans hu.2⟩
    exact ⟨htf,⟨hleft.trans (lowerSource_monotone ht hl htf htime.1),
      (lowerSource_monotone ht htf hu htime.2).trans hright⟩⟩
  have hd (t : ℝ) (htime : t∈Icc l u) :
      HasDerivAt (fun z => -z+PPrimaryLabel.outer (lowerSource A B z))
        (-1+PPrimaryLabel.d1 (lowerSource A B t)*lowerSpeed A B t) t := by
    have hc := (PPrimaryLabel.outer_hasDerivAt
      (primary_domain (hdom t htime).2)).comp t (lowerSource_hasDerivAt A B t)
    exact (hasDerivAt_id' t).neg.add hc
  exact monoOn_of_hasDeriv_nonneg
    (fun t htime => (hd t htime).continuousAt.continuousWithinAt)
    (fun t htime => hd t (Ioo_subset_Icc_self htime))
    (fun t htime => by
      have h := hdom t (Ioo_subset_Icc_self htime)
      linarith [lower_active_speed ht h.1 h.2])

theorem original_lower_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) (Real.pi/2-x)) :
    (8977827/10000000:ℝ)<value b B (Real.pi/2-x) := by
  have hcut := lower_source_cut hx hm
  have ha := primary_mem hs
  have hactual : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
  by_cases hstart : outerDiagonal≤1-B
  · have hzero : outerDiagonal≤lowerSource A B 0 := by simpa only [lowerSource_zero] using hstart
    have hmono := lower_active_monotone ht (by norm_num) hx hx.1 hzero (hcut.trans ha.2)
    have hstep := hmono (show (0:ℝ)∈Icc 0 x from ⟨le_rfl,hx.1⟩)
      (show x∈Icc 0 x from ⟨hx.1,le_rfl⟩) hx.1
    have hxdom : lowerSource A B x∈Icc outerDiagonal outerAxial :=
      ⟨hzero.trans (lowerSource_monotone ht (by norm_num) hx hx.1),hcut.trans ha.2⟩
    have hM := OppositeTwo.M_monotone hxdom ha hcut
    rw [hactual] at hM
    dsimp only at hstep
    rw [lowerSource_zero] at hstep
    have hbase := aligned_lower (show 1-B∈Icc outerDiagonal 1 from ⟨hstart,by linarith [ht.1]⟩)
    have harg : 1-(1-B)=B := by ring
    dsimp [aligned] at hbase
    rw [harg] at hbase
    dsimp [value]
    linarith
  · have hcont : Continuous (lowerSource A B) :=
      continuous_iff_continuousAt.2 fun y => (lowerSource_hasDerivAt A B y).continuousAt
    obtain ⟨y,hy,hycontact⟩ := intermediate_value_Icc
      (show (0:ℝ)≤7/10 by norm_num) hcont.continuousOn
      (show outerDiagonal∈Icc (lowerSource A B 0) (lowerSource A B (7/10)) by
        rw [lowerSource_zero]
        exact ⟨by linarith,(lowerSource_cap ht).le⟩)
    have hdiag := PrimaryDiagonal.original_contact ht hy hycontact
    rcases le_total x y with hxy | hyx
    · have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
      have hP := P_monotone (source_mem hs) hd (source_mem hs).2
      dsimp [value] at *
      linarith
    · have hmono := lower_active_monotone ht hy hx hyx (by rw [hycontact]) (hcut.trans ha.2)
      have hstep := hmono (show y∈Icc y x from ⟨le_rfl,hyx⟩)
        (show x∈Icc y x from ⟨hyx,le_rfl⟩) hyx
      dsimp only at hstep
      rw [hycontact] at hstep
      have hxdom : lowerSource A B x∈Icc outerDiagonal outerAxial := by
        have hh := lowerSource_monotone ht hy hx hyx
        rw [hycontact] at hh
        exact ⟨hh,hcut.trans ha.2⟩
      have hM := OppositeTwo.M_monotone hxdom ha hcut
      rw [hactual] at hM
      have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
      have hD : PPrimaryLabel.outer outerDiagonal= -P outerDiagonal := by
        have hh := PLabel.primary_actual (ShortOuterOne.SameContact.arc_state hd)
        rw [ShortOuterOne.SameContact.arc_diagonal] at hh
        exact hh
      rw [hD] at hstep
      dsimp [value] at *
      linarith

end SquaresInCircles.Eight.SecondWord.NegativeTwo
