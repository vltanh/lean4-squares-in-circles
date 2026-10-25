module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneEdgeFiveAPrimaryUpper
public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryNegativeGeometry

/-!
# The two lower A-primary supports and both complete halves

Uncompiled transcription of Section 6, equations (33)--(35). The
original weak separator forces the stated .226 cap. Both genuine target
endpoints then increase; the diagonal initial value is no smaller than
the axial one. The shared cap lemma is the identical geometric argument
already transcribed for the negative primary families.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.APrimary
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference
abbrev cap := Opposite.Primary.Negative.cap

def GA (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2-x+c r+(p r-1-P r)*outerAxial+1/2+Real.cos x/2+(1/2+outerAxial)*Real.sin x
def GD (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2-x+c r+(p r-1)*outerAxial-(P r+t r)*outerDiagonal+1/2+
    (1/2+outerDiagonal)*(Real.cos x+Real.sin x)
def GAd (x : ℝ) : ℝ := -1-Real.sin x/2+(1/2+outerAxial)*Real.cos x
def GDd (x : ℝ) : ℝ := -1+(1/2+outerDiagonal)*(Real.cos x-Real.sin x)

theorem forced_cap (r : Row) (hr : ARows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Primary r false a b A B x) : x<cap := by
  apply Opposite.Primary.Negative.forced_cap hs ht hx
  have hd : direction false = -1 := by
    simp [direction,ShortWord.MixedQuarter.direction]
  dsimp only [Primary] at hm
  rw [A_sign hr,hd] at hm
  simp only [width] at hm
  simp only [Opposite.Primary.width]
  linarith
theorem GA_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (GA r) (GAd x) x := by
  have h := ((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+c r+(p r-1-P r)*outerAxial+1/2)).add
      ((Real.hasDerivAt_cos x).div_const 2)).add
        ((Real.hasDerivAt_sin x).const_mul (1/2+outerAxial))
  convert h using 1
  · funext y; simp only [GA,Pi.add_apply,Pi.neg_apply,id_eq]; ring
  · simp only [GAd]; ring
theorem GD_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (GD r) (GDd x) x := by
  have h := (((hasDerivAt_id x).neg).const_add
    (Real.pi/2+c r+(p r-1)*outerAxial-(P r+t r)*outerDiagonal+1/2)).add
      (((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).const_mul (1/2+outerDiagonal))
  convert h using 1
  · funext y; simp only [GD,Pi.add_apply,Pi.neg_apply,id_eq]; ring
  · simp only [GDd]; ring
theorem GAd_positive {x : ℝ} (hx : x∈Icc 0 cap) : 0<GAd x := by
  have tr := Opposite.Primary.Negative.small_trig hx
  have ha : (957/500:ℝ)<1/2+outerAxial := by linarith [ShortOuterZero.fine_axial_bounds.1]
  have hh := mul_lt_mul'' ha tr.1 (by norm_num) (by norm_num)
  dsimp [GAd]
  linarith [tr.2.2]
theorem GDd_positive {x : ℝ} (hx : x∈Icc 0 cap) : 0<GDd x := by
  have tr := Opposite.Primary.Negative.small_trig hx
  have hd : (1399/1000:ℝ)<1/2+outerDiagonal := by linarith [ShortMixedZero.fine_diagonal_bounds.1]
  have hc : (749/1000:ℝ)<Real.cos x-Real.sin x := by linarith [tr.1,tr.2.2]
  have hh := mul_lt_mul'' hd hc (by norm_num) (by norm_num)
  dsimp [GDd]
  linarith
theorem GA_monotone (r : Row) : MonotoneOn (GA r) (Icc 0 cap) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (GA_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => GA_hasDerivAt r x)
    (fun x hx => (GAd_positive (Ioo_subset_Icc_self hx)).le)
theorem GD_monotone (r : Row) : MonotoneOn (GD r) (Icc 0 cap) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (GD_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => GD_hasDerivAt r x)
    (fun x hx => (GDd_positive (Ioo_subset_Icc_self hx)).le)

def initialBox (r : Row) : Interval (GA r 0) := by
  convert (((halfPi.add (Interval.point (c r))).add
    ((Interval.point (p r-1-P r)).mul axial)).add (Interval.point 1)) using 1
  simp [GA]
  ring
theorem initial (r : Row) (hr : ARows r) : (2697/2500:ℝ)<GA r 0 := by
  -- the lower endpoint of `initialBox` before its cast to `Interval (GA r 0)`
  let X := ((halfPi.add (Interval.point (c r))).add
    ((Interval.point (p r-1-P r)).mul axial)).add (Interval.point 1)
  have he : GA r 0=Real.pi/2+c r+(p r-1-P r)*outerAxial+1 := by
    simp only [GA,Real.sin_zero,Real.cos_zero]; ring
  have hh : (2697/2500:ℝ)<X.lo := by
    rcases hr with rfl|rfl <;> dsimp [X,c,p,P] <;> mixed_fixed
  rw [he]
  exact hh.trans_le X.mem.1
theorem diagonal_initial (r : Row) (hr : ARows r) : GA r 0≤GD r 0 := by
  have hc := coefficient_bounds r
  have hP := mul_nonneg hc.2.1 (show 0≤outerAxial-outerDiagonal by
    linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2])
  have ht := mul_nonneg (show 0≤1-t r by linarith [hc.2.2.2.2.2])
    (show 0≤outerDiagonal by linarith [outer_endpoint_bounds.2.2.1])
  simp only [GA,GD,Real.sin_zero,Real.cos_zero]
  nlinarith
theorem axial_lower (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 cap) :
    (2697/2500:ℝ)<GA r x :=
  (initial r hr).trans_le (GA_monotone r (by norm_num [cap,Opposite.Primary.Negative.cap]) hx hx.1)
theorem diagonal_lower (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 cap) :
    (2697/2500:ℝ)<GD r x :=
  ((initial r hr).trans_le (diagonal_initial r hr)).trans_le
    (GD_monotone r (by norm_num [cap,Opposite.Primary.Negative.cap]) hx hx.1)

theorem lower_original (r : Row) (hr : ARows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Primary r false a b A B x) : (2697/2500:ℝ)<cost r false a b A B x := by
  have hsmall : x∈Icc 0 cap := ⟨hx.1,(forced_cap r hr hs ht hx hm).le⟩
  have tr := Opposite.Primary.Negative.small_trig hsmall
  have hc := coefficient_bounds r
  have hdir : direction false = -1 := by
    simp [direction,ShortWord.MixedQuarter.direction]
  have hsource := ShortWord.MixedQuarter.outer_axial_lower (X:=p r-1) (Y:=q r) hs
    (by linarith [hc.1]) (by linarith [hc.2.2.1])
  have hY : 0≤Real.cos x-t r := by linarith [tr.1,hc.2.2.2.2.2]
  have htarget := outer_endpoint_support (X:= -P r+Real.sin x) (Y:=Real.cos x-t r) ht hY
  rw [show -P r+Real.sin x+(Real.cos x-t r)=-P r+Real.sin x+Real.cos x-t r by ring] at htarget
  have hh := primary_support r false (lam:=1) (by norm_num) hm
    (S:=(p r-1)*outerAxial)
    (T:=min ((-P r+Real.sin x)*outerAxial)
      ((-P r+Real.sin x+Real.cos x-t r)*outerDiagonal))
    (by rw [A_sign hr]; linarith [hsource])
    (by rw [A_sign hr,hdir]; linarith [htarget])
  have hang : angle false x=Real.pi/2-x := by
    simp only [angle,ShortWord.MixedQuarter.angle,hdir]; ring
  rw [hang] at hh
  rcases le_total ((-P r+Real.sin x)*outerAxial)
    ((-P r+Real.sin x+Real.cos x-t r)*outerDiagonal) with hsplit|hsplit
  · rw [min_eq_left hsplit] at hh
    have hv := axial_lower r hr hsmall
    simp only [GA,width] at hv hh
    linarith
  · rw [min_eq_right hsplit] at hh
    have hv := diagonal_lower r hr hsmall
    simp only [GD,width] at hv hh
    linarith

theorem original (r : Row) (hr : ARows r) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Primary r upper a b A B x) : (2697/2500:ℝ)<cost r upper a b A B x := by
  cases upper
  · exact lower_original r hr hs ht hx hm
  · linarith [Upper.original r hr hs ht hx hm]

end SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.APrimary
