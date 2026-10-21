module

public import SquaresInCircles.Eight.TableFree.SecondOuterFixedReference

/-!
# Exact fixed-reference arithmetic for every literal outer label

Uncompiled source draft.  An already established bracket for one
physical coordinate and its circle radical gives explicit bounds for
the value and two derivatives of any literal role label.  This is
ordinary finite arithmetic at a named reference, not a cover of the
coordinate domain or an external arithmetic certificate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.GeneralReference
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def lo (c l u : ℝ) : ℝ := min (c*l) (c*u)
def hi (c l u : ℝ) : ℝ := max (c*l) (c*u)
def rlo (bl bh ul uh : ℝ) : ℝ := (bl+1/2)/uh
def rhi (bl bh ul uh : ℝ) : ℝ := (bh+1/2)/ul
def dlo (bl bh ul uh : ℝ) : ℝ := Q0/uh^3
def dhi (bl bh ul uh : ℝ) : ℝ := Q0/ul^3

def valueLo (H : RoleLabel) (bl bh ul uh : ℝ) : ℝ :=
  H.c+lo H.p (ul-1/2) (uh-1/2)+lo H.q bl bh+lo H.r bl^2 bh^2+
    lo H.s ((ul-1/2)*bl) ((uh-1/2)*bh)
def valueHi (H : RoleLabel) (bl bh ul uh : ℝ) : ℝ :=
  H.c+hi H.p (ul-1/2) (uh-1/2)+hi H.q bl bh+hi H.r bl^2 bh^2+
    hi H.s ((ul-1/2)*bl) ((uh-1/2)*bh)
def firstLo (H : RoleLabel) (bl bh ul uh : ℝ) : ℝ :=
  H.q+lo (2*H.r) bl bh+lo H.s (ul-1/2) (uh-1/2)+
    lo (-H.p) (rlo bl bh ul uh) (rhi bl bh ul uh)+
    lo (-H.s) (bl*rlo bl bh ul uh) (bh*rhi bl bh ul uh)
def firstHi (H : RoleLabel) (bl bh ul uh : ℝ) : ℝ :=
  H.q+hi (2*H.r) bl bh+hi H.s (ul-1/2) (uh-1/2)+
    hi (-H.p) (rlo bl bh ul uh) (rhi bl bh ul uh)+
    hi (-H.s) (bl*rlo bl bh ul uh) (bh*rhi bl bh ul uh)
def secondLo (H : RoleLabel) (bl bh ul uh : ℝ) : ℝ :=
  2*H.r+lo (-2*H.s) (rlo bl bh ul uh) (rhi bl bh ul uh)+
    lo (-H.p) (dlo bl bh ul uh) (dhi bl bh ul uh)+
    lo (-H.s) (bl*dlo bl bh ul uh) (bh*dhi bl bh ul uh)
def secondHi (H : RoleLabel) (bl bh ul uh : ℝ) : ℝ :=
  2*H.r+hi (-2*H.s) (rlo bl bh ul uh) (rhi bl bh ul uh)+
    hi (-H.p) (dlo bl bh ul uh) (dhi bl bh ul uh)+
    hi (-H.s) (bl*dlo bl bh ul uh) (bh*dhi bl bh ul uh)

lemma bounds {l u x : ℝ} (c : ℝ) (hx : x∈Icc l u) :
    lo c l u≤c*x ∧ c*x≤hi c l u :=
  ⟨affine_min_le hx,affine_le_max hx⟩

theorem label (H : RoleLabel) {b bl bh ul uh : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hbox : b∈Icc bl bh)
    (hU : U b∈Icc ul uh) (hbl : 0≤bl) (hul : 1/2<ul) :
    valueLo H bl bh ul uh≤H.outer b ∧ H.outer b≤valueHi H bl bh ul uh ∧
      firstLo H bl bh ul uh≤H.d1 b ∧ H.d1 b≤firstHi H bl bh ul uh ∧
      secondLo H bl bh ul uh≤H.d2 b ∧ H.d2 b≤secondHi H bl bh ul uh := by
  have hr := FixedReference.ratios hb hbox hU hbl hul
  have hul0 : 0<ul := by linarith
  have huh0 : 0<uh := (U_positive (outer_domain hb)).trans_le hU.2
  have ha : arc b∈Icc (ul-1/2) (uh-1/2) := by
    dsimp [U] at hU
    constructor <;> linarith [hU.1,hU.2]
  have harc0 : 0≤arc b := by linarith [ha.1]
  have hbh : 0≤bh := hbl.trans (hbox.1.trans hbox.2)
  have hab : arc b*b∈Icc ((ul-1/2)*bl) ((uh-1/2)*bh) := by
    exact ⟨mul_le_mul ha.1 hbox.1 hbl harc0,
      mul_le_mul ha.2 hbox.2 hb.1 (by linarith [hU.1,hU.2])⟩
  have hb2 : b^2∈Icc bl^2 bh^2 :=
    ⟨pow_le_pow_left₀ hbl hbox.1 2,pow_le_pow_left₀ hb.1 hbox.2 2⟩
  have hri : ratio b∈Icc (rlo bl bh ul uh) (rhi bl bh ul uh) := ⟨hr.1,hr.2.1⟩
  have hdi : ratioD b∈Icc (dlo bl bh ul uh) (dhi bl bh ul uh) := ⟨hr.2.2.1,hr.2.2.2⟩
  have hr0 : 0≤ratio b := by linarith [(outer_ratio_bounds hb).1]
  have hd0 : 0≤ratioD b := (outer_ratio_bounds hb).2.2.1.le
  have hrl : 0≤rlo bl bh ul uh := by dsimp [rlo]; positivity
  have hrh : 0≤rhi bl bh ul uh := by dsimp [rhi]; positivity
  have hdl : 0≤dlo bl bh ul uh := by dsimp [dlo]; norm_num [Q0]; positivity
  have hdh : 0≤dhi bl bh ul uh := by dsimp [dhi]; norm_num [Q0]; positivity
  have hbr : b*ratio b∈Icc (bl*rlo bl bh ul uh) (bh*rhi bl bh ul uh) :=
    ⟨mul_le_mul hbox.1 hri.1 hrl hb.1,mul_le_mul hbox.2 hri.2 hr0 hbh⟩
  have hbd : b*ratioD b∈Icc (bl*dlo bl bh ul uh) (bh*dhi bl bh ul uh) :=
    ⟨mul_le_mul hbox.1 hdi.1 hdl hb.1,mul_le_mul hbox.2 hdi.2 hd0 hbh⟩
  have hvp := bounds H.p ha
  have hvq := bounds H.q hbox
  have hvr := bounds H.r hb2
  have hvs := bounds H.s hab
  have hdr := bounds (2*H.r) hbox
  have hds := bounds H.s ha
  have hdp := bounds (-H.p) hri
  have hdbr := bounds (-H.s) hbr
  have hddr := bounds (-2*H.s) hri
  have hddp := bounds (-H.p) hdi
  have hddbr := bounds (-H.s) hbd
  dsimp [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi,
    RoleLabel.outer,RoleLabel.eval,RoleLabel.d1,RoleLabel.d2]
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.GeneralReference
