module

public import SquaresInCircles.Eight.Words.Second.WordData

/-!
# Eight squares: exact arithmetic transfer at a single physical circle reference

The inputs bracket one coordinate and its one circle radical.  The
outputs are explicit rational formulas for the value and first two
derivatives of the target label.  This arithmetic lemma is used only
after the actual fixed reference has been established by circle squaring
and Taylor inequalities; it makes no assertion about a mesh of points.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.FixedReference

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def valueLo (bl bh _ul uh : ℝ) : ℝ :=
  167/10000+(121161/50000)*bl-(2867/3125)*bh^2-(95769/100000)*(uh-1/2)*bh
def valueHi (bl bh ul _uh : ℝ) : ℝ :=
  167/10000+(121161/50000)*bh-(2867/3125)*bl^2-(95769/100000)*(ul-1/2)*bl
def firstLo (bl bh _ul uh : ℝ) : ℝ :=
  121161/50000-(5734/3125)*bh-(95769/100000)*(uh-1/2)+
    (95769/100000)*bl*((bl+1/2)/uh)
def firstHi (bl bh ul _uh : ℝ) : ℝ :=
  121161/50000-(5734/3125)*bl-(95769/100000)*(ul-1/2)+
    (95769/100000)*bh*((bh+1/2)/ul)
def secondLo (bl _bh _ul uh : ℝ) : ℝ :=
  -5734/3125+(95769/50000)*((bl+1/2)/uh)+(95769/100000)*bl*(Q0/uh^3)
def secondHi (_bl bh ul _uh : ℝ) : ℝ :=
  -5734/3125+(95769/50000)*((bh+1/2)/ul)+(95769/100000)*bh*(Q0/ul^3)

lemma ratios {b bl bh ul uh : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hbox : b∈Icc bl bh) (hU : U b∈Icc ul uh) (hbl : 0≤bl) (hul : 1/2<ul) :
    (bl+1/2)/uh≤ratio b ∧ ratio b≤(bh+1/2)/ul ∧
      Q0/uh^3≤ratioD b ∧ ratioD b≤Q0/ul^3 := by
  have hu := U_positive (outer_domain hb)
  have hul0 : 0<ul := by linarith
  have huh0 : 0<uh := hu.trans_le hU.2
  have hrl : 0≤(bl+1/2)/uh := by positivity
  have hrh : 0≤(bh+1/2)/ul := by
    have hbh : 0≤bh := hbl.trans (hbox.1.trans hbox.2)
    positivity
  have hUlo3 := pow_le_pow_left₀ hul0.le hU.1 3
  have hUhi3 := pow_le_pow_left₀ hu.le hU.2 3
  refine ⟨?_,?_,?_,?_⟩
  · change (bl+1/2)/uh≤W b/U b
    apply (le_div_iff₀ hu).2
    have hm := mul_le_mul_of_nonneg_left hU.2 hrl
    have he : ((bl+1/2)/uh)*uh=bl+1/2 := by field_simp [huh0.ne']
    rw [he] at hm
    dsimp [W]
    linarith [hbox.1]
  · change W b/U b≤(bh+1/2)/ul
    apply (div_le_iff₀ hu).2
    have hm := mul_le_mul_of_nonneg_left hU.1 hrh
    have he : ((bh+1/2)/ul)*ul=bh+1/2 := by field_simp [hul0.ne']
    rw [he] at hm
    dsimp [W]
    nlinarith [hbox.2]
  · change Q0/uh^3≤Q0/(U b)^3
    apply (le_div_iff₀ (pow_pos hu 3)).2
    have hm := mul_le_mul_of_nonneg_left hUhi3
      (show 0≤Q0/uh^3 by norm_num [Q0]; positivity)
    have he : (Q0/uh^3)*uh^3=Q0 := by field_simp [huh0.ne']
    simpa only [he] using hm
  · change Q0/(U b)^3≤Q0/ul^3
    apply (div_le_iff₀ (pow_pos hu 3)).2
    have hm := mul_le_mul_of_nonneg_left hUlo3
      (show 0≤Q0/ul^3 by norm_num [Q0]; positivity)
    have he : (Q0/ul^3)*ul^3=Q0 := by field_simp [hul0.ne']
    rw [he] at hm
    nlinarith

theorem target {b bl bh ul uh : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hbox : b∈Icc bl bh) (hU : U b∈Icc ul uh) (hbl : 0≤bl) (hul : 1/2<ul) :
    valueLo bl bh ul uh≤T b ∧ T b≤valueHi bl bh ul uh ∧
      firstLo bl bh ul uh≤TLabel.d1 b ∧ TLabel.d1 b≤firstHi bl bh ul uh ∧
      secondLo bl bh ul uh≤TLabel.d2 b ∧ TLabel.d2 b≤ secondHi bl bh ul uh := by
  have hr := ratios hb hbox hU hbl hul
  have hul0 : 0<ul := by linarith
  have huh0 : 0<uh := (U_positive (outer_domain hb)).trans_le hU.2
  have hbh : 0≤bh := hb.1.trans hbox.2
  have harc0 : 0≤U b-1/2 := by linarith [hU.1]
  have harcH : 0≤uh-1/2 := by linarith [hU.1,hU.2]
  have hradL : 0≤(bl+1/2)/uh := by positivity
  have hr0 : 0≤ratio b := by linarith [(outer_ratio_bounds hb).1]
  have hD0 : 0≤ratioD b := (outer_ratio_bounds hb).2.2.1.le
  have hq : 0≤Q0 := by norm_num [Q0]
  have hb2lo := pow_le_pow_left₀ hbl hbox.1 2
  have hb2hi := pow_le_pow_left₀ hb.1 hbox.2 2
  have hablo := mul_le_mul (show ul-1/2≤U b-1/2 by linarith [hU.1]) hbox.1 hbl harc0
  have habhi := mul_le_mul (show U b-1/2≤uh-1/2 by linarith [hU.2]) hbox.2 hb.1 harcH
  have hbrlo := mul_le_mul hbox.1 hr.1 hradL hb.1
  have hbrhi := mul_le_mul hbox.2 hr.2.1 hr0 hbh
  have hbDlo := mul_le_mul hbox.1 hr.2.2.1 (by positivity : 0≤Q0/uh^3) hb.1
  have hbDhi := mul_le_mul hbox.2 hr.2.2.2 hD0 hbh
  have hv : T b=167/10000+(121161/50000)*b-(2867/3125)*b^2-
      (95769/100000)*(U b-1/2)*b := by
    dsimp [T,RoleLabel.outer,RoleLabel.eval,TLabel,U]
    ring
  have hd : TLabel.d1 b=121161/50000-(5734/3125)*b-
      (95769/100000)*(U b-1/2)+(95769/100000)*b*ratio b := by
    dsimp [RoleLabel.d1,TLabel,U]
    ring
  have hdd : TLabel.d2 b= -5734/3125+(95769/50000)*ratio b+
      (95769/100000)*b*ratioD b := by
    dsimp [RoleLabel.d2,TLabel]
    ring
  rw [hv,hd,hdd]
  dsimp only [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · linarith only [hbox.1,hb2hi,habhi]
  · linarith only [hbox.2,hb2lo,hablo]
  · linarith only [hbox.2,hU.2,hbrlo]
  · linarith only [hbox.1,hU.1,hbrhi]
  · linarith only [hr.1,hbDlo]
  · linarith only [hr.2.1,hbDhi]

end SquaresInCircles.Eight.SecondWord.FixedReference
