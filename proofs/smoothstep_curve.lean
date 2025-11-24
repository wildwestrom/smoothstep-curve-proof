/-
# Smoothstep Curves: Infinitely Differentiable Curvature Functions

This file demonstrates the construction of smoothstep-based curvature functions that provide
$G^\infty$ continuous transitions from tangent lines to circular arcs.
The property of being infinitely differentiable may prove to be useful for engineering applications.

## Mathematical Framework

A smoothstep curve is defined by a curvature function κ(s) that smoothly transitions from 0
at the start to a target curvature R at the end. The key insight is to use a normalized
bump function to create this transition.

### General Form

For a smoothstep curve with:
- $s$ = arc length parameter (0 ≤ s ≤ L)
- $L$ = total length of the transition curve
- $R$ = target curvature (radius of circular arc)
- $G(t)$ = bump function on [0,1]

The curvature function is:
$$\kappa(s) = R \cdot F\left(\frac{s}{L}\right)$$

where $F(z)$ is the normalized integral of the bump function:
$$F(z) = \frac{\int_0^z G(t)\,dt}{\int_0^1 G(t)\,dt}$$

The heading angle is then:
$$\theta(s) = \int_0^s \kappa(v)\,dv = R \int_0^s F\left(\frac{v}{L}\right)\,dv$$

And the Cartesian coordinates are:
$$x(s) = \int_0^s \cos(\theta(v))\,dv, \quad y(s) = \int_0^s \sin(\theta(v))\,dv$$

### Key Properties

1. **Smoothness**: If G is C^∞ on [0,1], then κ is C^∞ on [0,L]
2. **Boundary Conditions**: κ(0) = 0, κ(L) = R
3. **Monotonicity**: F is monotonically increasing from 0 to 1
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.BumpFunction.Basic

noncomputable
section GenericFramework

open scoped ContDiff Topology
open MeasureTheory

/-
## Generic Framework for Smoothstep Curves

The following definitions and lemmas establish the mathematical foundation for constructing
smoothstep curves from any C^∞ bump function G on [0,1].
-/

lemma intervalIntegrable_on_unit_segment
  {f : ℝ → ℝ} {a b : ℝ} (hf : ContDiffOn ℝ ∞ f unitInterval)
  (ha : a ∈ unitInterval) (hb : b ∈ unitInterval) (hab : a ≤ b) :
  IntervalIntegrable f volume a b := by
  have hsubset : Set.Icc a b ⊆ unitInterval := by
    intro t ht
    exact ⟨le_trans ha.1 ht.1, le_trans ht.2 hb.2⟩
  have hcont : ContinuousOn f (Set.Icc a b) :=
    hf.continuousOn.mono hsubset
  exact hcont.intervalIntegrable_of_Icc (μ := volume) (a := a) (b := b) hab

lemma pos_on_subIoo_of_unit
  {f : ℝ → ℝ} {a b : ℝ}
  (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < f x) :
  ∀ t ∈ Set.Ioo a b, 0 < f t := by
  intro t ht
  have ht0 : 0 < t := lt_of_le_of_lt ha0 ht.1
  have ht1 : t < 1 := lt_of_lt_of_le ht.2 hb1
  exact hpos t ⟨ht0, ht1⟩

-- The standard primitive from 0: z ↦ ∫ t in (0)..z, f t.
def primitiveFromZero (f : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ t in (0)..z, f t

-- Fundamental result: the primitive z ↦ ∫_{0..z} f is C^∞ on [0,1] if f is C^∞ on [0,1]
lemma primitive_is_C_inf_on_unitInterval
  (f : ℝ → ℝ) (hfinf : ContDiffOn ℝ ∞ f unitInterval) :
  ContDiffOn ℝ ∞ (primitiveFromZero f) unitInterval := by
  classical
  have hmeas :
      ∀ x, StronglyMeasurableAtFilter f (𝓝[unitInterval] x) volume :=
    fun x =>
      hfinf.continuousOn.stronglyMeasurableAtFilter_nhdsWithin
        (hs := isClosed_Icc.measurableSet) x
  have h_deriv :
      ∀ x ∈ unitInterval, HasDerivWithinAt (primitiveFromZero f) (f x) unitInterval x := by
    intro x hx
    have hint : IntervalIntegrable f volume 0 x :=
      intervalIntegrable_on_unit_segment hfinf
        (show (0 : ℝ) ∈ unitInterval by exact ⟨le_rfl, by norm_num⟩) hx hx.1
    have hcont : ContinuousWithinAt f unitInterval x := hfinf.continuousOn.continuousWithinAt hx
    haveI : Fact (x ∈ Set.Icc (0 : ℝ) 1) := ⟨hx.1, hx.2⟩
    haveI : intervalIntegral.FTCFilter x (𝓝[unitInterval] x) (𝓝[unitInterval] x) := by
      simpa [unitInterval] using
        (inferInstance : intervalIntegral.FTCFilter x (𝓝[Set.Icc (0 : ℝ) 1] x)
          (𝓝[Set.Icc (0 : ℝ) 1] x))
    exact intervalIntegral.integral_hasDerivWithinAt_right (a := 0) (b := x) hint (hmeas x) hcont
  have h_diff : DifferentiableOn ℝ (primitiveFromZero f) unitInterval :=
    fun x hx => (h_deriv x hx).differentiableWithinAt
  have h_deriv_eq : ∀ x ∈ unitInterval, derivWithin (primitiveFromZero f) unitInterval x = f x :=
    fun x hx => (h_deriv x hx).derivWithin (uniqueDiffOn_Icc_zero_one x hx)
  exact (contDiffOn_infty_iff_derivWithin uniqueDiffOn_Icc_zero_one).mpr
    ⟨h_diff, (contDiffOn_congr h_deriv_eq).mpr hfinf⟩

-- Helper: convert uIoc integral to intervalIntegral
lemma uIoc_to_intervalIntegral (f : ℝ → ℝ) {z : ℝ} (hz : z ∈ unitInterval) :
  (∫ t in Set.uIoc 0 z, f t) = ∫ t in (0)..z, f t := by
  simpa [Set.uIoc, hz.1] using (intervalIntegral.integral_of_le (μ := volume) (f := f) (a := 0) (b := z) hz.1).symm

lemma uIoc_to_intervalIntegral_one (f : ℝ → ℝ) :
  (∫ t in Set.uIoc 0 1, f t) = ∫ t in (0)..1, f t := by
  simpa [Set.uIoc, le_rfl] using (intervalIntegral.integral_of_le (μ := volume) (f := f) (a := 0) (b := 1) (by norm_num)).symm

def clampUnit (z : ℝ) : ℝ := min (max z 0) 1

lemma clampUnit_mem_unitInterval (z : ℝ) : clampUnit z ∈ unitInterval := by
  refine ⟨?_, ?_⟩
  · have : 0 ≤ max z 0 := le_max_right _ _
    exact le_min this zero_le_one
  · exact min_le_right _ _

lemma clampUnit_of_mem {z : ℝ} (hz : z ∈ unitInterval) : clampUnit z = z := by
  have hz0 : 0 ≤ z := hz.1
  have hz1 : z ≤ 1 := hz.2
  simp [clampUnit, hz0, hz1]

lemma clampUnit_of_nonpos {z : ℝ} (hz : z ≤ 0) : clampUnit z = 0 := by
  simp [clampUnit, hz]

lemma clampUnit_of_one_le {z : ℝ} (hz : 1 ≤ z) : clampUnit z = 1 := by
  have hz0 : 0 ≤ z := le_trans zero_le_one hz
  simp [clampUnit, hz, hz0]

/-
### Core Definitions
-/

namespace Smooth

-- Numerator of the normalized integral: ∫₀ᶻ G(t) dt
def FNum (G : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in Set.uIoc 0 z, G t

-- Denominator of the normalized integral: ∫₀¹ G(t) dt
def FDen (G : ℝ → ℝ) : ℝ := ∫ t in Set.uIoc 0 1, G t

-- The normalized smoothstep function F(z) = FNum(clampUnit z) / FDen
def F (G : ℝ → ℝ) (z : ℝ) : ℝ := FNum G (clampUnit z) / FDen G

lemma FNum_zero (G : ℝ → ℝ) : FNum G 0 = 0 := by
  simp [FNum]

lemma FNum_one (G : ℝ → ℝ) : FNum G 1 = FDen G := by
  simp [FNum, FDen]

lemma F_zero (G : ℝ → ℝ) : F G 0 = 0 := by
  simp [F, FNum_zero, clampUnit_of_nonpos (show (0 : ℝ) ≤ 0 by rfl)]

lemma F_one (G : ℝ → ℝ) (hden : FDen G ≠ 0) : F G 1 = 1 := by
  have hclamp : clampUnit 1 = 1 :=
    clampUnit_of_mem (show (1 : ℝ) ∈ unitInterval by exact ⟨zero_le_one, le_rfl⟩)
  simp [F, hclamp, FNum_one, hden]

lemma FNum_contDiffOn
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval) :
  ContDiffOn ℝ ∞ (FNum G) unitInterval := by
  classical
  let P : ℝ → ℝ := primitiveFromZero G
  have hP : ContDiffOn ℝ ∞ P unitInterval :=
    primitive_is_C_inf_on_unitInterval G hG
  have h_congr : ∀ z ∈ unitInterval, FNum G z = P z := by
    intro z hz; simpa [FNum, P] using uIoc_to_intervalIntegral G hz
  exact ContDiffOn.congr_mono hP h_congr fun ⦃a⦄ a ↦ a

lemma FDen_pos
  {G : ℝ → ℝ} (hint : IntervalIntegrable G volume 0 1)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) :
  0 < FDen G := by
  have hposI : 0 < ∫ x in (0)..1, G x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (a:=0) (b:=1) (f:=G) hint hpos (by norm_num)
  rw [FDen, uIoc_to_intervalIntegral_one]
  exact hposI

lemma FNum_monotone_on_unit
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) :
  MonotoneOn (FNum G) unitInterval := by
  intro x hx y hy hxy
  classical
  by_cases hxy_eq : x = y
  · subst hxy_eq; exact le_rfl
  · have hlt : x < y := lt_of_le_of_ne hxy hxy_eq
    have hint_xy :
        IntervalIntegrable G volume x y :=
      intervalIntegrable_on_unit_segment hG hx hy hxy
    have h0x :
        IntervalIntegrable G volume 0 x :=
      intervalIntegrable_on_unit_segment hG
        (show (0 : ℝ) ∈ unitInterval by exact ⟨le_rfl, by norm_num⟩)
        hx hx.1
    have hpos_xy :
        ∀ t ∈ Set.Ioo x y, 0 < G t :=
      pos_on_subIoo_of_unit (f := G) hx.1 hy.2 hpos
    have hadd :
        (∫ t in (0)..x, G t) + (∫ t in (x)..y, G t) =
            (∫ t in (0)..y, G t) := by
      simpa using
        (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (f := G) (a := 0) (b := x) (c := y) h0x hint_xy)
    have hxInt : (∫ t in (0)..x, G t) = FNum G x := by
      simpa [FNum] using (uIoc_to_intervalIntegral G hx).symm
    have hyInt : (∫ t in (0)..y, G t) = FNum G y := by
      simpa [FNum] using (uIoc_to_intervalIntegral G hy).symm
    have hinc_nonneg : 0 ≤ ∫ t in (x)..y, G t := by
      have hpos_int :
          0 < ∫ t in (x)..y, G t :=
        intervalIntegral.intervalIntegral_pos_of_pos_on
          (a := x) (b := y) (f := G) hint_xy hpos_xy hlt
      exact hpos_int.le
    have hadd' : FNum G x + ∫ t in (x)..y, G t = FNum G y := by
      simpa [hxInt, hyInt] using hadd
    have hx_le_sum :
        FNum G x ≤ FNum G x + ∫ t in (x)..y, G t :=
      le_add_of_nonneg_right hinc_nonneg
    simpa [hadd'] using hx_le_sum

lemma F_eq_ratio_on_unit {G : ℝ → ℝ} {z : ℝ} (hz : z ∈ unitInterval) :
  F G z = FNum G z / FDen G := by
  simp [F, clampUnit_of_mem hz]

lemma F_monotone_on_unit
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) (hden : 0 < FDen G) :
  MonotoneOn (F G) unitInterval := by
  intro x hx y hy hxy
  have hxF : F G x = FNum G x / FDen G := F_eq_ratio_on_unit (G := G) hx
  have hyF : F G y = FNum G y / FDen G := F_eq_ratio_on_unit (G := G) hy
  have hFNum_mono : FNum G x ≤ FNum G y :=
    FNum_monotone_on_unit hG hpos hx hy hxy
  have := div_le_div_of_nonneg_right hFNum_mono hden.le
  simpa [hxF, hyF] using this

lemma F_contDiffOn
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval) :
  ContDiffOn ℝ ∞ (F G) unitInterval := by
  have hNum := FNum_contDiffOn hG
  have h : ContDiffOn ℝ ∞ (fun x => FNum G x / FDen G) unitInterval :=
    ContDiffOn.div_const hNum (FDen G)
  exact (contDiffOn_congr (fun x hx => F_eq_ratio_on_unit (G := G) hx)).mpr h

-- The curvature function κ(s) = R · F(s/L)
def kappa (G : ℝ → ℝ) (s R L : ℝ) : ℝ := R * F G (s / L)

lemma div_mem_unitInterval_of_mem_Icc {L : ℝ} (hL : 0 < L) {s : ℝ}
    (hs : s ∈ Set.Icc 0 L) : s / L ∈ unitInterval := by
  rcases hs with ⟨hs0, hsL⟩
  refine ⟨div_nonneg hs0 (le_of_lt hL), ?_⟩
  have hLne : L ≠ 0 := ne_of_gt hL
  have : s / L ≤ L / L := div_le_div_of_nonneg_right hsL (le_of_lt hL)
  simpa [div_self hLne] using this

lemma kappa_contDiffOn
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (R L : ℝ) (hL : 0 < L) :
  ContDiffOn ℝ ∞ (fun s => kappa G s R L) (Set.Icc 0 L) := by
  have hmap :
      ∀ ⦃s⦄, s ∈ Set.Icc 0 L → s / L ∈ unitInterval := by
    intro s hs
    exact div_mem_unitInterval_of_mem_Icc hL hs
  have hF : ContDiffOn ℝ ∞ (F G) unitInterval := F_contDiffOn hG
  have hcomp : ContDiffOn ℝ ∞ (fun s => F G (s / L)) (Set.Icc 0 L) :=
    hF.comp (contDiffOn_id.div_const L) (fun s hs => hmap hs)
  simpa [kappa] using contDiffOn_const.mul hcomp

/-
### SmoothstepCurve Structure

This structure encapsulates a complete smoothstep curve with all its properties.
-/

structure SmoothstepCurve where
  F : ℝ → ℝ
  κ : ℝ → ℝ → ℝ → ℝ
  F_is_C_inf : ContDiffOn ℝ ∞ F unitInterval
  κ_is_C_inf : ∀ R L (_ : 0 < L), ContDiffOn ℝ ∞ (fun s => κ s R L) (Set.Icc 0 L)
  κ_at_zero : ∀ R L, κ 0 R L = 0
  κ_at_L : ∀ R L (_ : L ≠ 0), κ L R L = R
  -- Monotonicity of the normalized smoothstep on [0,1].
  F_monotone_on_unit : MonotoneOn F unitInterval
  -- For nonnegative `R`, κ(·, R, L) is monotone on [0,L].
  κ_monotone_on_Icc : ∀ R L (_ : 0 < L) (_ : 0 ≤ R),
    MonotoneOn (fun s => κ s R L) (Set.Icc 0 L)

namespace SmoothstepCurve

variable (C : SmoothstepCurve)

@[simp] lemma contDiffOn_F : ContDiffOn ℝ ∞ C.F unitInterval :=
  C.F_is_C_inf

lemma contDiffOn_κ (R L : ℝ) (hL : 0 < L) :
    ContDiffOn ℝ ∞ (fun s => C.κ s R L) (Set.Icc 0 L) :=
  C.κ_is_C_inf R L hL

@[simp] lemma κ_at_zero' (R L : ℝ) : C.κ 0 R L = 0 :=
  C.κ_at_zero R L

@[simp] lemma κ_at_L' (R L : ℝ) (hL : L ≠ 0) : C.κ L R L = R :=
  C.κ_at_L R L hL

lemma monotoneOn_F : MonotoneOn C.F unitInterval :=
  C.F_monotone_on_unit

lemma κ_monotone_on_Icc' (R L : ℝ) (hL : 0 < L) (hR : 0 ≤ R) :
    MonotoneOn (fun s => C.κ s R L) (Set.Icc 0 L) :=
  C.κ_monotone_on_Icc R L hL hR

end SmoothstepCurve

def mkSmoothstepCurve (G : ℝ → ℝ) (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) : SmoothstepCurve :=
  let hfi : IntervalIntegrable G volume 0 1 :=
    hG.continuousOn.intervalIntegrable_of_Icc (μ := volume) (a := 0) (b := 1) (by norm_num)
  let hden : 0 < FDen G := FDen_pos hfi hpos
  {
    F := F G,
    κ := kappa G,
    F_is_C_inf := F_contDiffOn hG,
    κ_is_C_inf := fun R L hL => kappa_contDiffOn hG R L hL,
    κ_at_zero := fun R L => by simp [kappa, F_zero (G := G)],
    κ_at_L := fun R L hL => by
      have hden_ne : FDen G ≠ 0 := hden.ne'
      simp [kappa, div_self hL, F_one (G := G) hden_ne],
    F_monotone_on_unit := by
      exact F_monotone_on_unit hG hpos hden,
    κ_monotone_on_Icc := by
      intro R L hL hR x hx y hy hxy
      -- map to unit interval
      have hxmap : x / L ∈ unitInterval :=
        div_mem_unitInterval_of_mem_Icc hL hx
      have hymap : y / L ∈ unitInterval :=
        div_mem_unitInterval_of_mem_Icc hL hy
      have hxy_div : x / L ≤ y / L := div_le_div_of_nonneg_right hxy (le_of_lt hL)
      -- monotonicity of F on [0,1]
      have hFmono : MonotoneOn (F G) unitInterval :=
        F_monotone_on_unit hG hpos hden
      have hcmp := hFmono hxmap hymap hxy_div
      -- scale by nonnegative R
      simpa [kappa] using mul_le_mul_of_nonneg_left hcmp hR
  }

-- Helper to create smoothstep curve from any denominator function
def mkSmoothstepCurveFromDenom (denom : ℝ → ℝ) (hdenom_contDiff : ContDiff ℝ ∞ denom)
  (hdenom_pos : ∀ x ∈ Set.Ioo 0 1, 0 < denom x) : SmoothstepCurve :=
  let G := fun t => expNegInvGlue (denom t)
  let hG : ContDiffOn ℝ ∞ G unitInterval :=
    (expNegInvGlue.contDiff.comp hdenom_contDiff).contDiffOn
  let hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x :=
    fun x hx => expNegInvGlue.pos_of_pos (hdenom_pos x hx)
  mkSmoothstepCurve G hG hpos

end Smooth

end GenericFramework

/-
## Implementation 1: Standard Smoothstep Curve

Uses the classic smoothstep bump function G(t) = e^(-1/(t(1-t))).
Provides G^∞ continuous transition from tangent to circular arc.
-/

noncomputable
section SmoothstepCurve1

open scoped ContDiff Topology
open Smooth MeasureTheory

/-
### Implementation Details

Uses expNegInvGlue function from Mathlib for proper boundary conditions.
-/

-- The denominator function t(1-t) for the bump function
def denom_fn (t : ℝ) : ℝ := t * (1 - t)

lemma denom_contDiff : ContDiff ℝ ∞ denom_fn :=
  contDiff_id.mul (contDiff_const.sub contDiff_id)

lemma denom_pos_on_Ioo (t : ℝ) (ht : t ∈ Set.Ioo 0 1) : 0 < denom_fn t := by
  rcases ht with ⟨ht0, ht1⟩
  exact mul_pos ht0 (sub_pos.mpr ht1)


-- ### Construction and Main Results

-- The first smoothstep curve using the standard bump function
def curve1 := mkSmoothstepCurveFromDenom denom_fn denom_contDiff denom_pos_on_Ioo

-- The normalized smoothstep function for curve 1
def F₁ : ℝ → ℝ := curve1.F

-- The curvature function for curve 1
def κ₁ (s R L : ℝ) : ℝ := curve1.κ s R L

-- All smoothness, boundary, and monotonicity facts can be pulled from
-- `SmoothstepCurve` via lemmas such as
-- `SmoothstepCurve.contDiffOn_F curve1` or `SmoothstepCurve.κ_at_zero' curve1`.

end SmoothstepCurve1

/-
## Implementation 2: Improved Smoothstep Curve

Uses modified bump function G₂(t) = e^(-1/(1-(t-1)²)) with better performance characteristics:
- Smaller angular jerk and snap
- Shorter transition length for same deflection angle
- Better motion control performance
-/

noncomputable
section SmoothstepCurve2

open scoped ContDiff Topology
open Smooth MeasureTheory

/-
### Implementation Details

Uses expNegInvGlue with denominator function 1-(t-1)².
-/

-- The denominator function 1-(t-1)² for the improved bump function
def denom2 (t : ℝ) : ℝ := 1 - (t - 1)^2

lemma denom2_contDiff : ContDiff ℝ ∞ denom2 :=
  contDiff_const.sub ((contDiff_id.sub contDiff_const).pow 2)

-- Positivity of denom2 on (0,1): 1-(t-1)² > 0 when t ∈ (0,1)
lemma denom2_pos_on_Ioo (x : ℝ) (hx : x ∈ Set.Ioo 0 1) : 0 < denom2 x := by
  have habs : |x - 1| < 1 := by
    have h1 : -1 < x - 1 := by linarith [hx.1]
    have h2 : x - 1 < 1 := by linarith [hx.2]
    exact abs_lt.mpr ⟨by simpa [neg_one_mul] using h1, h2⟩
  have hsq : (x - 1)^2 < 1 := by
    have := (sq_lt_one_iff_abs_lt_one (a := x - 1)).mpr habs
    simpa [pow_two] using this
  have : 1 - (x - 1)^2 > 0 := sub_pos.mpr hsq
  simpa [denom2] using this

-- ### Construction and Main Results

-- The second smoothstep curve using the improved bump function
def curve2 := mkSmoothstepCurveFromDenom denom2 denom2_contDiff denom2_pos_on_Ioo

-- The normalized smoothstep function for curve 2
def F₂ : ℝ → ℝ := curve2.F

-- The curvature function for curve 2
def κ₂ (s R L : ℝ) : ℝ := curve2.κ s R L

-- Reuse the general `SmoothstepCurve` lemmas with `curve2` to access
-- differentiability, boundary, and monotonicity properties.

end SmoothstepCurve2
