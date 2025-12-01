/-
# Smoothstep Curves: Infinitely Differentiable Curvature Functions

This file develops smoothstep-based curvature functions that provide
\(G^\infty\) continuous transitions between segments of constant curvature
(for example, between tangent lines and circular arcs).

The key design is fixed and permeates the entire development:

* We **always parameterize transitions by a bump function \(G\)** supported in \((0,1)\).
* The shape function \(H\) is *derived* — never assumed — as the normalized primitive of \(G\).
* Users stay in control of quantitative bounds (peak jerk, snap, …) by choosing the bump \(G\)
  that best fits their application.  The API intentionally avoids a single “canonical” smoothstep.

With this normalization the qualitative requirements on \(H\) (smooth, monotone, flat endpoints,
normalized) become automatic consequences of the properties of \(G\).

We keep all constructions \(C^\infty\) / \(G^\infty\)-smooth; no finite-order relaxation
is used anywhere.

## Mathematical Framework

A smoothstep curve is defined by a curvature function \(\kappa(s)\) that smoothly
transitions from a start curvature \(R₁\) to an end curvature \(R₂\):

* Straight line: \(Rᵢ = 0\).
* Circular arc: constant nonzero curvature \(Rᵢ\), with radius \(1 / |Rᵢ|\).

We work with a **shape function** \(H\) derived from a bump \(G\).  Conceptually:

* Choose a nonnegative bump \(G\) supported in \((0,1)\), \(C^\infty\), with
  \(\int_0^1 G = 1\).
* Define
  $$
  H(z) := \int_0^z G(t)\,dt,\quad z\in[0,1].
  $$
* Then \(H : [0,1] → [0,1]\) is smooth, monotone, and flat at the endpoints.

The implementation follows this viewpoint:

* `HInt G z` is the primitive \(\int_0^z G\).
* `HInt_denom G` is \(\int_0^1 G\), used for normalization.
* `H G z := HInt G (clampUnit z) / HInt_denom G` is the shape function
  exposed by the API.
* The curvature expression is given directly in terms of \(H\).

The user chooses \(G\) (bump shape) to control quantitative properties
(e.g., max of \(\kappa'\), \(\kappa''\), …); the framework guarantees the qualitative
properties (smoothness, flat joins, monotonic curvature change).

### General Form

For a smoothstep curve with:

* \(s\)  = arc length parameter with \(0 ≤ s ≤ L\)
* \(L\)  = total length of the transition curve
* \(R₁\) = start curvature (constant before the transition)
* \(R₂\) = end curvature (constant after the transition)
* \(z := s / L ∈ [0,1]\) = normalized arc-length parameter
* \(ΔR := R₂ - R₁\) = curvature change

we define the curvature on the transition segment by

$$
\kappa(s) = R₁ + ΔR \cdot H(s/L).
$$

where \(H : [0,1] → [0,1]\) is the shape function constructed from \(G\) as
above.

The heading angle is

$$
\theta(s)
= \int_0^s \kappa(v)\,dv
= R₁ s + ΔR\cdot L \int_0^{s/L} H(u)\,du.
$$

The Cartesian coordinates (arc length parametrization) are

$$
x(s) = \int_0^s \cos(\theta(v))\,dv,\quad
y(s) = \int_0^s \sin(\theta(v))\,dv.
$$

### Conditions on \(H\)

At the abstract level, we want a shape function
\(H : [0,1] → [0,1]\) with:

1. **Smoothness**:
   \(H ∈ C^\infty([0,1])\).

2. **Boundary values**:
   \(H(0) = 0,\quad H(1) = 1.\)

3. **Monotonicity**:
   \(H'(z) ≥ 0\) for all \(z ∈ [0,1]\).
   Then if \(ΔR > 0\), curvature increases, and if \(ΔR < 0\), curvature decreases.

4. **Flatness at endpoints**:
   \(H^{(n)}(0) = H^{(n)}(1) = 0\) for all \(n ≥ 1\).

These four properties imply that for \(0 ≤ s ≤ L\),

$$
\kappa^{(n)}(s) = ΔR \cdot L^{-n} \cdot H^{(n)}(s/L),
$$

so

$$
\kappa^{(n)}(0) = \kappa^{(n)}(L) = 0 \quad\text{for all } n ≥ 1.
$$

If we extend \(\kappa\) by constants \(R₁\) for \(s < 0\) and \(R₂\) for \(s > L\), we get a globally \(C^\infty\) curvature function with all derivatives matching at \(0\) and \(L\), i.e. \(G^\infty\) continuity at the joins. This matches the fact that tangents and circular arcs have constant curvature, so all of their curvature derivatives (order ≥ 1) vanish.

### Equivalence with the Bump-Function Framework

The implementation actually starts from a bump \(G\) and *derives* \(H\) from it. The key mathematical fact is:

*If \(H\) satisfies the four conditions above, then:*

* \(G := H'\) is a nonnegative \(C^\infty\) bump on \((0,1)\) with \(\int_0^1 G = 1\),

* and conversely, if \(G ≥ 0\) is a \(C^\infty\) bump with \(\int_0^1 G = 1\) and we set \(H(z) := \int_0^z G(t)\,dt\), then \(H\) satisfies (1)–(4).

Thus the four abstract conditions on \(H\) are exactly equivalent to saying:

> \(H\) is the normalized cumulative integral of a nonnegative \(C^\infty\) bump \(G\) supported in \((0,1)\).

In this file:

- The **generic framework** (`Smooth` namespace) formalizes the passage from `G` to `H` together with the curvature profile \(\kappa\).
- The **`SmoothstepCurve` structure** packages the resulting \(H\), the curvature \(\kappa\), and all accompanying properties (smoothness, flat joins, monotonicity).
- The constructors `mkSmoothstepCurve`, `mkSmoothstepCurveFromShape`, and `mkSmoothstepCurveFromDenom` give users multiple entry points for supplying their own bumps. In particular, `mkSmoothstepCurveFromDenom` turns *any* denominator function into a bump via `expNegInvGlue ∘ denom`, so the public API never fixes a single smoothstep.
- The implementations `curve1` and `curve2` demonstrate two concrete denominators with different quantitative trade-offs while still respecting the generic bump → shape → curvature pipeline.
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
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Topology.Order.DenselyOrdered

section GenericFramework

open ContDiff Topology
open MeasureTheory
open Filter

/-
## Generic Framework for Smoothstep Curves

The following definitions and lemmas establish the mathematical foundation for constructing
smoothstep curves from any C^∞ shape function H on [0,1] (or equivalently, from its derivative
G = H' which serves as a bump function in the implementation).
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

/-- A convenient `FTCFilter` instance for `𝓝[unitInterval]`. -/
private def ftcFilter_unitInterval {x : ℝ} (hx : x ∈ unitInterval) :
    intervalIntegral.FTCFilter x (𝓝[unitInterval] x) (𝓝[unitInterval] x) := by
  classical
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by simpa [unitInterval] using hx
  simpa [unitInterval] using
    (intervalIntegral.FTCFilter.nhdsIcc (x := x) (a := (0 : ℝ)) (b := (1 : ℝ))
      (h := ⟨hxIcc⟩))

-- The standard primitive from 0: z ↦ ∫ t in (0)..z, f t.
noncomputable def primitiveFromZero (f : ℝ → ℝ) : ℝ → ℝ :=
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
    have hFTC : intervalIntegral.FTCFilter x (𝓝[unitInterval] x) (𝓝[unitInterval] x) :=
      ftcFilter_unitInterval hx
    haveI : intervalIntegral.FTCFilter x (𝓝[unitInterval] x) (𝓝[unitInterval] x) := hFTC
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

def clampUnit (z : ℝ) : ℝ := min (max z 0) 1

lemma clampUnit_of_mem {z : ℝ} (hz : z ∈ unitInterval) : clampUnit z = z := by
  have hz0 : 0 ≤ z := hz.1
  have hz1 : z ≤ 1 := hz.2
  simp [clampUnit, hz0, hz1]

lemma clampUnit_of_nonpos {z : ℝ} (hz : z ≤ 0) : clampUnit z = 0 := by
  simp [clampUnit, hz]

/-
### Core Definitions
-/

namespace Smooth

-- Numerator of the normalized integral: ∫₀ᶻ H'(t) dt (where H' is the derivative of the shape function)
noncomputable def HInt (G : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in Set.uIoc 0 z, G t

-- Denominator of the normalized integral: ∫₀¹ H'(t) dt (normalization constant)
noncomputable def HInt_denom (G : ℝ → ℝ) : ℝ := ∫ t in Set.uIoc 0 1, G t

-- The shape function H(z) = HInt(clampUnit z) / HInt_denom
noncomputable def H (G : ℝ → ℝ) (z : ℝ) : ℝ := HInt G (clampUnit z) / HInt_denom G

lemma HInt_zero (G : ℝ → ℝ) : HInt G 0 = 0 := by
  simp [HInt]

lemma HInt_one (G : ℝ → ℝ) : HInt G 1 = HInt_denom G := by
  simp [HInt, HInt_denom]

lemma H_zero (G : ℝ → ℝ) : H G 0 = 0 := by
  simp [H, HInt_zero, clampUnit_of_nonpos (show (0 : ℝ) ≤ 0 by rfl)]

lemma H_one (G : ℝ → ℝ) (hden : HInt_denom G ≠ 0) : H G 1 = 1 := by
  have hclamp : clampUnit 1 = 1 :=
    clampUnit_of_mem (show (1 : ℝ) ∈ unitInterval by exact ⟨zero_le_one, le_rfl⟩)
  simp [H, hclamp, HInt_one, hden]

lemma HInt_contDiffOn
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval) :
  ContDiffOn ℝ ∞ (HInt G) unitInterval := by
  classical
  let P : ℝ → ℝ := primitiveFromZero G
  have hP : ContDiffOn ℝ ∞ P unitInterval :=
    primitive_is_C_inf_on_unitInterval G hG
  have h_congr : ∀ z ∈ unitInterval, HInt G z = P z := by
    intro z hz; simpa [HInt, P] using uIoc_to_intervalIntegral G hz
  exact ContDiffOn.congr_mono hP h_congr fun ⦃a⦄ a ↦ a

lemma HInt_denom_pos
  {G : ℝ → ℝ} (hint : IntervalIntegrable G volume 0 1)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) :
  0 < HInt_denom G := by
  have hposI : 0 < ∫ x in (0)..1, G x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (a:=0) (b:=1) (f:=G) hint hpos (by norm_num)
  rw [HInt_denom, uIoc_to_intervalIntegral G (show (1 : ℝ) ∈ unitInterval from ⟨zero_le_one, le_rfl⟩)]
  exact hposI

lemma HInt_monotone_on_unit
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) :
  MonotoneOn (HInt G) unitInterval := by
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
        ∀ t ∈ Set.Ioo x y, 0 < G t := by
      intro t ht
      have ht0 : 0 < t := lt_of_le_of_lt hx.1 ht.1
      have ht1 : t < 1 := lt_of_lt_of_le ht.2 hy.2
      exact hpos t ⟨ht0, ht1⟩
    have hadd :
        (∫ t in (0)..x, G t) + (∫ t in (x)..y, G t) =
            (∫ t in (0)..y, G t) := by
      simpa using
        (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (f := G) (a := 0) (b := x) (c := y) h0x hint_xy)
    have hxInt : (∫ t in (0)..x, G t) = HInt G x := by
      simpa [HInt] using (uIoc_to_intervalIntegral G hx).symm
    have hyInt : (∫ t in (0)..y, G t) = HInt G y := by
      simpa [HInt] using (uIoc_to_intervalIntegral G hy).symm
    have hinc_nonneg : 0 ≤ ∫ t in (x)..y, G t := by
      have hpos_int :
          0 < ∫ t in (x)..y, G t :=
        intervalIntegral.intervalIntegral_pos_of_pos_on
          (a := x) (b := y) (f := G) hint_xy hpos_xy hlt
      exact hpos_int.le
    have hadd' : HInt G x + ∫ t in (x)..y, G t = HInt G y := by
      simpa [hxInt, hyInt] using hadd
    have hx_le_sum :
        HInt G x ≤ HInt G x + ∫ t in (x)..y, G t :=
      le_add_of_nonneg_right hinc_nonneg
    simpa [hadd'] using hx_le_sum

lemma H_eq_ratio_on_unit {G : ℝ → ℝ} {z : ℝ} (hz : z ∈ unitInterval) :
  H G z = HInt G z / HInt_denom G := by
  simp [H, clampUnit_of_mem hz]

lemma H_monotone_on_unit
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) (hden : 0 < HInt_denom G) :
  MonotoneOn (H G) unitInterval := by
  intro x hx y hy hxy
  have hxH : H G x = HInt G x / HInt_denom G := H_eq_ratio_on_unit (G := G) hx
  have hyH : H G y = HInt G y / HInt_denom G := H_eq_ratio_on_unit (G := G) hy
  have hHInt_mono : HInt G x ≤ HInt G y :=
    HInt_monotone_on_unit hG hpos hx hy hxy
  have := div_le_div_of_nonneg_right hHInt_mono hden.le
  simpa [hxH, hyH] using this

lemma H_contDiffOn
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval) :
  ContDiffOn ℝ ∞ (H G) unitInterval := by
  have hNum := HInt_contDiffOn hG
  have h : ContDiffOn ℝ ∞ (fun x => HInt G x / HInt_denom G) unitInterval :=
    ContDiffOn.div_const hNum (HInt_denom G)
  exact (contDiffOn_congr (fun x hx => H_eq_ratio_on_unit (G := G) hx)).mpr h

private lemma H_eq_ratio_eqOn (G : ℝ → ℝ) :
    Set.EqOn (H G) (fun z => HInt G z / HInt_denom G) unitInterval := by
  intro z hz
  exact H_eq_ratio_on_unit (G := G) hz

lemma derivWithin_HInt_eq
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    {x : ℝ} (hx : x ∈ unitInterval) :
    derivWithin (HInt G) unitInterval x = G x := by
  classical
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hint : IntervalIntegrable G volume 0 x :=
    intervalIntegrable_on_unit_segment hG
      (show (0 : ℝ) ∈ unitInterval by exact ⟨le_rfl, by norm_num⟩) hx hx0
  have hcont : ContinuousWithinAt G unitInterval x :=
    hG.continuousOn.continuousWithinAt hx
  have hmeas :
      StronglyMeasurableAtFilter G (𝓝[unitInterval] x) volume :=
    hG.continuousOn.stronglyMeasurableAtFilter_nhdsWithin
      (hs := isClosed_Icc.measurableSet) x
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by simpa [unitInterval] using hx
  have hFTC :
      intervalIntegral.FTCFilter x (𝓝[unitInterval] x) (𝓝[unitInterval] x) :=
    ftcFilter_unitInterval hx
  haveI : intervalIntegral.FTCFilter x (𝓝[unitInterval] x) (𝓝[unitInterval] x) := hFTC
  have hEqOn :
      Set.EqOn (HInt G) (fun z => ∫ t in (0)..z, G t) unitInterval := by
    intro z hz
    simpa [HInt] using uIoc_to_intervalIntegral (f := G) hz
  have hHas :
      HasDerivWithinAt (fun z => ∫ t in (0)..z, G t) (G x) unitInterval x := by
    exact intervalIntegral.integral_hasDerivWithinAt_right
      (a := 0) (b := x) hint hmeas hcont
  have hDeriv :
      derivWithin (fun z => ∫ t in (0)..z, G t) unitInterval x = G x :=
    hHas.derivWithin (uniqueDiffOn_Icc_zero_one x hx)
  have hcongr :=
    derivWithin_congr hEqOn (by simpa using hEqOn hx)
  simpa using hcongr ▸ hDeriv

lemma iteratedDerivWithin_succ_HInt
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    {x : ℝ} (hx : x ∈ unitInterval) (n : ℕ) :
    iteratedDerivWithin (n + 1) (HInt G) unitInterval x =
      iteratedDerivWithin n G unitInterval x := by
  classical
  have hEq :
      Set.EqOn (derivWithin (HInt G) unitInterval) G unitInterval :=
    fun z hz => derivWithin_HInt_eq hG hz
  have hcongr :=
    (iteratedDerivWithin_congr (s := unitInterval)
        (f := derivWithin (HInt G) unitInterval) (g := G)
        (n := n) hEq) hx
  simpa [iteratedDerivWithin_succ'] using hcongr

lemma iteratedDerivWithin_succ_H
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    {x : ℝ} (hx : x ∈ unitInterval) (n : ℕ) :
    iteratedDerivWithin (n + 1) (H G) unitInterval x =
      (1 / HInt_denom G) *
        iteratedDerivWithin n G unitInterval x := by
  classical
  set c := (1 / HInt_denom G) with hc
  have hEq :
      Set.EqOn (H G) (fun z => c * HInt G z) unitInterval := by
    intro z hz
    have hclamp : clampUnit z = z := clampUnit_of_mem hz
    simp [H, hclamp, hc, div_eq_mul_inv, mul_comm]
  have hEq' :=
    (iteratedDerivWithin_congr (s := unitInterval)
        (f := H G) (g := fun z => c * HInt G z)
        (n := n + 1) hEq) hx
  have hcont :
      ContDiffWithinAt ℝ ((n : ℕ∞) + 1) (HInt G) unitInterval x :=
    ((HInt_contDiffOn hG).contDiffWithinAt hx).of_le
      (by
        have h : ((n : ℕ∞) + 1 : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
        exact_mod_cast h)
  have hconst :
      iteratedDerivWithin (n + 1) (fun z => c * HInt G z)
          unitInterval x
        = c *
          iteratedDerivWithin (n + 1) (HInt G) unitInterval x := by
    simpa using
      iteratedDerivWithin_const_mul (hx := hx)
        (h := uniqueDiffOn_Icc_zero_one)
        (c := c) (f := HInt G) (n := n + 1) hcont
  have hHInt :=
    iteratedDerivWithin_succ_HInt hG hx n
  calc
    iteratedDerivWithin (n + 1) (H G) unitInterval x
        = iteratedDerivWithin (n + 1) (fun z => c * HInt G z)
            unitInterval x := hEq'
    _ = c * iteratedDerivWithin (n + 1) (HInt G) unitInterval x := hconst
    _ = c * iteratedDerivWithin n G unitInterval x := by
      simpa using congrArg (fun t => c * t) hHInt
    _ = (1 / HInt_denom G) * iteratedDerivWithin n G unitInterval x := by
      simp [hc, div_eq_mul_inv, mul_comm]

lemma H_deriv_vanishes_at_point_from_G
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    {x : ℝ} (hx : x ∈ unitInterval)
    (hG_x : G x = 0)
    (hG_deriv_x :
      ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n G unitInterval x = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n (H G) unitInterval x = 0 := by
  classical
  intro n hn
  have hn0 : n ≠ 0 := by
    intro h
    have : 1 ≤ 0 := by simp [h] at hn
    exact Nat.not_succ_le_self 0 this
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hformula :=
    iteratedDerivWithin_succ_H hG hx k
  cases k with
  | zero =>
      simp [hformula, hG_x]
  | succ k =>
      have hk :
          iteratedDerivWithin (Nat.succ k) G unitInterval x = 0 :=
        hG_deriv_x _ (Nat.succ_pos _)
      simp [hformula, hk]

lemma H_deriv_vanishes_at_zero_from_G
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hG_zero : G 0 = 0)
    (hG_deriv_zero :
      ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n G unitInterval 0 = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n (H G) unitInterval 0 = 0 := by
  have hx0 : (0 : ℝ) ∈ unitInterval := ⟨le_rfl, by norm_num⟩
  exact H_deriv_vanishes_at_point_from_G hG hx0 hG_zero hG_deriv_zero

lemma H_deriv_vanishes_at_one_from_G
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hG_one : G 1 = 0)
    (hG_deriv_one :
      ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n G unitInterval 1 = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n (H G) unitInterval 1 = 0 := by
  have hx1 : (1 : ℝ) ∈ unitInterval := ⟨zero_le_one, le_rfl⟩
  exact H_deriv_vanishes_at_point_from_G hG hx1 hG_one hG_deriv_one

-- H maps to [0,1] on unitInterval
lemma H_mem_unitInterval
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) (hden : 0 < HInt_denom G)
  {z : ℝ} (hz : z ∈ unitInterval) :
  H G z ∈ unitInterval := by
  have hHmono := H_monotone_on_unit hG hpos hden
  have h0 : (0 : ℝ) ∈ unitInterval := ⟨le_rfl, by norm_num⟩
  have h1 : (1 : ℝ) ∈ unitInterval := ⟨zero_le_one, le_rfl⟩
  have hH0 : H G 0 = 0 := H_zero G
  have hH1 : H G 1 = 1 := H_one G hden.ne'
  have hz0 : 0 ≤ z := hz.1
  have hz1 : z ≤ 1 := hz.2
  have hH_z_ge_0 : 0 ≤ H G z := by
    have := hHmono h0 hz hz0
    rwa [hH0] at this
  have hH_z_le_1 : H G z ≤ 1 := by
    have := hHmono hz h1 hz1
    rwa [hH1] at this
  exact ⟨hH_z_ge_0, hH_z_le_1⟩

-- The curvature function κ(s) = R₁ + (R₂ - R₁) H(s/L)
noncomputable def kappaOfShape (H : ℝ → ℝ) (s R₁ R₂ L : ℝ) : ℝ :=
  R₁ + (R₂ - R₁) * H (s / L)

noncomputable def kappa (G : ℝ → ℝ) (s R₁ R₂ L : ℝ) : ℝ :=
  kappaOfShape (H G) s R₁ R₂ L

lemma div_mem_unitInterval_of_mem_Icc {L : ℝ} (hL : 0 < L) {s : ℝ}
    (hs : s ∈ Set.Icc 0 L) : s / L ∈ unitInterval := by
  rcases hs with ⟨hs0, hsL⟩
  refine ⟨div_nonneg hs0 (le_of_lt hL), ?_⟩
  have hLne : L ≠ 0 := ne_of_gt hL
  have : s / L ≤ L / L := div_le_div_of_nonneg_right hsL (le_of_lt hL)
  simpa [div_self hLne] using this

lemma kappaOfShape_contDiffOn
  {H : ℝ → ℝ} (hH : ContDiffOn ℝ ∞ H unitInterval)
  (R₁ R₂ L : ℝ) (hL : 0 < L) :
  ContDiffOn ℝ ∞ (fun s => kappaOfShape H s R₁ R₂ L) (Set.Icc 0 L) := by
  have hmap :
      ∀ ⦃s⦄, s ∈ Set.Icc 0 L → s / L ∈ unitInterval := by
    intro s hs
    exact div_mem_unitInterval_of_mem_Icc hL hs
  have hcomp : ContDiffOn ℝ ∞ (fun s => H (s / L)) (Set.Icc 0 L) :=
    hH.comp (contDiffOn_id.div_const L) (fun s hs => hmap hs)
  let g : ℝ → ℝ := fun s => (R₂ - R₁) * H (s / L)
  have hscale :
      ContDiffOn ℝ ∞ g (Set.Icc 0 L) :=
    contDiffOn_const.mul hcomp
  have hsum :
      ContDiffOn ℝ ∞ (fun s : ℝ => (fun _ : ℝ => R₁) s + g s)
        (Set.Icc 0 L) :=
    contDiffOn_const.add hscale
  have hsum' :
      ContDiffOn ℝ ∞ (fun s : ℝ => R₁ + g s)
        (Set.Icc 0 L) := by
    refine (contDiffOn_congr ?_).mp hsum
    intro x hx
    simp
  simpa [kappaOfShape, g, add_comm, add_left_comm, add_assoc] using hsum'

lemma kappa_contDiffOn
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (R₁ R₂ L : ℝ) (hL : 0 < L) :
  ContDiffOn ℝ ∞ (fun s => kappa G s R₁ R₂ L) (Set.Icc 0 L) := by
  simpa [kappa, kappaOfShape] using
    kappaOfShape_contDiffOn (H := H G) (R₁ := R₁) (R₂ := R₂)
      (L := L) (hH := H_contDiffOn hG) hL

lemma kappaOfShape_at_zero (H : ℝ → ℝ) (R₁ R₂ L : ℝ) (hH0 : H 0 = 0) :
    kappaOfShape H 0 R₁ R₂ L = R₁ := by
  simp [kappaOfShape, hH0]

lemma kappa_at_zero (G : ℝ → ℝ) (R₁ R₂ L : ℝ) :
    kappa G 0 R₁ R₂ L = R₁ := by
  simpa [kappa, kappaOfShape] using
    kappaOfShape_at_zero (H := H G) R₁ R₂ L (H_zero G)

lemma kappaOfShape_at_L
    (H : ℝ → ℝ) (R₁ R₂ L : ℝ) (hL : L ≠ 0) (hH1 : H 1 = 1) :
    kappaOfShape H L R₁ R₂ L = R₂ := by
  have hdiv : L / L = 1 := div_self hL
  simp [kappaOfShape, hdiv, hH1]

lemma kappa_at_L
    (G : ℝ → ℝ) (R₁ R₂ L : ℝ) (hL : L ≠ 0) (hden : HInt_denom G ≠ 0) :
    kappa G L R₁ R₂ L = R₂ := by
  simpa [kappa, kappaOfShape] using
    kappaOfShape_at_L (H := H G) R₁ R₂ L hL (H_one (G := G) hden)

-- Helper lemma for the common setup in monotonicity proofs
private lemma kappa_inequality_helper_of_shape
    {H : ℝ → ℝ} (hmono : MonotoneOn H unitInterval)
    (L : ℝ) (hL : 0 < L)
    (x y : ℝ) (hx : x ∈ Set.Icc 0 L) (hy : y ∈ Set.Icc 0 L) (hxy : x ≤ y) :
    H (x / L) ≤ H (y / L) := by
  have hxmap : x / L ∈ unitInterval :=
    div_mem_unitInterval_of_mem_Icc hL hx
  have hymap : y / L ∈ unitInterval :=
    div_mem_unitInterval_of_mem_Icc hL hy
  have hxy_div : x / L ≤ y / L :=
    div_le_div_of_nonneg_right hxy (le_of_lt hL)
  exact hmono hxmap hymap hxy_div

lemma kappaOfShape_monotone_on_Icc
    {H : ℝ → ℝ} (hHmono : MonotoneOn H unitInterval)
    (R₁ R₂ L : ℝ) (hL : 0 < L) (hmono : R₁ ≤ R₂) :
    MonotoneOn (fun s => kappaOfShape H s R₁ R₂ L) (Set.Icc 0 L) := by
  intro x hx y hy hxy
  have hcmp := kappa_inequality_helper_of_shape hHmono L hL x y hx hy hxy
  have hΔ : 0 ≤ R₂ - R₁ := sub_nonneg.mpr hmono
  have hscaled :
      (R₂ - R₁) * H (x / L) ≤ (R₂ - R₁) * H (y / L) :=
    mul_le_mul_of_nonneg_left hcmp hΔ
  have := add_le_add_left hscaled R₁
  simpa [kappaOfShape, add_comm, add_left_comm, add_assoc] using this

lemma kappa_monotone_on_Icc
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x)
    (R₁ R₂ L : ℝ) (hL : 0 < L) (hden : 0 < HInt_denom G) (hmono : R₁ ≤ R₂) :
    MonotoneOn (fun s => kappa G s R₁ R₂ L) (Set.Icc 0 L) := by
  have hmonoH := H_monotone_on_unit hG hpos hden
  simpa [kappa, kappaOfShape] using
    kappaOfShape_monotone_on_Icc (H := H G) (hHmono := hmonoH)
      (R₁ := R₁) (R₂ := R₂) (L := L) hL hmono

lemma kappaOfShape_antitone_on_Icc
    {H : ℝ → ℝ} (hHmono : MonotoneOn H unitInterval)
    (R₁ R₂ L : ℝ) (hL : 0 < L) (hmono : R₂ ≤ R₁) :
    AntitoneOn (fun s => kappaOfShape H s R₁ R₂ L) (Set.Icc 0 L) := by
  intro x hx y hy hxy
  have hcmp := kappa_inequality_helper_of_shape hHmono L hL x y hx hy hxy
  have hΔ : R₂ - R₁ ≤ 0 := sub_nonpos.mpr hmono
  have hscaled :
      (R₂ - R₁) * H (y / L) ≤ (R₂ - R₁) * H (x / L) :=
    mul_le_mul_of_nonpos_left hcmp hΔ
  have := add_le_add_left hscaled R₁
  simpa [kappaOfShape, add_comm, add_left_comm, add_assoc] using this

lemma kappa_antitone_on_Icc
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x)
    (R₁ R₂ L : ℝ) (hL : 0 < L) (hden : 0 < HInt_denom G) (hmono : R₂ ≤ R₁) :
    AntitoneOn (fun s => kappa G s R₁ R₂ L) (Set.Icc 0 L) := by
  have hmonoH := H_monotone_on_unit hG hpos hden
  simpa [kappa, kappaOfShape] using
    kappaOfShape_antitone_on_Icc (H := H G) (hHmono := hmonoH)
      (R₁ := R₁) (R₂ := R₂) (L := L) hL hmono

/-
### SmoothstepCurve Structure

This structure encapsulates a complete smoothstep curve with all its properties.
-/

structure SmoothstepCurve where
  H : ℝ → ℝ
  κ : ℝ → ℝ → ℝ → ℝ → ℝ
  H_is_C_inf : ContDiffOn ℝ ∞ H unitInterval
  H_zero : H 0 = 0
  H_one : H 1 = 1
  H_mem_unitInterval :
    ∀ ⦃z : ℝ⦄, z ∈ unitInterval → H z ∈ unitInterval
  κ_is_C_inf :
    ∀ R₁ R₂ L (_ : 0 < L),
      ContDiffOn ℝ ∞ (fun s => κ s R₁ R₂ L) (Set.Icc 0 L)
  κ_at_zero : ∀ R₁ R₂ L, κ 0 R₁ R₂ L = R₁
  κ_at_L : ∀ R₁ R₂ L (_ : L ≠ 0), κ L R₁ R₂ L = R₂
  κ_formula :
    ∀ s R₁ R₂ L, κ s R₁ R₂ L = R₁ + (R₂ - R₁) * H (s / L)
  -- Monotonicity of the shape function on [0,1].
  H_monotone_on_unit : MonotoneOn H unitInterval
  -- κ is monotone when R₁ ≤ R₂ and antitone when R₂ ≤ R₁.
  κ_monotone_on_Icc :
    ∀ R₁ R₂ L (_ : 0 < L) (_ : R₁ ≤ R₂),
      MonotoneOn (fun s => κ s R₁ R₂ L) (Set.Icc 0 L)
  κ_antitone_on_Icc :
    ∀ R₁ R₂ L (_ : 0 < L) (_ : R₂ ≤ R₁),
      AntitoneOn (fun s => κ s R₁ R₂ L) (Set.Icc 0 L)
  -- Flatness at boundaries: all derivatives (n ≥ 1) of H vanish at 0 and 1
  H_deriv_vanishes_at_zero : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n H unitInterval 0 = 0
  H_deriv_vanishes_at_one : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n H unitInterval 1 = 0

noncomputable def mkSmoothstepCurve (G : ℝ → ℝ) (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) (hG_zero : G 0 = 0) (hG_one : G 1 = 0)
  (hG_deriv_zero : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n G unitInterval 0 = 0)
  (hG_deriv_one : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n G unitInterval 1 = 0) : SmoothstepCurve :=
  let hfi : IntervalIntegrable G volume 0 1 :=
    hG.continuousOn.intervalIntegrable_of_Icc (μ := volume) (a := 0) (b := 1) (by norm_num)
  let hden : 0 < HInt_denom G := HInt_denom_pos hfi hpos
  {
    H := H G,
    κ := fun s R₁ R₂ L => kappa G s R₁ R₂ L,
    H_is_C_inf := H_contDiffOn hG,
    H_zero := H_zero G,
    H_one := H_one G hden.ne',
    H_mem_unitInterval := by
      intro z hz
      exact H_mem_unitInterval hG hpos hden hz,
    κ_is_C_inf := fun R₁ R₂ L hL => kappa_contDiffOn hG R₁ R₂ L hL,
    κ_at_zero := fun R₁ R₂ L => kappa_at_zero G R₁ R₂ L,
    κ_at_L := fun R₁ R₂ L hL => by
      have hden_ne : HInt_denom G ≠ 0 := hden.ne'
      exact kappa_at_L G R₁ R₂ L hL hden_ne,
    κ_formula := by
      intro s R₁ R₂ L
      simp [kappa, kappaOfShape],
    H_monotone_on_unit := by
      exact H_monotone_on_unit hG hpos hden,
    κ_monotone_on_Icc := by
      intro R₁ R₂ L hL hmono
      exact kappa_monotone_on_Icc hG hpos R₁ R₂ L hL hden hmono,
    κ_antitone_on_Icc := by
      intro R₁ R₂ L hL hmono
      exact kappa_antitone_on_Icc hG hpos R₁ R₂ L hL hden hmono,
    H_deriv_vanishes_at_zero :=
      H_deriv_vanishes_at_zero_from_G hG hG_zero hG_deriv_zero,
    H_deriv_vanishes_at_one :=
      H_deriv_vanishes_at_one_from_G hG hG_one hG_deriv_one
  }

/-- Constructor that takes an abstract shape function satisfying the four core properties. -/
noncomputable def mkSmoothstepCurveFromShape (H : ℝ → ℝ)
  (hH_smooth : ContDiffOn ℝ ∞ H unitInterval)
  (hH_zero : H 0 = 0) (hH_one : H 1 = 1)
  (hH_mem : ∀ ⦃z : ℝ⦄, z ∈ unitInterval → H z ∈ unitInterval)
  (hH_mono : MonotoneOn H unitInterval)
  (hH_deriv_zero : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n H unitInterval 0 = 0)
  (hH_deriv_one : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n H unitInterval 1 = 0) :
  SmoothstepCurve :=
  {
    H := H,
    κ := fun s R₁ R₂ L => kappaOfShape H s R₁ R₂ L,
    H_is_C_inf := hH_smooth,
    H_zero := hH_zero,
    H_one := hH_one,
    H_mem_unitInterval := by
      intro z hz
      exact hH_mem hz,
    κ_is_C_inf := by
      intro R₁ R₂ L hL
      exact kappaOfShape_contDiffOn (H := H) (hH := hH_smooth)
        (R₁ := R₁) (R₂ := R₂) (L := L) hL,
    κ_at_zero := by
      intro R₁ R₂ L
      exact kappaOfShape_at_zero (H := H) R₁ R₂ L hH_zero,
    κ_at_L := by
      intro R₁ R₂ L hL
      exact kappaOfShape_at_L (H := H) R₁ R₂ L hL hH_one,
    κ_formula := by
      intro s R₁ R₂ L
      simp [kappaOfShape],
    H_monotone_on_unit := hH_mono,
    κ_monotone_on_Icc := by
      intro R₁ R₂ L hL hmono
      exact kappaOfShape_monotone_on_Icc (H := H) (hHmono := hH_mono)
        (R₁ := R₁) (R₂ := R₂) (L := L) hL hmono,
    κ_antitone_on_Icc := by
      intro R₁ R₂ L hL hmono
      exact kappaOfShape_antitone_on_Icc (H := H) (hHmono := hH_mono)
        (R₁ := R₁) (R₂ := R₂) (L := L) hL hmono,
    H_deriv_vanishes_at_zero := hH_deriv_zero,
    H_deriv_vanishes_at_one := hH_deriv_one
  }

-- Helper lemmas for expNegInvGlue compositions
-- These show that H has vanishing derivatives when G = expNegInvGlue ∘ denom,
-- without requiring denom itself to vanish.

lemma slope_zero_of_left_const {f : ℝ → ℝ} (hf : ∀ x ≤ 0, f x = f 0) :
    (fun x => slope f 0 x) =ᶠ[𝓝[Set.Iio (0 : ℝ)] 0] fun _ => 0 :=
  Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => by
    have hfx : f x = f 0 := hf x (le_of_lt hx)
    simp [slope, hfx]

lemma iteratedDerivWithin_zero_fun_all {s : Set ℝ} {n : ℕ} :
    ∀ x, iteratedDerivWithin n (fun _ => (0 : ℝ)) s x = 0 := by
  intro x
  induction n generalizing x with
  | zero => simp [iteratedDerivWithin_zero]
  | succ n ih =>
    rw [iteratedDerivWithin_succ]
    have : iteratedDerivWithin n (fun _ => (0 : ℝ)) s = 0 := funext ih
    rw [this]
    simp

lemma iteratedDeriv_expNegInvGlue_nonpos :
    ∀ (n : ℕ) {x : ℝ}, x ≤ 0 → iteratedDeriv n expNegInvGlue x = 0 := by
  classical
  intro n
  induction n with
  | zero =>
    intro x hx
    exact expNegInvGlue.zero_of_nonpos hx
  | succ n hn =>
    intro x hx
    have hSucc :
        iteratedDeriv (n.succ) expNegInvGlue =
          deriv (iteratedDeriv n expNegInvGlue) :=
      iteratedDeriv_succ (n := n) (f := expNegInvGlue)
    rcases lt_or_eq_of_le hx with hxlt | rfl
    · have hxmem : x ∈ Set.Iio (0 : ℝ) := hxlt
      have hEq :
          Set.EqOn (iteratedDeriv n expNegInvGlue) (fun _ => (0 : ℝ)) (Set.Iio (0 : ℝ)) := by
        intro y hy
        exact hn (le_of_lt hy)
      have hopen : IsOpen (Set.Iio (0 : ℝ)) := isOpen_Iio
      have hDerivEq :
          Set.EqOn (deriv (iteratedDeriv n expNegInvGlue)) (deriv fun _ => (0 : ℝ))
            (Set.Iio (0 : ℝ)) :=
        Set.EqOn.deriv hEq hopen
      have hDerivZero :
          deriv (iteratedDeriv n expNegInvGlue) x = 0 := by
        have := hDerivEq hxmem
        simpa using this
      have hxval :=
        congrArg (fun g => g x) hSucc
      simp [hxval, hDerivZero]
    · have hconst :
          (fun x => slope (iteratedDeriv n expNegInvGlue) 0 x) =ᶠ[𝓝[Set.Iio (0 : ℝ)] 0]
            fun _ => (0 : ℝ) :=
        slope_zero_of_left_const fun y hy => by
          rw [hn hy, hn (x:=0) le_rfl]
      have hDiff :
          HasDerivAt (iteratedDeriv n expNegInvGlue)
            (iteratedDeriv (Nat.succ n) expNegInvGlue 0) 0 := by
        have hC :
            ContDiff ℝ (n + 1) expNegInvGlue :=
          (expNegInvGlue.contDiff.of_le (by
            have h : ((n + 1 : ℕ∞) ≤ (⊤ : ℕ∞)) := le_top
            exact_mod_cast h))
        have hd :
            Differentiable ℝ (iteratedDeriv n expNegInvGlue) :=
          ContDiff.differentiable_iteratedDeriv' (m := n) hC
        have hHas : HasDerivAt (iteratedDeriv n expNegInvGlue)
            (deriv (iteratedDeriv n expNegInvGlue) 0) 0 :=
          (hd 0).hasDerivAt
        simpa [iteratedDeriv_succ] using hHas
      have hmono :
          𝓝[Set.Iio (0 : ℝ)] 0 ≤ 𝓝[{x | x ≠ (0 : ℝ)}] 0 :=
        nhdsWithin_mono _ fun x hx => ne_of_lt hx
      have hLim :
          Filter.Tendsto (fun x => slope (iteratedDeriv n expNegInvGlue) 0 x)
            (𝓝[{x | x ≠ (0 : ℝ)}] 0)
            (𝓝 (iteratedDeriv (Nat.succ n) expNegInvGlue 0)) :=
        hDiff.tendsto_slope
      have hConstLim :
          Filter.Tendsto (fun x => slope (iteratedDeriv n expNegInvGlue) 0 x)
            (𝓝[Set.Iio (0 : ℝ)] 0) (𝓝 (0 : ℝ)) :=
        (tendsto_const_nhds : Filter.Tendsto (fun _ => (0 : ℝ)) _ _).congr' hconst.symm
      have hclosure :
          (0 : ℝ) ∈ closure (Set.Iio (0 : ℝ)) := by
        have : (0 : ℝ) ≤ 0 := le_rfl
        simp [closure_Iio, Set.Iic, Set.mem_setOf_eq]
      have hNeBot :
          NeBot (𝓝[Set.Iio (0 : ℝ)] (0 : ℝ)) :=
        mem_closure_iff_nhdsWithin_neBot.mp hclosure
      have hLim' := (hLim.mono_left hmono)
      haveI : NeBot (𝓝[Set.Iio (0 : ℝ)] (0 : ℝ)) := hNeBot
      have :=
        tendsto_nhds_unique hLim' hConstLim
      simpa using this

lemma iteratedDeriv_expNegInvGlue_zero (n : ℕ) :
    iteratedDeriv n expNegInvGlue 0 = 0 :=
  iteratedDeriv_expNegInvGlue_nonpos n le_rfl

lemma iteratedDeriv_comp_expNegInvGlue_at
    {denom : ℝ → ℝ} (hdenom : ContDiff ℝ ∞ denom)
    {a : ℝ} (ha : denom a = 0) :
    ∀ n : ℕ, iteratedDeriv n (fun t => expNegInvGlue (denom t)) a = 0 := by
  classical
  intro n
  have hgAt :
      ContDiffAt ℝ (⊤ : ℕ∞) expNegInvGlue (denom a) :=
    expNegInvGlue.contDiff.contDiffAt
  have hfAt : ContDiffAt ℝ (⊤ : ℕ∞) denom a :=
    hdenom.contDiffAt
  have hsum :=
    iteratedDeriv_comp_eq_sum_orderedFinpartition
      (n := (⊤ : ℕ∞))
      (hi := by
        have h : (n : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
        exact_mod_cast h)
      (g := expNegInvGlue) (f := denom) (x := a)
      (hg := hgAt) (hf := hfAt)
  have hzero :
      ∀ c : OrderedFinpartition n,
        iteratedDeriv c.length expNegInvGlue (denom a) = 0 := by
    intro c
    simpa [ha] using iteratedDeriv_expNegInvGlue_zero (c.length)
  simpa [Function.comp, hzero] using hsum


lemma iteratedDerivWithin_expNegInvGlue_comp_of_mem
    {denom : ℝ → ℝ} (hdenom : ContDiff ℝ ∞ denom)
    {a : ℝ} (ha : denom a = 0) (ha_mem : a ∈ unitInterval) :
    ∀ n : ℕ, iteratedDerivWithin n (fun t => expNegInvGlue (denom t)) unitInterval a = 0 := by
  intro n
  have hcontTop :
      ContDiffAt ℝ (⊤ : ℕ∞) (fun t => expNegInvGlue (denom t)) a :=
    (expNegInvGlue.contDiff.comp hdenom).contDiffAt
  have hcont :
      ContDiffAt ℝ n (fun t => expNegInvGlue (denom t)) a := by
    have h : (n : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    simpa using hcontTop.of_le (by exact_mod_cast h)
  have hs : UniqueDiffOn ℝ unitInterval := by
    simpa [unitInterval] using uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)
  have hEq :
      iteratedDerivWithin n (fun t => expNegInvGlue (denom t)) unitInterval a =
        iteratedDeriv n (fun t => expNegInvGlue (denom t)) a :=
    iteratedDerivWithin_eq_iteratedDeriv (hs := hs) (h := hcont) (hx := ha_mem)
  have hzero := iteratedDeriv_comp_expNegInvGlue_at hdenom ha n
  simpa [hEq] using hzero

lemma H_deriv_vanishes_at_endpoint_expNegInvGlue_comp
  {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
  {a : ℝ} (ha_mem : a ∈ unitInterval) (ha_zero : denom a = 0) :
  ∀ n : ℕ, n ≥ 1 →
      iteratedDerivWithin n (H (fun t => expNegInvGlue (denom t))) unitInterval a = 0 := by
  let G := fun t => expNegInvGlue (denom t)
  have hG : ContDiffOn ℝ ∞ G unitInterval :=
    (expNegInvGlue.contDiff.comp hdenom_contDiff).contDiffOn
  intro n hn
  by_cases hden : HInt_denom G = 0
  · have hH : ∀ x, H G x = 0 := by simp [H, hden]
    rw [iteratedDerivWithin_congr (f := H G) (g := fun _ => 0) (s := unitInterval) (n := n) (by intro x hx; exact hH x)]
    · apply iteratedDerivWithin_zero_fun_all
    · simpa [unitInterval] using ha_mem
  · have hvan :=
      H_deriv_vanishes_at_point_from_G hG ha_mem
        (by simp [G, ha_zero, expNegInvGlue.zero])
        (by
          intro k hk
          exact
            iteratedDerivWithin_expNegInvGlue_comp_of_mem
              hdenom_contDiff ha_zero ha_mem k)
    exact hvan n hn

lemma H_deriv_vanishes_at_zero_expNegInvGlue_comp
  {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
  (hdenom_zero : denom 0 = 0) :
  ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n (H (fun t => expNegInvGlue (denom t))) unitInterval 0 = 0 := by
  have hmem : (0 : ℝ) ∈ unitInterval := ⟨le_rfl, by norm_num⟩
  exact
    H_deriv_vanishes_at_endpoint_expNegInvGlue_comp hdenom_contDiff hmem hdenom_zero

lemma H_deriv_vanishes_at_one_expNegInvGlue_comp
  {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
  (hdenom_one : denom 1 = 0) :
  ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n (H (fun t => expNegInvGlue (denom t))) unitInterval 1 = 0 := by
  have hmem : (1 : ℝ) ∈ unitInterval := ⟨zero_le_one, le_rfl⟩
  exact
    H_deriv_vanishes_at_endpoint_expNegInvGlue_comp hdenom_contDiff hmem hdenom_one

-- Helper to create smoothstep curve from any denominator function
noncomputable def mkSmoothstepCurveFromDenom (denom : ℝ → ℝ) (hdenom_contDiff : ContDiff ℝ ∞ denom)
  (hdenom_pos : ∀ x ∈ Set.Ioo 0 1, 0 < denom x) (hdenom_zero : denom 0 = 0) (hdenom_one : denom 1 = 0) : SmoothstepCurve :=
  let G := fun t => expNegInvGlue (denom t)
  let hG : ContDiffOn ℝ ∞ G unitInterval :=
    (expNegInvGlue.contDiff.comp hdenom_contDiff).contDiffOn
  let hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x :=
    fun x hx => expNegInvGlue.pos_of_pos (hdenom_pos x hx)
  let hfi : IntervalIntegrable G volume 0 1 :=
    hG.continuousOn.intervalIntegrable_of_Icc (μ := volume) (a := 0) (b := 1) (by norm_num)
  let hden : 0 < HInt_denom G := HInt_denom_pos hfi hpos
  {
    H := H G,
    κ := fun s R₁ R₂ L => kappa G s R₁ R₂ L,
    H_is_C_inf := H_contDiffOn hG,
    H_zero := H_zero G,
    H_one := H_one G hden.ne',
    H_mem_unitInterval := by
      intro z hz
      exact H_mem_unitInterval hG hpos hden hz,
    κ_is_C_inf := fun R₁ R₂ L hL => kappa_contDiffOn hG R₁ R₂ L hL,
    κ_at_zero := fun R₁ R₂ L => kappa_at_zero G R₁ R₂ L,
    κ_at_L := fun R₁ R₂ L hL => by
      have hden_ne : HInt_denom G ≠ 0 := hden.ne'
      exact kappa_at_L G R₁ R₂ L hL hden_ne,
    κ_formula := by
      intro s R₁ R₂ L
      simp [kappa, kappaOfShape],
    H_monotone_on_unit := H_monotone_on_unit hG hpos hden,
    κ_monotone_on_Icc := fun R₁ R₂ L hL hmono =>
      kappa_monotone_on_Icc hG hpos R₁ R₂ L hL hden hmono,
    κ_antitone_on_Icc := fun R₁ R₂ L hL hmono =>
      kappa_antitone_on_Icc hG hpos R₁ R₂ L hL hden hmono,
    H_deriv_vanishes_at_zero := H_deriv_vanishes_at_zero_expNegInvGlue_comp hdenom_contDiff hdenom_zero,
    H_deriv_vanishes_at_one := H_deriv_vanishes_at_one_expNegInvGlue_comp hdenom_contDiff hdenom_one
  }

structure DenomParams where
  denom : ℝ → ℝ
  contDiff : ContDiff ℝ ∞ denom
  pos_on_Ioo : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < denom x
  zero : denom 0 = 0
  one : denom 1 = 0

noncomputable def curveFrom (p : DenomParams) : SmoothstepCurve :=
  mkSmoothstepCurveFromDenom p.denom p.contDiff p.pos_on_Ioo p.zero p.one

end Smooth

end GenericFramework

/-
## Standard Smoothstep Curve

This section keeps the generic “parameterize by `G`” design but instantiates it
with the classical bump
```
G₁ z = expNegInvGlue (z * (1 - z)).
```
On the open interval `(0,1)` this coincides with `exp (-1 / (z (1 - z)))`, so it
is strictly positive there, integrates to a positive finite constant, and every
iterated derivative of `G₁` vanishes at `z = 0` and `z = 1`.  The exported shape
is still the normalized primitive `H G₁`, so downstream applications remain free
to swap in different bumps when tighter high-order derivative bounds are needed.
-/

section CanonicalSmoothstep

open scoped ContDiff Topology
open Smooth MeasureTheory

/-
### Canonical Smoothstep

Relies on `expNegInvGlue` to glue every derivative to zero at the endpoints.
-/

-- Canonical denominator z(1 - z) used in the base bump
def denomCanonical (z : ℝ) : ℝ := z * (1 - z)

lemma denomCanonical_contDiff : ContDiff ℝ ∞ denomCanonical :=
  contDiff_id.mul (contDiff_const.sub contDiff_id)

lemma denomCanonical_pos_on_Ioo (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
    0 < denomCanonical t := by
  rcases ht with ⟨ht0, ht1⟩
  exact mul_pos ht0 (sub_pos.mpr ht1)

-- Canonical denominator vanishes at both endpoints
lemma denomCanonical_fn_zero : denomCanonical 0 = 0 := by simp [denomCanonical]
lemma denomCanonical_fn_one : denomCanonical 1 = 0 := by simp [denomCanonical]

-- Resulting bump vanishes at both endpoints
lemma G₁_zero : (fun t => expNegInvGlue (denomCanonical t)) 0 = 0 := by
  simp [denomCanonical_fn_zero, expNegInvGlue.zero_of_nonpos (le_refl 0)]

lemma G₁_one : (fun t => expNegInvGlue (denomCanonical t)) 1 = 0 := by
  simp [denomCanonical_fn_one, expNegInvGlue.zero_of_nonpos (le_refl 0)]

noncomputable def curveCanonical : SmoothstepCurve :=
  mkSmoothstepCurveFromDenom denomCanonical denomCanonical_contDiff denomCanonical_pos_on_Ioo denomCanonical_fn_zero denomCanonical_fn_one

end CanonicalSmoothstep

/-
## Parametric Families of Denominators
-/

section ParametricDenominators

open scoped ContDiff Topology
open Smooth MeasureTheory

variable (a : ℝ)

/-
Here we simply rescale the denominator with a single coefficient `a` and pick
```
G₂ z = expNegInvGlue (az(1 - z)),
```
for some positive parameter `a`. Inside `(0,1)` this behaves like
`exp (-1 / (a z (1 - z)))`, while `expNegInvGlue` glues the bump (and every derivative)
to zero at the endpoints. Normalizing the primitive once again gives the shape `H G₂`,
so the public API is unchanged even though this particular bump can yield smaller
jerk/snap bounds in practice.
-/

def denomScaled (z : ℝ) : ℝ := a * z * (1 - z)

lemma denomScaled_contDiff : ContDiff ℝ ∞ (denomScaled a) :=
  (contDiff_const.mul contDiff_id).mul (contDiff_const.sub contDiff_id)

lemma denomScaled_pos_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo 0 1) (ha : 0 < a) :
    0 < denomScaled a x := by
  rcases hx with ⟨hx0, hx1⟩
  have hx_pos : 0 < x := hx0
  have h1x_pos : 0 < 1 - x := sub_pos.mpr hx1
  have : 0 < a * x * (1 - x) := by
    exact mul_pos (mul_pos ha hx_pos) h1x_pos
  simpa [denomScaled] using this

lemma denomScaled_zero : denomScaled a 0 = 0 := by
  simp [denomScaled]

lemma denomScaled_one : denomScaled a 1 = 0 := by
  simp [denomScaled]

noncomputable def curveScaled (ha : 0 < a) : SmoothstepCurve :=
  mkSmoothstepCurveFromDenom (denomScaled a) (denomScaled_contDiff a)
    (fun {x} hx => denomScaled_pos_on_Ioo (a := a) (x := x) hx ha) (denomScaled_zero a) (denomScaled_one a)

/-
Now we tweak it further by adding asymmetric powers of `p` and `q`
```
G(z) = expNegInvGlue (az^p(1 - z)^q)
```
-/

def denomPow (a : ℝ) (p q : ℕ) (z : ℝ) : ℝ :=
  a * z ^ p * (1 - z) ^ q

lemma denomPow_contDiff (a : ℝ) (p q : ℕ) : ContDiff ℝ ∞ (denomPow a p q) := by
  have hz_pow : ContDiff ℝ ∞ (fun z : ℝ => z ^ p) := by
    simpa using contDiff_id.pow p
  have h1_pow : ContDiff ℝ ∞ (fun z : ℝ => (1 - z) ^ q) := by
    simpa using (contDiff_const.sub contDiff_id).pow q
  have hconst : ContDiff ℝ ∞ (fun _ : ℝ => a) := contDiff_const
  have hprod := (hconst.mul hz_pow).mul h1_pow
  simpa [denomPow] using hprod

lemma denomPow_pos_on_Ioo {a : ℝ} {p q : ℕ} (ha : 0 < a) :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (0 : ℝ) 1 → 0 < denomPow a p q x := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have hx_pos : 0 < x := hx0
  have h1x_pos : 0 < 1 - x := sub_pos.mpr hx1
  have hz := pow_pos hx_pos p
  have h1z := pow_pos h1x_pos q
  exact mul_pos (mul_pos ha hz) h1z

lemma denomPow_zero {a : ℝ} {p q : ℕ} (hp : 0 < p) :
    denomPow a p q 0 = 0 := by
  cases p with
  | zero => cases hp
  | succ p' =>
      simp [denomPow]

lemma denomPow_one {a : ℝ} {p q : ℕ} (hq : 0 < q) :
    denomPow a p q 1 = 0 := by
  cases q with
  | zero => cases hq
  | succ q' =>
      simp [denomPow]

def denomPowParams {a : ℝ} {p q : ℕ} (ha : 0 < a) (hp : 0 < p) (hq : 0 < q) :
    DenomParams where
  denom := denomPow a p q
  contDiff := denomPow_contDiff a p q
  pos_on_Ioo := denomPow_pos_on_Ioo (a := a) (p := p) (q := q) ha
  zero := denomPow_zero (a := a) (p := p) (q := q) hp
  one := denomPow_one (a := a) (p := p) (q := q) hq

noncomputable def curvePow {a : ℝ} {p q : ℕ} (ha : 0 < a) (hp : 0 < p) (hq : 0 < q) :
    SmoothstepCurve :=
  curveFrom (denomPowParams (a := a) (p := p) (q := q) ha hp hq)

-- Polynomial bump denominator with an affine skew term
def denomPoly (α β : ℝ) (z : ℝ) : ℝ :=
  (z * (1 - z)) * (α + β * z)

lemma denomPoly_contDiff (α β : ℝ) : ContDiff ℝ ∞ (denomPoly α β) := by
  have h1 : ContDiff ℝ ∞ (fun z : ℝ => z * (1 - z)) := by
    simpa [denomCanonical] using denomCanonical_contDiff
  have h2 : ContDiff ℝ ∞ (fun z : ℝ => α + β * z) :=
    (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hprod :
      ContDiff ℝ ∞ (fun z : ℝ => (z * (1 - z)) * (α + β * z)) :=
    h1.mul h2
  simpa [denomPoly] using hprod

lemma denomPoly_pos_on_Ioo {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (0 : ℝ) 1 → 0 < denomPoly α β x := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have hbase : 0 < x * (1 - x) := mul_pos hx0 (sub_pos.mpr hx1)
  have hβx : 0 ≤ β * x := mul_nonneg hβ hx0.le
  have hlin : 0 < α + β * x := by
    have hαle : α ≤ α + β * x := by
      have := add_le_add_left hβx α
      simpa using this
    exact lt_of_lt_of_le hα hαle
  have := mul_pos hbase hlin
  simpa [denomPoly] using this

lemma denomPoly_zero (α β : ℝ) : denomPoly α β 0 = 0 := by
  simp [denomPoly]

lemma denomPoly_one (α β : ℝ) : denomPoly α β 1 = 0 := by
  simp [denomPoly]

def denomPolyParams {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) : DenomParams where
  denom := denomPoly α β
  contDiff := denomPoly_contDiff α β
  pos_on_Ioo := denomPoly_pos_on_Ioo hα hβ
  zero := denomPoly_zero α β
  one := denomPoly_one α β

noncomputable def curvePoly {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) : SmoothstepCurve :=
  curveFrom (denomPolyParams (α := α) (β := β) hα hβ)

end ParametricDenominators

/-
## Reparametrization
-/

noncomputable
section Reparametrization

open scoped ContDiff
open Smooth

namespace Smooth

lemma iteratedDerivWithin_comp_vanish_of_flat
    {g φ : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g unitInterval)
    (hφ : ContDiffOn ℝ ∞ φ unitInterval)
    (hmap : Set.MapsTo φ unitInterval unitInterval)
    {a : ℝ} (ha : a ∈ unitInterval)
    (hflat : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n φ unitInterval a = 0) :
    ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n (fun z => g (φ z)) unitInterval a = 0 := by
  intro n hn
  classical
  have hs : UniqueDiffOn ℝ unitInterval :=
    uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)
  have ha_image : φ a ∈ unitInterval := hmap ha
  have hginf :
      ContDiffWithinAt ℝ ((n : ℕ∞)) g unitInterval (φ a) :=
    ((hg.contDiffWithinAt ha_image).of_le (by
      exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞))))
  have hφinf :
      ContDiffWithinAt ℝ ((n : ℕ∞)) φ unitInterval a :=
    ((hφ.contDiffWithinAt ha).of_le (by
      exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞))))
  have hsum :=
    iteratedDerivWithin_comp_eq_sum_orderedFinpartition
      (hg := hginf) (hf := hφinf) (ht := hs) (hs := hs)
      (hx := ha) (hst := hmap) (hi := le_rfl)
  have hpos : 0 < n := Nat.succ_le_iff.mp hn
  have hparts :
      ∀ c : OrderedFinpartition n,
        ∏ j : Fin c.length,
            iteratedDerivWithin (c.partSize j) φ unitInterval a = 0 := by
    intro c
    have hlen : 0 < c.length := c.length_pos hpos
    classical
    have hfactor :
        ∀ j : Fin c.length,
          iteratedDerivWithin (c.partSize j) φ unitInterval a = 0 := by
      intro j
      have hjpos : 1 ≤ c.partSize j := Nat.succ_le_of_lt (c.partSize_pos j)
      exact hflat _ hjpos
    classical
    have hprod :
        ((Finset.univ : Finset (Fin c.length)).prod fun j =>
            iteratedDerivWithin (c.partSize j) φ unitInterval a : ℝ) = 0 := by
      refine
        Finset.prod_eq_zero
          (s := (Finset.univ : Finset (Fin c.length)))
          (f := fun j => iteratedDerivWithin (c.partSize j) φ unitInterval a)
          (i := ⟨0, hlen⟩) ?_ ?_
      · simp
      · simpa using hfactor ⟨0, hlen⟩
    simpa using hprod
  have hterm :
      ∀ c : OrderedFinpartition n,
        iteratedDerivWithin c.length g unitInterval (φ a)
            * ∏ j, iteratedDerivWithin (c.partSize j) φ unitInterval a = 0 := by
    intro c
    simp [hparts c]
  have hsimp :
      ∑ c : OrderedFinpartition n,
        iteratedDerivWithin c.length g unitInterval (φ a)
            * ∏ j : Fin c.length,
                iteratedDerivWithin (c.partSize j) φ unitInterval a = 0 := by
    classical
    refine Finset.sum_eq_zero ?_
    intro c _
    exact hterm c
  simpa using hsum.trans hsimp

def reparam (base : SmoothstepCurve) (φ : ℝ → ℝ)
    (hφ_smooth : ContDiffOn ℝ ∞ φ unitInterval)
    (hφ_mem : ∀ ⦃z : ℝ⦄, z ∈ unitInterval → φ z ∈ unitInterval)
    (hφ_zero : φ 0 = 0) (hφ_one : φ 1 = 1)
    (hφ_mono : MonotoneOn φ unitInterval)
    (hφ_flat_zero : ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n φ unitInterval 0 = 0)
    (hφ_flat_one : ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n φ unitInterval 1 = 0) :
    SmoothstepCurve := by
  classical
  let Hφ : ℝ → ℝ := fun z => base.H (φ z)
  have hmaps : Set.MapsTo φ unitInterval unitInterval := fun z hz => hφ_mem hz
  have hz0 : (0 : ℝ) ∈ unitInterval := ⟨le_rfl, by norm_num⟩
  have hz1 : (1 : ℝ) ∈ unitInterval := ⟨zero_le_one, le_rfl⟩
  refine mkSmoothstepCurveFromShape
    Hφ
    ?smooth ?H0 ?H1 ?Hmem ?Hmono ?Hflat0 ?Hflat1
  · have hcomp :
        ContDiffOn ℝ ∞ (fun z => base.H (φ z)) unitInterval :=
      base.H_is_C_inf.comp hφ_smooth fun z hz => hφ_mem hz
    simpa [Hφ] using hcomp
  · simp [Hφ, hφ_zero, base.H_zero]
  · simp [Hφ, hφ_one, base.H_one]
  · intro z hz
    exact base.H_mem_unitInterval (hφ_mem hz)
  · intro x hx y hy hxy
    exact base.H_monotone_on_unit (hφ_mem hx) (hφ_mem hy) (hφ_mono hx hy hxy)
  · intro n hn
    have := iteratedDerivWithin_comp_vanish_of_flat
      (g := base.H) (φ := φ)
      base.H_is_C_inf hφ_smooth hmaps hz0 hφ_flat_zero
    exact this n hn
  · intro n hn
    have := iteratedDerivWithin_comp_vanish_of_flat
      (g := base.H) (φ := φ)
      base.H_is_C_inf hφ_smooth hmaps hz1 hφ_flat_one
    exact this n hn

end Smooth

end Reparametrization

/-
## Convex Combinations
-/

section ConvexCombination

open scoped ContDiff
open Smooth

namespace Smooth

def mixShape (w : ℝ) (H₁ H₂ : ℝ → ℝ) : ℝ → ℝ :=
  fun z => w * H₁ z + (1 - w) * H₂ z

lemma mixShape_contDiff (w : ℝ)
    {H₁ H₂ : ℝ → ℝ} (hH₁ : ContDiffOn ℝ ∞ H₁ unitInterval)
    (hH₂ : ContDiffOn ℝ ∞ H₂ unitInterval) :
    ContDiffOn ℝ ∞ (mixShape w H₁ H₂) unitInterval := by
  have hmul₁ :
      ContDiffOn ℝ ∞ (fun z => w * H₁ z) unitInterval :=
    (ContDiffOn.const_smul (s := unitInterval) (f := H₁) w hH₁)
  have hmul₂ :
      ContDiffOn ℝ ∞ (fun z => (1 - w) * H₂ z) unitInterval :=
    (ContDiffOn.const_smul (s := unitInterval) (f := H₂) (1 - w) hH₂)
  exact hmul₁.add hmul₂

lemma mixShape_mem_unitInterval {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1)
    {H₁ H₂ : ℝ → ℝ}
    (hH₁ : ∀ ⦃z : ℝ⦄, z ∈ unitInterval → H₁ z ∈ unitInterval)
    (hH₂ : ∀ ⦃z : ℝ⦄, z ∈ unitInterval → H₂ z ∈ unitInterval)
    {z : ℝ} (hz : z ∈ unitInterval) :
    mixShape w H₁ H₂ z ∈ unitInterval := by
  obtain ⟨hw0, hw1⟩ := hw
  have h1w : 0 ≤ 1 - w := sub_nonneg.mpr hw1
  obtain ⟨h1lo, h1hi⟩ := hH₁ hz
  obtain ⟨h2lo, h2hi⟩ := hH₂ hz
  refine ⟨?_, ?_⟩
  · have hterm1 : 0 ≤ w * H₁ z := mul_nonneg hw0 h1lo
    have hterm2 : 0 ≤ (1 - w) * H₂ z := mul_nonneg h1w h2lo
    exact add_nonneg hterm1 hterm2
  · have hterm1 : w * H₁ z ≤ w * 1 := by
      exact mul_le_mul_of_nonneg_left h1hi hw0
    have hterm2 : (1 - w) * H₂ z ≤ (1 - w) * 1 := by
      exact mul_le_mul_of_nonneg_left h2hi h1w
    have hsum_le :
        mixShape w H₁ H₂ z ≤ w * (1 : ℝ) + (1 - w) * (1 : ℝ) :=
      add_le_add hterm1 hterm2
    have hsum_eq : w * (1 : ℝ) + (1 - w) * (1 : ℝ) = 1 := by ring
    simpa [mixShape, hsum_eq] using hsum_le

lemma mixShape_monotone {w : ℝ} (hw : 0 ≤ w) (hw' : 0 ≤ 1 - w)
    {H₁ H₂ : ℝ → ℝ} (hH₁ : MonotoneOn H₁ unitInterval)
    (hH₂ : MonotoneOn H₂ unitInterval) :
    MonotoneOn (mixShape w H₁ H₂) unitInterval := by
  intro x hx y hy hxy
  have h1 := hH₁ hx hy hxy
  have h2 := hH₂ hx hy hxy
  have hterm1 :
      w * H₁ x ≤ w * H₁ y :=
    mul_le_mul_of_nonneg_left h1 hw
  have hterm2 :
      (1 - w) * H₂ x ≤ (1 - w) * H₂ y :=
    mul_le_mul_of_nonneg_left h2 hw'
  have := add_le_add hterm1 hterm2
  simpa [mixShape, add_comm, add_left_comm, add_assoc, add_right_comm] using this

lemma iteratedDeriv_mixShape_zero
    {c₁ c₂ : SmoothstepCurve} {w : ℝ} {a : ℝ} (ha : a ∈ unitInterval) :
    ∀ n : ℕ, iteratedDerivWithin n
        (mixShape w c₁.H c₂.H) unitInterval a =
      w * iteratedDerivWithin n c₁.H unitInterval a +
        (1 - w) * iteratedDerivWithin n c₂.H unitInterval a := by
  intro n
  classical
  have hs : UniqueDiffOn ℝ unitInterval :=
    uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)
  have hcont₁ :
      ContDiffWithinAt ℝ ((n : ℕ∞)) c₁.H unitInterval a :=
    ((c₁.H_is_C_inf.contDiffWithinAt ha).of_le (by
      exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞))))
  have hcont₂ :
      ContDiffWithinAt ℝ ((n : ℕ∞)) c₂.H unitInterval a :=
    ((c₂.H_is_C_inf.contDiffWithinAt ha).of_le (by
      exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞))))
  have hscale₁ :=
    iteratedDerivWithin_const_mul (hx := ha) (h := hs) w hcont₁
  have hscale₂ :=
    iteratedDerivWithin_const_mul (hx := ha) (h := hs) (1 - w) hcont₂
  have hcontscaled₁ :
      ContDiffWithinAt ℝ ((n : ℕ∞)) (fun z => w * c₁.H z) unitInterval a :=
    (ContDiffWithinAt.const_smul (s := unitInterval) (f := c₁.H) (x := a) w hcont₁)
  have hcontscaled₂ :
      ContDiffWithinAt ℝ ((n : ℕ∞)) (fun z => (1 - w) * c₂.H z) unitInterval a :=
    (ContDiffWithinAt.const_smul (s := unitInterval) (f := c₂.H) (x := a) (1 - w) hcont₂)
  have hadd :=
    iteratedDerivWithin_fun_add (hx := ha) (h := hs) hcontscaled₁ hcontscaled₂
  have hscaled :
      iteratedDerivWithin n (mixShape w c₁.H c₂.H) unitInterval a =
        iteratedDerivWithin n (fun z => w * c₁.H z) unitInterval a +
          iteratedDerivWithin n (fun z => (1 - w) * c₂.H z) unitInterval a := by
    simpa [mixShape, add_comm, add_left_comm, add_assoc] using hadd
  simpa [mixShape, add_comm, add_left_comm, add_assoc, hscale₁, hscale₂] using hscaled

noncomputable def mixCurve (w : ℝ) (hw : w ∈ Set.Icc (0 : ℝ) 1)
    (c₁ c₂ : SmoothstepCurve) : SmoothstepCurve := by
  classical
  refine mkSmoothstepCurveFromShape
    (mixShape w c₁.H c₂.H)
    (mixShape_contDiff w c₁.H_is_C_inf c₂.H_is_C_inf)
    (by simp [mixShape, c₁.H_zero, c₂.H_zero])
    (by simp [mixShape, c₁.H_one, c₂.H_one])
    ?mem ?mono ?flat0 ?flat1
  · intro z hz
    exact mixShape_mem_unitInterval hw
      (c₁.H_mem_unitInterval) (c₂.H_mem_unitInterval) hz
  · have hw0 : 0 ≤ w := hw.1
    have hw1 : 0 ≤ 1 - w := sub_nonneg.mpr hw.2
    exact mixShape_monotone hw0 hw1
      c₁.H_monotone_on_unit c₂.H_monotone_on_unit
  · intro n hn
    have hderiv := iteratedDeriv_mixShape_zero
        (c₁ := c₁) (c₂ := c₂) (w := w) (a := 0) (ha := ⟨le_rfl, by norm_num⟩) n
    have hz₁ := c₁.H_deriv_vanishes_at_zero n hn
    have hz₂ := c₂.H_deriv_vanishes_at_zero n hn
    simp [hderiv, hz₁, hz₂]
  · intro n hn
    have hderiv := iteratedDeriv_mixShape_zero
        (c₁ := c₁) (c₂ := c₂) (w := w) (a := 1) (ha := ⟨zero_le_one, le_rfl⟩) n
    have hz₁ := c₁.H_deriv_vanishes_at_one n hn
    have hz₂ := c₂.H_deriv_vanishes_at_one n hn
    simp [hderiv, hz₁, hz₂]

end Smooth

end ConvexCombination
