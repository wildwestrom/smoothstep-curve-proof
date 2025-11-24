/-
# Smoothstep Curves: Infinitely Differentiable Curvature Functions

This file demonstrates the construction of smoothstep-based curvature functions
that provide $G^\infty$ continuous transitions between segments of constant
curvature (for example, between tangent lines and circular arcs).
The property of being infinitely differentiable may prove to be useful for
engineering applications.

## Mathematical Framework

A smoothstep curve is defined by a curvature function $\kappa(s)$ that
smoothly transitions from a start curvature $R_1$ to an end curvature
$R_2$. A straight line corresponds to $R_i = 0$, and a circular arc
corresponds to a nonzero constant curvature $R_i$ (with radius
$1 / |R_i|$).

The key insight is to use a single "shape function" $H$ to create this
transition, eliminating the need for intermediate bump functions and
normalization integrals.

### General Form

For a smoothstep curve with:

- $s$ = arc length parameter with $0 \le s \le L$
- $L$ = total length of the transition curve
- $R_1$ = start curvature (constant curvature before the transition)
- $R_2$ = end curvature (constant curvature after the transition)
- $z = s/L \in [0,1]$ = normalized arc-length parameter
- $\Delta R = R_2 - R_1$ = curvature change

Define the curvature on the transition segment directly by

$$
\kappa(s) = R_1 + \Delta R\,H\!\left(\frac{s}{L}\right),
$$

where $H:[0,1]\to[0,1]$ is a "shape function" satisfying the conditions below.

The heading angle is

$$
\theta(s) = \int_0^s \kappa(v)\,dv
          = R_1 s + \Delta R\,L \int_0^{s/L} H(u)\,du.
$$

The Cartesian coordinates (with arc length parametrization) are

$$
x(s) = \int_0^s \cos(\theta(v))\,dv, \quad
y(s) = \int_0^s \sin(\theta(v))\,dv.
$$

### Conditions on $H$

The shape function $H$ must satisfy:

1. **Smoothness**:
  $H \in C^\infty([0,1])$.

2. **Boundary values**:
  $$
  H(0) = 0, \quad H(1) = 1.
  $$

3. **Monotonicity**:
  $$
  H'(z) \ge 0 \quad \text{for all } z \in [0,1].
  $$
  (Then if $\Delta R>0$, $\kappa$ increases; if $\Delta R<0$, $\kappa$ decreases.)

4. **Flatness at endpoints**:
  $$
  H^{(n)}(0) = H^{(n)}(1) = 0 \quad \text{for all } n \ge 1.
  $$
  Then, for $0 \le s \le L$,
  $$
  \kappa^{(n)}(s) = \Delta R\,L^{-n}\,H^{(n)}\!\left(\frac{s}{L}\right),
  $$
  so in particular
  $$
  \kappa^{(n)}(0) = \kappa^{(n)}(L) = 0 \quad \text{for all } n \ge 1.
  $$

When $\kappa$ is extended by constants $R_1$ for $s < 0$ and $R_2$ for $s > L$,
this yields a $C^\infty$ curvature function globally, with all derivatives
matching at $s=0$ and $s=L$ (i.e., $G^\infty$ at the joins). This matches
the fact that circular arcs and straight tangents have constant curvature,
so all of their curvature derivatives (of order $\ge 1$) are zero.

### Relation to Bump-Function Framework

This formulation is equivalent to the traditional bump-function approach:
- In the traditional framework, one chooses a bump $G$, integrates and normalizes
  it to get $F$, and uses $\kappa = R_1 + (R_2-R_1)F(s/L)$.
- In the simplified picture: $H := F$ is the primary object, and $G$ is its
  derivative: $G(z) = F'(z) = H'(z)$.
- Normalization is implicitly encoded in $H(0)=0, H(1)=1$.

This reduces the construction to one function $H$ with simple endpoint and
monotonicity conditions, while preserving all four properties.
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

noncomputable
section GenericFramework

open scoped ContDiff Topology
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

lemma pos_on_subIoo_of_unit
  {f : ℝ → ℝ} {a b : ℝ}
  (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < f x) :
  ∀ t ∈ Set.Ioo a b, 0 < f t := by
  intro t ht
  have ht0 : 0 < t := lt_of_le_of_lt ha0 ht.1
  have ht1 : t < 1 := lt_of_lt_of_le ht.2 hb1
  exact hpos t ⟨ht0, ht1⟩

/-- A convenient `FTCFilter` instance for `𝓝[unitInterval]`. -/
private def ftcFilter_unitInterval {x : ℝ} (hx : x ∈ unitInterval) :
    intervalIntegral.FTCFilter x (𝓝[unitInterval] x) (𝓝[unitInterval] x) := by
  classical
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by simpa [unitInterval] using hx
  simpa [unitInterval] using
    (intervalIntegral.FTCFilter.nhdsIcc (x := x) (a := (0 : ℝ)) (b := (1 : ℝ))
      (h := ⟨hxIcc⟩))

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
def HInt (G : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in Set.uIoc 0 z, G t

-- Denominator of the normalized integral: ∫₀¹ H'(t) dt (normalization constant)
def HInt_denom (G : ℝ → ℝ) : ℝ := ∫ t in Set.uIoc 0 1, G t

-- The shape function H(z) = HInt(clampUnit z) / HInt_denom
def H (G : ℝ → ℝ) (z : ℝ) : ℝ := HInt G (clampUnit z) / HInt_denom G

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
        ∀ t ∈ Set.Ioo x y, 0 < G t :=
      pos_on_subIoo_of_unit (f := G) hx.1 hy.2 hpos
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

lemma H_deriv_vanishes_at_zero_from_G
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hG_zero : G 0 = 0)
    (hG_deriv_zero :
      ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n G unitInterval 0 = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n (H G) unitInterval 0 = 0 := by
  classical
  intro n hn
  have hn0 : n ≠ 0 := by
    intro h
    have : 1 ≤ 0 := by simp [h] at hn
    exact Nat.not_succ_le_self 0 this
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hx0 : (0 : ℝ) ∈ unitInterval := ⟨le_rfl, by norm_num⟩
  have hformula :=
    iteratedDerivWithin_succ_H hG hx0 k
  cases k with
  | zero =>
      simp [hformula, hG_zero]
  | succ k =>
      have hk :
          iteratedDerivWithin (Nat.succ k) G unitInterval 0 = 0 :=
        hG_deriv_zero _ (Nat.succ_pos _)
      simp [hformula, hk]

lemma H_deriv_vanishes_at_one_from_G
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hG_one : G 1 = 0)
    (hG_deriv_one :
      ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n G unitInterval 1 = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n (H G) unitInterval 1 = 0 := by
  classical
  intro n hn
  have hn0 : n ≠ 0 := by
    intro h
    have : 1 ≤ 0 := by simp [h] at hn
    exact Nat.not_succ_le_self 0 this
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hx1 : (1 : ℝ) ∈ unitInterval := ⟨zero_le_one, le_rfl⟩
  have hformula :=
    iteratedDerivWithin_succ_H hG hx1 k
  cases k with
  | zero =>
      simp [hformula, hG_one]
  | succ k =>
      have hk :
          iteratedDerivWithin (Nat.succ k) G unitInterval 1 = 0 :=
        hG_deriv_one _ (Nat.succ_pos _)
      simp [hformula, hk]

lemma H_deriv_vanishes_at_zero
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hG_zero : G 0 = 0)
    (hG_deriv_zero :
      ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n G unitInterval 0 = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n (H G) unitInterval 0 = 0 :=
  H_deriv_vanishes_at_zero_from_G hG hG_zero hG_deriv_zero

lemma H_deriv_vanishes_at_one
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hG_one : G 1 = 0)
    (hG_deriv_one :
      ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n G unitInterval 1 = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n (H G) unitInterval 1 = 0 :=
  H_deriv_vanishes_at_one_from_G hG hG_one hG_deriv_one

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
def kappa (G : ℝ → ℝ) (s R₁ R₂ L : ℝ) : ℝ :=
  R₁ + (R₂ - R₁) * H G (s / L)

lemma div_mem_unitInterval_of_mem_Icc {L : ℝ} (hL : 0 < L) {s : ℝ}
    (hs : s ∈ Set.Icc 0 L) : s / L ∈ unitInterval := by
  rcases hs with ⟨hs0, hsL⟩
  refine ⟨div_nonneg hs0 (le_of_lt hL), ?_⟩
  have hLne : L ≠ 0 := ne_of_gt hL
  have : s / L ≤ L / L := div_le_div_of_nonneg_right hsL (le_of_lt hL)
  simpa [div_self hLne] using this

lemma kappa_contDiffOn
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (R₁ R₂ L : ℝ) (hL : 0 < L) :
  ContDiffOn ℝ ∞ (fun s => kappa G s R₁ R₂ L) (Set.Icc 0 L) := by
  have hmap :
      ∀ ⦃s⦄, s ∈ Set.Icc 0 L → s / L ∈ unitInterval := by
    intro s hs
    exact div_mem_unitInterval_of_mem_Icc hL hs
  have hH : ContDiffOn ℝ ∞ (H G) unitInterval := H_contDiffOn hG
  have hcomp : ContDiffOn ℝ ∞ (fun s => H G (s / L)) (Set.Icc 0 L) :=
    hH.comp (contDiffOn_id.div_const L) (fun s hs => hmap hs)
  let g : ℝ → ℝ := fun s => (R₂ - R₁) * H G (s / L)
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
  simpa [kappa, g, add_comm, add_left_comm, add_assoc] using hsum'

lemma kappa_at_zero (G : ℝ → ℝ) (R₁ R₂ L : ℝ) :
    kappa G 0 R₁ R₂ L = R₁ := by
  simp [kappa, H_zero]

lemma kappa_at_L
    (G : ℝ → ℝ) (R₁ R₂ L : ℝ) (hL : L ≠ 0) (hden : HInt_denom G ≠ 0) :
    kappa G L R₁ R₂ L = R₂ := by
  have hdiv : L / L = 1 := div_self hL
  simp [kappa, hdiv, H_one (G := G) hden]

-- Helper lemma for the common setup in monotonicity proofs
private lemma kappa_inequality_helper
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x)
    (L : ℝ) (hL : 0 < L) (hden : 0 < HInt_denom G)
    (x y : ℝ) (hx : x ∈ Set.Icc 0 L) (hy : y ∈ Set.Icc 0 L) (hxy : x ≤ y) :
    H G (x / L) ≤ H G (y / L) := by
  have hxmap : x / L ∈ unitInterval :=
    div_mem_unitInterval_of_mem_Icc hL hx
  have hymap : y / L ∈ unitInterval :=
    div_mem_unitInterval_of_mem_Icc hL hy
  have hxy_div : x / L ≤ y / L :=
    div_le_div_of_nonneg_right hxy (le_of_lt hL)
  have hHmono := H_monotone_on_unit hG hpos hden
  exact hHmono hxmap hymap hxy_div

lemma kappa_monotone_on_Icc
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x)
    (R₁ R₂ L : ℝ) (hL : 0 < L) (hden : 0 < HInt_denom G) (hmono : R₁ ≤ R₂) :
    MonotoneOn (fun s => kappa G s R₁ R₂ L) (Set.Icc 0 L) := by
  intro x hx y hy hxy
  have hcmp := kappa_inequality_helper hG hpos L hL hden x y hx hy hxy
  have hΔ : 0 ≤ R₂ - R₁ := sub_nonneg.mpr hmono
  have hscaled :
      (R₂ - R₁) * H G (x / L) ≤ (R₂ - R₁) * H G (y / L) :=
    mul_le_mul_of_nonneg_left hcmp hΔ
  have := add_le_add_left hscaled R₁
  simpa [kappa, add_comm, add_left_comm, add_assoc] using this

lemma kappa_antitone_on_Icc
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x)
    (R₁ R₂ L : ℝ) (hL : 0 < L) (hden : 0 < HInt_denom G) (hmono : R₂ ≤ R₁) :
    AntitoneOn (fun s => kappa G s R₁ R₂ L) (Set.Icc 0 L) := by
  intro x hx y hy hxy
  have hcmp := kappa_inequality_helper hG hpos L hL hden x y hx hy hxy
  have hΔ : R₂ - R₁ ≤ 0 := sub_nonpos.mpr hmono
  have hscaled :
      (R₂ - R₁) * H G (y / L) ≤ (R₂ - R₁) * H G (x / L) :=
    mul_le_mul_of_nonpos_left hcmp hΔ
  have := add_le_add_left hscaled R₁
  simpa [kappa, add_comm, add_left_comm, add_assoc] using this

/-
### SmoothstepCurve Structure

This structure encapsulates a complete smoothstep curve with all its properties.
-/

structure SmoothstepCurve where
  H : ℝ → ℝ
  κ : ℝ → ℝ → ℝ → ℝ → ℝ
  H_is_C_inf : ContDiffOn ℝ ∞ H unitInterval
  κ_is_C_inf :
    ∀ R₁ R₂ L (_ : 0 < L),
      ContDiffOn ℝ ∞ (fun s => κ s R₁ R₂ L) (Set.Icc 0 L)
  κ_at_zero : ∀ R₁ R₂ L, κ 0 R₁ R₂ L = R₁
  κ_at_L : ∀ R₁ R₂ L (_ : L ≠ 0), κ L R₁ R₂ L = R₂
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

def mkSmoothstepCurve (G : ℝ → ℝ) (hG : ContDiffOn ℝ ∞ G unitInterval)
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
    κ_is_C_inf := fun R₁ R₂ L hL => kappa_contDiffOn hG R₁ R₂ L hL,
    κ_at_zero := fun R₁ R₂ L => kappa_at_zero G R₁ R₂ L,
    κ_at_L := fun R₁ R₂ L hL => by
      have hden_ne : HInt_denom G ≠ 0 := hden.ne'
      exact kappa_at_L G R₁ R₂ L hL hden_ne,
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

lemma H_deriv_vanishes_at_zero_expNegInvGlue_comp
  {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
  (hdenom_zero : denom 0 = 0) :
  ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n (H (fun t => expNegInvGlue (denom t))) unitInterval 0 = 0 := by
  let G := fun t => expNegInvGlue (denom t)
  have hG : ContDiffOn ℝ ∞ G unitInterval :=
    (expNegInvGlue.contDiff.comp hdenom_contDiff).contDiffOn
  intro n hn
  by_cases hden : HInt_denom G = 0
  · have hH : ∀ x, H G x = 0 := by simp [H, hden]
    rw [iteratedDerivWithin_congr (f := H G) (g := fun _ => 0) (s := unitInterval) (n := n) (by intro x hx; exact hH x)]
    · apply iteratedDerivWithin_zero_fun_all
    · simp
  · have hvan :=
      H_deriv_vanishes_at_zero_from_G hG
        (by simp [G, hdenom_zero, expNegInvGlue.zero])
        (by
          intro k hk
          exact
            iteratedDerivWithin_expNegInvGlue_comp_of_mem
              hdenom_contDiff hdenom_zero (by norm_num) k)
    exact hvan n hn

lemma H_deriv_vanishes_at_one_expNegInvGlue_comp
  {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
  (hdenom_one : denom 1 = 0) :
  ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n (H (fun t => expNegInvGlue (denom t))) unitInterval 1 = 0 := by
  let G := fun t => expNegInvGlue (denom t)
  have hG : ContDiffOn ℝ ∞ G unitInterval :=
    (expNegInvGlue.contDiff.comp hdenom_contDiff).contDiffOn
  intro n hn
  by_cases hden : HInt_denom G = 0
  · have hH : ∀ x, H G x = 0 := by simp [H, hden]
    rw [iteratedDerivWithin_congr (f := H G) (g := fun _ => 0) (s := unitInterval) (n := n) (by intro x hx; exact hH x)]
    · apply iteratedDerivWithin_zero_fun_all
    · simp
  · have hvan :=
      H_deriv_vanishes_at_one_from_G hG
        (by simp [G, hdenom_one, expNegInvGlue.zero])
        (by
          intro k hk
          exact
            iteratedDerivWithin_expNegInvGlue_comp_of_mem
              hdenom_contDiff hdenom_one (by norm_num) k)
    exact hvan n hn

-- Helper to create smoothstep curve from any denominator function
def mkSmoothstepCurveFromDenom (denom : ℝ → ℝ) (hdenom_contDiff : ContDiff ℝ ∞ denom)
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
    κ_is_C_inf := fun R₁ R₂ L hL => kappa_contDiffOn hG R₁ R₂ L hL,
    κ_at_zero := fun R₁ R₂ L => kappa_at_zero G R₁ R₂ L,
    κ_at_L := fun R₁ R₂ L hL => by
      have hden_ne : HInt_denom G ≠ 0 := hden.ne'
      exact kappa_at_L G R₁ R₂ L hL hden_ne,
    H_monotone_on_unit := H_monotone_on_unit hG hpos hden,
    κ_monotone_on_Icc := fun R₁ R₂ L hL hmono =>
      kappa_monotone_on_Icc hG hpos R₁ R₂ L hL hden hmono,
    κ_antitone_on_Icc := fun R₁ R₂ L hL hmono =>
      kappa_antitone_on_Icc hG hpos R₁ R₂ L hL hden hmono,
    H_deriv_vanishes_at_zero := H_deriv_vanishes_at_zero_expNegInvGlue_comp hdenom_contDiff hdenom_zero,
    H_deriv_vanishes_at_one := H_deriv_vanishes_at_one_expNegInvGlue_comp hdenom_contDiff hdenom_one
  }

end Smooth

end GenericFramework

/-
## Implementation 1: Standard Smoothstep Curve

Uses the classic smoothstep bump function $$G\left(z\right)=e^{\left(-\frac{1}{z\left(1-z\right)}\right)}$$.
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

-- The denominator function z(1-z) for the bump function
def denom_fn (z : ℝ) : ℝ := z * (1 - z)

lemma denom_contDiff : ContDiff ℝ ∞ denom_fn :=
  contDiff_id.mul (contDiff_const.sub contDiff_id)

lemma denom_pos_on_Ioo (t : ℝ) (ht : t ∈ Set.Ioo 0 1) : 0 < denom_fn t := by
  rcases ht with ⟨ht0, ht1⟩
  exact mul_pos ht0 (sub_pos.mpr ht1)

-- denom_fn vanishes at boundaries
lemma denom_fn_zero : denom_fn 0 = 0 := by simp [denom_fn]
lemma denom_fn_one : denom_fn 1 = 0 := by simp [denom_fn]

-- G = expNegInvGlue ∘ denom_fn vanishes at boundaries
lemma G₁_zero : (fun t => expNegInvGlue (denom_fn t)) 0 = 0 := by
  simp [denom_fn_zero, expNegInvGlue.zero_of_nonpos (le_refl 0)]

lemma G₁_one : (fun t => expNegInvGlue (denom_fn t)) 1 = 0 := by
  simp [denom_fn_one, expNegInvGlue.zero_of_nonpos (le_refl 0)]

def curve1 : SmoothstepCurve :=
  mkSmoothstepCurveFromDenom denom_fn denom_contDiff denom_pos_on_Ioo denom_fn_zero denom_fn_one

end SmoothstepCurve1

/-
## Implementation 2: Improved Smoothstep Curve

Uses modified bump function $$G_2\left(z\right)=e^{\left(1-\frac{1}{4z\left(1-z\right)}\right)}$$ with better performance characteristics:
- Smaller angular jerk and snap
- Shorter transition length for same deflection angle
- Better motion control performance
-/

noncomputable
section SmoothstepCurve2

open scoped ContDiff Topology
open Smooth MeasureTheory

def denom2 (z : ℝ) : ℝ := 4 * z * (1 - z)

lemma denom2_contDiff : ContDiff ℝ ∞ denom2 :=
  (contDiff_const.mul contDiff_id).mul (contDiff_const.sub contDiff_id)

lemma denom2_pos_on_Ioo (x : ℝ) (hx : x ∈ Set.Ioo 0 1) : 0 < denom2 x := by
  rcases hx with ⟨hx0, hx1⟩
  have hx_pos : 0 < x := hx0
  have h1x_pos : 0 < 1 - x := sub_pos.mpr hx1
  have : 0 < 4 * x * (1 - x) := by
    have h4 : 0 < (4 : ℝ) := by norm_num
    exact mul_pos (mul_pos h4 hx_pos) h1x_pos
  simpa [denom2] using this

-- denom2 vanishes at 0
lemma denom2_zero : denom2 0 = 0 := by
  simp only [denom2]
  norm_num

-- denom2 vanishes at 1
lemma denom2_one : denom2 1 = 0 := by
  simp only [denom2]
  norm_num

-- G = expNegInvGlue ∘ denom2 vanishes at 0
lemma G₂_zero : (fun t => expNegInvGlue (denom2 t)) 0 = 0 := by
  simp [denom2_zero, expNegInvGlue.zero_of_nonpos (le_refl 0)]

-- G = expNegInvGlue ∘ denom2 vanishes at 1
lemma G₂_one : (fun t => expNegInvGlue (denom2 t)) 1 = 0 := by
  simp [denom2_one, expNegInvGlue.zero_of_nonpos (le_refl 0)]

def curve2 : SmoothstepCurve :=
  mkSmoothstepCurveFromDenom denom2 denom2_contDiff denom2_pos_on_Ioo denom2_zero denom2_one

end SmoothstepCurve2
