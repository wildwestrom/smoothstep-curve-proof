# Smoothstep Curves: Infinitely Differentiable Curvature Functions

This file develops smoothstep-based curvature functions that provide $G^\infty$ continuous transitions between segments of constant curvature (for example, between tangent lines and circular arcs).

The key design is fixed and permeates the entire development:

* We **always parameterize transitions by a bump function $G$** supported in $(0,1)$.
* The shape function $H$ is *derived* — never assumed — as the normalized primitive of $G$.
* Users stay in control of quantitative bounds (peak jerk, snap, …) by choosing the bump $G$ that best fits their application.  The API intentionally avoids a single “canonical” smoothstep.

With this normalization the qualitative requirements on $H$ (smooth, monotone, flat endpoints, normalized) become automatic consequences of the properties of $G$.

We keep all constructions $C^\infty$ / $G^\infty$-smooth; no finite-order relaxation is used anywhere.

> [!WARNING]
> This is proof has been "vibe-proved". I don't really know Lean 4, I just know enough to know what I'm trying to prove and how to formulate the end goal. I'd appreciate if someone who actually knows math could tell me any mistakes I made. If so, please leave an issue or pull request.
>
> Thank you.

## Mathematical Framework

A smoothstep curve is defined by a curvature function $\kappa(s)$ that smoothly transitions from a start curvature $R_1$ to an end curvature $R_2$:

* Straight line: $R_i = 0$.
* Circular arc: constant nonzero curvature $R_i$, with radius $1 / |R_i|$.

We work with a **shape function** $H$ derived from a bump $G$.  Conceptually:

* Choose a nonnegative bump $G$ supported in $(0,1)$, $C^\infty$, with $\int_0^1 G = 1$.
* Define $$H(z) := \int_0^z G(t) dt, \quad z \in[0,1]$$.
* Then $H : [0,1] → [0,1]$ is smooth, monotone, and flat at the endpoints.

The implementation follows this viewpoint:

* `HInt G z` is the primitive $\int_0^z G$.
* `HInt_denom G` is $\int_0^1 G$, used for normalization.
* `H G z := HInt G (clampUnit z) / HInt_denom G` is the shape function exposed by the API.
* The curvature expression is given directly in terms of $H$.

The user chooses $G$ (bump shape) to control quantitative properties (e.g., max of $\kappa'$, $\kappa''$, …); the framework guarantees the qualitative properties (smoothness, flat joins, monotonic curvature change).

### General Form

For a smoothstep curve with:

* $s$  = arc length parameter with $0 ≤ s ≤ L$
* $L$  = total length of the transition curve
* $R_1$ = start curvature (constant before the transition)
* $R_2$ = end curvature (constant after the transition)
* $z := s / L ∈ [0,1]$ = normalized arc-length parameter
* $\Delta R := R_2 - R_1$ = curvature change

we define the curvature on the transition segment by

$$
\kappa(s) = R_1 + \Delta R \cdot H(s/L).
$$

where $H : [0,1] → [0,1]$ is the shape function constructed from $G$ as above.

The heading angle is

$$
\theta(s)
= \int_0^s \kappa(v) dv
= R_1 s + \Delta R\cdot L \int_0^{s/L} H(u) du.
$$

The Cartesian coordinates (arc length parametrization) are

$$
x(s) = \int_0^s \cos(\theta(v)) dv,\quad
y(s) = \int_0^s \sin(\theta(v)) dv.
$$

### Conditions on $H$

At the abstract level, we want a shape function
$H : [0,1] → [0,1]$ with:

1. **Smoothness**:
   $H ∈ C^\infty([0,1])$.

2. **Boundary values**:
   $H(0) = 0,\quad H(1) = 1.$

3. **Monotonicity**:
   $H'(z) ≥ 0$ for all $z ∈ [0,1]$.
   Then if $\Delta R > 0$, curvature increases, and if $\Delta R < 0$, curvature decreases.

4. **Flatness at endpoints**:
   $H^{(n)}(0) = H^{(n)}(1) = 0$ for all $n ≥ 1$.

These four properties imply that for $0 ≤ s ≤ L$,

$$
\kappa^{(n)}(s) = \Delta R \cdot L^{-n} \cdot H^{(n)}(s/L),
$$

so

$$
\kappa^{(n)}(0) = \kappa^{(n)}(L) = 0 \quad\text{for all } n ≥ 1.
$$

If we extend $\kappa$ by constants $R_1$ for $s < 0$ and $R_2$ for $s > L$, we get a globally $C^\infty$ curvature function with all derivatives matching at $0$ and $L$, i.e. $G^\infty$ continuity at the joins. This matches the fact that tangents and circular arcs have constant curvature, so all of their curvature derivatives (order $\ge 1$) vanish.

### Equivalence with the Bump-Function Framework

The implementation actually starts from a bump $G$ and *derives* $H$ from it. The key mathematical fact is:

*If* $H$ *satisfies the four conditions above, then:*

* $G := H'$ is a nonnegative $C^\infty$ bump on $(0,1)$ with $\int_0^1 G = 1$,

* and conversely, if $G ≥ 0$ is a $C^\infty$ bump with $\int_0^1 G = 1$ and we set $H(z) := \int_0^z G(t)\,dt$, then $H$ satisfies (1)–(4).

Thus the four abstract conditions on $H$ are exactly equivalent to saying:

> $H$ is the normalized cumulative integral of a nonnegative $C^\infty$ bump $G$ supported in $(0,1)$.

In this file:

- The **generic framework** (`Smooth` namespace) formalizes the passage from `G` to `H` together with the curvature profile $\kappa$.
- The **`SmoothstepCurve` structure** packages the resulting $H$, the curvature $\kappa$, and all accompanying properties (smoothness, flat joins, monotonicity).
- The constructors `mkSmoothstepCurve`, `mkSmoothstepCurveFromShape`, and `mkSmoothstepCurveFromDenom` give users multiple entry points for supplying their own bumps. In particular, `mkSmoothstepCurveFromDenom` turns *any* denominator function into a bump via `expNegInvGlue ∘ denom`, so the public API never fixes a single smoothstep.
- The implementations `curve1` and `curve2` demonstrate two concrete denominators with different quantitative trade-offs while still respecting the generic bump → shape → curvature pipeline.
