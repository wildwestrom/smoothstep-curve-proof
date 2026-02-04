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

* Choose a nonnegative bump $G$ supported in $(0,1)$, globally $C^\infty$ on $\mathbb{R}$, vanishing for $z ≤ 0$, with $\int_0^1 G = 1$.
* Define $$H(z) := \frac{\int_0^z G(t) dt}{\int_0^1 G(t) dt}$$ for all $z \in \mathbb{R}$.
* Then $H : \mathbb{R} → \mathbb{R}$ is globally smooth, maps $[0,1]$ to $[0,1]$, is monotone on $[0,1]$, flat at the endpoints, and extends naturally to all of $\mathbb{R}$ (constant $0$ for $z ≤ 0$, constant $1$ for $z ≥ 1$).

The implementation follows this viewpoint:

* `HInt G z` is the primitive $\int_0^z G$.
* `HInt_denom G` is $\int_0^1 G$, used for normalization.
* `H G z := HInt G z / HInt_denom G` is the shape function exposed by the API, defined globally on $\mathbb{R}$.
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

where $H : \mathbb{R} → \mathbb{R}$ is the shape function constructed from $G$ as above (with $H$ mapping $[0,1]$ into $[0,1]$).

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

At the abstract level, we want a shape function $H : \mathbb{R} → \mathbb{R}$ with:

1. **Global Smoothness**:
   $H ∈ C^\infty(\mathbb{R})$ (globally smooth on all of $\mathbb{R}$).

2. **Boundary values and extension**:
   $H(0) = 0,\quad H(1) = 1.$
   $H(z) = 0$ for all $z ≤ 0$.
   $H(z) = 1$ for all $z ≥ 1$.

3. **Monotonicity**:
   $H'(z) ≥ 0$ for all $z ∈ [0,1]$.
   Then if $\Delta R > 0$, curvature increases, and if $\Delta R < 0$, curvature decreases.

4. **Flatness at endpoints**:
   $H^{(n)}(0) = H^{(n)}(1) = 0$ for all $n ≥ 1$.

These four properties, combined with global smoothness of $H$, imply that for all $s \in \mathbb{R}$,

$$
\kappa^{(n)}(s) = \Delta R \cdot L^{-n} \cdot H^{(n)}(s/L),
$$

and in particular

$$
\kappa^{(n)}(0) = \kappa^{(n)}(L) = 0 \quad\text{for all } n ≥ 1.
$$

Since $H$ is globally $C^\infty$ and extends naturally (constant $0$ for $z ≤ 0$, constant $1$ for $z ≥ 1$), the curvature function $\kappa$ is also globally $C^\infty$ on all of $\mathbb{R}$. When we extend $\kappa$ by constants $R_1$ for $s < 0$ and $R_2$ for $s > L$, all derivatives match at $0$ and $L$, giving $G^\infty$ continuity at the joins. This matches the fact that tangents and circular arcs have constant curvature, so all of their curvature derivatives (order $\ge 1$) vanish.

### Equivalence with the Bump-Function Framework

The implementation actually starts from a bump $G$ and *derives* $H$ from it. The key mathematical fact is:

*If* $H$ *satisfies the four conditions above, then:*

* $G := H'$ is a nonnegative globally $C^\infty$ bump supported in $(0,1)$ with $\int_0^1 G = 1$,

* and conversely, if $G ≥ 0$ is globally $C^\infty$, vanishes for $z ≤ 0$, is supported in $(0,1)$, and $\int_0^1 G = 1$, and we set $H(z) := \int_0^z G(t)\,dt / \int_0^1 G(t)\,dt$, then $H$ satisfies (1)–(4).

Thus the four abstract conditions on $H$ are exactly equivalent to saying:

> $H$ is the normalized cumulative integral of a nonnegative globally $C^\infty$ bump $G$ supported in $(0,1)$ and vanishing for $z ≤ 0$.

In this file:

- The **generic framework** (`Smooth` namespace) formalizes the passage from `G` to `H` together with the curvature profile $\kappa$, establishing global $C^\infty$ smoothness throughout.
- The **`SmoothstepCurve` structure** packages the resulting $H$ (globally smooth on $\mathbb{R}$), the curvature $\kappa$, and all accompanying properties (global smoothness, flat joins, monotonicity on $[0,1]$).
- The constructor `mkSmoothstepCurveFromShape` allows users to supply shape functions directly, while `curveFrom` builds curves from `DenomParams` structures. The `curveFrom` constructor turns *any* denominator function into a bump via `expNegInvGlue ∘ denom`, so the public API never fixes a single smoothstep.
- Example implementations include `curveCanonical`, `curveScaled`, `curvePow`, and `curvePoly`, demonstrating concrete denominators with different quantitative trade-offs while respecting the generic bump → shape → curvature pipeline.
