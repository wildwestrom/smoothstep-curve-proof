# Smoothstep railway transition curves

A Lean 4 formalization of curvature transitions that are flat to every order at their endpoints.

Railway alignments are assembled from pieces with different curvature. A straight has curvature $0$; a circular arc has some constant curvature $R \ne 0$. Although both pieces have zero curvature derivative,

```math
\frac{d\kappa_{\mathrm{straight}}}{ds}
= \frac{d\kappa_{\mathrm{circle}}}{ds} = 0,
\qquad
\kappa_{\mathrm{straight}} \ne \kappa_{\mathrm{circle}},
```

joining them directly makes curvature jump at the join.

A clothoid fixes that discontinuity by varying curvature linearly. But when the clothoid is joined to a straight or circular segment, its nonzero constant curvature derivative meets the zero derivative of the neighboring segment. The next order still changes abruptly.

This project asks the deliberately theoretical question: can the transition be made flat at both ends not just to one chosen order, but to **every** order?

The answer formalized here is yes, at the level of the curvature profile.

> [!NOTE]
> A nonconstant polynomial transition spliced to constant curvature on either side can only hide the join for finitely many derivatives. A polynomial of finite degree cannot have every positive-order derivative vanish at an endpoint unless the relevant Taylor data make it constant, so some derivative must eventually be discontinuous. This observation motivates using a non-polynomial bump function, but it is not currently formalized in this repository.

## Construction

Begin with a smooth bump $G : \mathbb R \to \mathbb R$ that is positive on $(0,1)$ and zero outside it. Normalize its cumulative integral:

```math
H(z) =
\frac{\displaystyle\int_0^z G(t)\,dt}
     {\displaystyle\int_0^1 G(t)\,dt}.
```

The resulting shape function is a smooth step:

- $H(z)=0$ for $z\le 0$;
- $H(z)=1$ for $z\ge 1$;
- $H$ is monotone on $[0,1]$; and
- every positive-order derivative of $H$ vanishes at $0$ and $1$.

For a transition of length $L>0$, from curvature $R_1$ to $R_2$, define

```math
\kappa(s) = R_1 + (R_2-R_1)H(s/L).
```

Because $H$ is already constant outside the unit interval, this is one global function: $\kappa(s)=R_1$ before the transition and $\kappa(s)=R_2$ after it. At $s=0$ and $s=L$, every derivative of positive order is zero. The transition therefore agrees to every curvature-derivative order with the constant-curvature pieces on either side.

### Canonical example

The standard construction in this repository uses Mathlib's globally smooth `expNegInvGlue` with

```math
d(z)=z(1-z),
\qquad
G(z)=\exp\!\left(-\frac{1}{z(1-z)}\right) \quad \text{for } 0<z<1,
\qquad
G(z)=0 \quad \text{otherwise}.
```

This bump and all of its derivatives vanish at both endpoints. Integrating and normalizing it produces the required $H$. The framework is not tied to this one choice: `DenomParams` packages the conditions needed to construct other valid bumps of the form `expNegInvGlue ∘ denom`.

## What Lean proves

The central `SmoothstepCurve` structure packages a shape function and its induced curvature function together with proofs that:

- the shape and curvature functions are globally $C^\infty$;
- the shape is constant outside $[0,1]$, has values $0$ and $1$ at the endpoints, and is monotone within the interval;
- every positive-order derivative of the shape vanishes at both endpoints;
- curvature takes the requested endpoint values and is monotone or antitone according to the direction of the curvature change; and
- every positive-order curvature derivative vanishes at both joins.

The repository also proves several ways to build and combine these profiles:

- a canonical symmetric denominator and scaled, odd-power, and asymmetric families;
- smooth reparameterization and convex mixing of existing shapes;
- concatenation of two transitions through a shared curvature, including flatness of the internal join; and
- a Viennese/Hasslinger-style layer coupling smooth cant to physical curvature, with smoothness and endpoint behavior proved for both profiles.

There are no `sorry` or `admit` placeholders in the Lean sources.

## What Lean does not prove

The formal development currently stops at curvature and cant profiles. It does not yet reconstruct a planar curve by integrating the Frenet equations and prove geometric $G^\infty$ continuity of that position curve. That is the geometric motivation for the construction, not a theorem claimed by this repository.

Likewise, this is not a claim that the curve is practical or optimal for real railway design. It does not model vehicle dynamics, speed, track forces, construction tolerances, or regulatory constraints. Infinite-order smoothness is a mathematical property, not an engineering approval.

`proofs/computable.lean` supplies a floating-point demonstration using Gauss–Legendre quadrature and RK4 integration. It is useful for evaluating and plotting examples, but its numerical error bounds and correspondence with the real-valued proofs are not themselves formally verified.

## Build

This project uses Lean 4 and Mathlib through Lake.

```bash
lake exe cache get   # optional: download pre-built Mathlib artifacts
lake build
lake exe runLinter
```

Do not run `lake clean`: rebuilding Mathlib from scratch can take a long time.

## Repository guide

| Path | Contents |
| --- | --- |
| `proofs/smoothstep_curve.lean` | Generic bump-to-shape construction and `SmoothstepCurve` |
| `proofs/curve_examples.lean` | Concrete families, closure properties, and concatenation |
| `proofs/viennese_curve.lean` | Cant and physical-curvature model |
| `proofs/computable.lean` | Executable floating-point approximation and curve integration |
| `proofs.lean` | Library entry point |

## Background

This grew out of a search for better track geometry while playing Transport Fever 2. The longer account covers the path from Bézier curves, through clothoids and higher-order continuity, to this bump-function construction:

- [A deep dive into curves and smoothness, part 1](https://www.westrom.xyz/blog/007-curves-part-1)
- [A deep dive into curves and smoothness, part 2](https://www.westrom.xyz/blog/008-curves-part-2)
- [Discussion on the Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/583339-AI-authored-projects/topic/Bump.20Function-based.20Railway.20Transition.20Curve/with/625308180)

The broader motivation was informed by Raph Levien's [*From Spiral to Spline: Optimal Techniques in Interactive Curve Design*](https://levien.com/phd/thesis.pdf) and the review [*Railway Transition Curves: A Review of the State-of-the-Art and Future Research*](https://doi.org/10.3390/infrastructures5050043).

## Review wanted

This is an AI-assisted formalization written while learning Lean. A successful build checks the proof terms, but it does not guarantee that the definitions capture every intended geometric or railway-engineering claim. Mathematical, Lean, and railway-engineering review is welcome, especially counterexamples, missing hypotheses, or places where the informal interpretation outruns the formal result.
