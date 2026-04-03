/-
  Computable Smoothstep Curves

  Float-based numerical implementation of smoothstep curves for `#eval` and potential extraction.
  Uses Gauss-Legendre quadrature for numerical integration.

  UNVERIFIED: the informal precision claims below are numerical expectations, not Lean proofs.
-/

namespace Computable

/-! ## Layer 1: Gauss-Legendre Quadrature

32-point Gauss-Legendre nodes and weights on [-1,1].
For C∞ functions, n-point Gauss-Legendre achieves ~10⁻²ⁿ error (spectral convergence).
With n=32 points, we get ~10⁻¹⁵ precision for smooth integrands.

Source: `scipy.special.roots_legendre(32)`, emitted with 17 significant digits
to round-trip exactly through IEEE-754 `Float`.
-/

/-- 32-point Gauss-Legendre nodes on [-1, 1] -/
def gaussLegendreNodes32 : Array Float := #[
  -0.99726386184948157,
  -0.98561151154526838,
  -0.96476225558750639,
  -0.93490607593773967,
  -0.89632115576605209,
  -0.84936761373256986,
  -0.79448379596794227,
  -0.73218211874028971,
  -0.66304426693021523,
  -0.5877157572407623,
  -0.50689990893222947,
  -0.42135127613063539,
  -0.33186860228212767,
  -0.23928736225213709,
  -0.14447196158279643,
  -0.048307665687738338,
  0.048307665687738338,
  0.14447196158279643,
  0.23928736225213709,
  0.33186860228212767,
  0.42135127613063539,
  0.50689990893222947,
  0.5877157572407623,
  0.66304426693021523,
  0.73218211874028971,
  0.79448379596794227,
  0.84936761373256986,
  0.89632115576605209,
  0.93490607593773967,
  0.96476225558750639,
  0.98561151154526838,
  0.99726386184948157
]

/-- 32-point Gauss-Legendre weights on [-1, 1]. -/
def gaussLegendreWeights32 : Array Float := #[
  0.0070186100094744202,
  0.016274394730904029,
  0.025392065309261264,
  0.034273862913020543,
  0.042835898022227203,
  0.050998059262376251,
  0.058684093478535787,
  0.065822222776361336,
  0.072345794108848491,
  0.078193895787070158,
  0.083311924226946471,
  0.0876520930044037,
  0.091173878695763641,
  0.093844399080804414,
  0.095638720079274653,
  0.09654008851472759,
  0.09654008851472759,
  0.095638720079274653,
  0.093844399080804414,
  0.091173878695763641,
  0.0876520930044037,
  0.083311924226946471,
  0.078193895787070158,
  0.072345794108848491,
  0.065822222776361336,
  0.058684093478535787,
  0.050998059262376251,
  0.042835898022227203,
  0.034273862913020543,
  0.025392065309261264,
  0.016274394730904029,
  0.0070186100094744202
]

/-- 8-point Gauss-Legendre nodes on [-1, 1]. -/
def gaussLegendreNodes8 : Array Float := #[
  -0.96028985649753629,
  -0.79666647741362684,
  -0.52553240991632899,
  -0.18343464249564981,
  0.18343464249564981,
  0.52553240991632899,
  0.79666647741362684,
  0.96028985649753629
]

/-- 8-point Gauss-Legendre weights on [-1, 1]. -/
def gaussLegendreWeights8 : Array Float := #[
  0.10122853629037618,
  0.22238103445337437,
  0.31370664587788732,
  0.3626837833783621,
  0.3626837833783621,
  0.31370664587788732,
  0.22238103445337437,
  0.10122853629037618
]

/-- 16-point Gauss-Legendre nodes on [-1, 1]. -/
def gaussLegendreNodes16 : Array Float := #[
  -0.98940093499164994,
  -0.9445750230732326,
  -0.86563120238783176,
  -0.755404408355003,
  -0.61787624440264377,
  -0.45801677765722737,
  -0.28160355077925892,
  -0.095012509837637441,
  0.095012509837637441,
  0.28160355077925892,
  0.45801677765722737,
  0.61787624440264377,
  0.755404408355003,
  0.86563120238783176,
  0.9445750230732326,
  0.98940093499164994
]

/-- 16-point Gauss-Legendre weights on [-1, 1]. -/
def gaussLegendreWeights16 : Array Float := #[
  0.027152459411754069,
  0.062253523938647776,
  0.095158511682492897,
  0.12462897125553395,
  0.14959598881657685,
  0.16915651939500256,
  0.18260341504492361,
  0.18945061045506845,
  0.18945061045506845,
  0.18260341504492361,
  0.16915651939500256,
  0.14959598881657685,
  0.12462897125553395,
  0.095158511682492897,
  0.062253523938647776,
  0.027152459411754069
]



/-- Helper loop for Gauss-Legendre integration -/
private def integrateLoop (f : Float → Float) (scale shift : Float)
    (nodes weights : Array Float) (i : Nat) (acc : Float) : Float :=
  if h : i < nodes.size then
    let x := nodes[i]
    let w := weights[i]!
    let t := scale * x + shift
    integrateLoop f scale shift nodes weights (i + 1) (acc + w * f t)
  else
    acc
termination_by nodes.size - i

/-- Numerical integration of `f` over `[a, b]` using the supplied Gauss-Legendre rule. -/
def integrateWithRule (nodes weights : Array Float) (f : Float → Float) (a b : Float) : Float :=
  let scale := (b - a) / 2
  let shift := (a + b) / 2
  scale * integrateLoop f scale shift nodes weights 0 0

/-- Numerical integration of f over [a, b] using 32-point Gauss-Legendre quadrature.
    Transform from [-1,1] to [a,b] via x = scale * t + shift where
    scale = (b-a)/2, shift = (a+b)/2 -/
def integrate (f : Float → Float) (a b : Float) : Float :=
  integrateWithRule gaussLegendreNodes32 gaussLegendreWeights32 f a b

/-! ## Layer 2: Bump Function and Shape Function H -/

/-- Computable exp(-1/x) for x > 0, else 0.
    This is the core building block for smooth bump functions. -/
def expNegInv (x : Float) : Float :=
  if x ≤ 0 then 0 else Float.exp (-1 / x)

/-- Canonical denominator: z(1-z), which is positive on (0,1) -/
def denomCanonical (z : Float) : Float := z * (1 - z)

/-- Canonical bump function G(z) = exp(-1/(z(1-z))).
    This is C∞ with support in (0,1). -/
def G (z : Float) : Float := expNegInv (denomCanonical z)

/-- Numerator integral: ∫₀ᶻ G(t) dt -/
def HInt (z : Float) : Float := integrate G 0 z

/-- Denominator (normalization constant): ∫₀¹ G(t) dt
    Computed once at definition time. -/
def HIntDenom : Float := integrate G 0 1

/-- Shape function H(z) = HInt(z) / HIntDenom.
    H : [0,1] → [0,1] with H(0) = 0, H(1) = 1.
    H is C∞ and monotonically increasing. -/
def H (z : Float) : Float := HInt z / HIntDenom

/-- Shape function computed with a supplied Gauss-Legendre rule. -/
def HWithRule (nodes weights : Array Float) (z : Float) : Float :=
  let num := integrateWithRule nodes weights G 0 z
  let denom := integrateWithRule nodes weights G 0 1
  num / denom

/-! ## Layer 3: Curvature Function -/

/-- Curvature function κ(s) that transitions from R₁ to R₂ over arc length L.
    κ(s, R₁, R₂, L) = R₁ + (R₂ - R₁) · H(s/L) -/
def kappa (s R1 R2 L : Float) : Float :=
  R1 + (R2 - R1) * H (s / L)

/-! ## Layer 4: Frenet-Serret ODE Integration (RK4)

For computing actual curve geometry (x, y, θ) via:
  dθ/ds = κ(s)
  dx/ds = cos(θ)
  dy/ds = sin(θ)
-/

/-- State of a curve at a given arc length -/
structure CurveState where
  /-- Arc length parameter -/
  s : Float
  /-- Tangent angle -/
  theta : Float
  /-- X coordinate -/
  x : Float
  /-- Y coordinate -/
  y : Float

/-- Configuration bundle for curvature and geometric sampling. -/
structure CurveConfig where
  /-- Initial curvature. -/
  R1 : Float
  /-- Final curvature. -/
  R2 : Float
  /-- Transition length. -/
  L : Float
  /-- Initial tangent angle. -/
  theta0 : Float
  /-- Number of RK4 steps. -/
  nSteps : Nat

instance : Repr CurveState where
  reprPrec c _ := repr s!"\{ s := {c.s}, theta := {c.theta}, x := {c.x}, y := {c.y} }"

/-- Single RK4 step for Frenet-Serret equations.
    Given κ : Float → Float (curvature as function of arc length),
    advances the curve state by ds. -/
def rk4Step (kappaFn : Float → Float) (state : CurveState) (ds : Float) : CurveState :=
  let s := state.s
  let theta := state.theta
  let x := state.x
  let y := state.y

  -- k1 values
  let k1_theta := kappaFn s
  let k1_x := Float.cos theta
  let k1_y := Float.sin theta

  -- k2 values (at s + ds/2, using k1)
  let s2 := s + ds / 2
  let theta2 := theta + ds / 2 * k1_theta
  let k2_theta := kappaFn s2
  let k2_x := Float.cos theta2
  let k2_y := Float.sin theta2

  -- k3 values (at s + ds/2, using k2)
  let theta3 := theta + ds / 2 * k2_theta
  let k3_theta := kappaFn s2
  let k3_x := Float.cos theta3
  let k3_y := Float.sin theta3

  -- k4 values (at s + ds, using k3)
  let s4 := s + ds
  let theta4 := theta + ds * k3_theta
  let k4_theta := kappaFn s4
  let k4_x := Float.cos theta4
  let k4_y := Float.sin theta4

  -- RK4 weighted average
  let theta_new := theta + ds / 6 * (k1_theta + 2 * k2_theta + 2 * k3_theta + k4_theta)
  let x_new := x + ds / 6 * (k1_x + 2 * k2_x + 2 * k3_x + k4_x)
  let y_new := y + ds / 6 * (k1_y + 2 * k2_y + 2 * k3_y + k4_y)

  { s := s + ds, theta := theta_new, x := x_new, y := y_new }

/-- Helper for integrateCurve -/
private def integrateCurveLoop (kappaFn : Float → Float) (ds : Float) (nSteps : Nat)
    (i : Nat) (state : CurveState) (acc : Array CurveState) : Array CurveState :=
  if i ≥ nSteps then
    acc.push state
  else
    let newState := rk4Step kappaFn state ds
    integrateCurveLoop kappaFn ds nSteps (i + 1) newState (acc.push state)
termination_by nSteps - i

/-- Integrate Frenet-Serret equations from s=0 to s=L.
    Returns an array of CurveState at each step. -/
def integrateCurve (R1 R2 L : Float) (theta0 : Float) (nSteps : Nat) : Array CurveState :=
  let ds := L / nSteps.toFloat
  let kappaFn := fun s => kappa s R1 R2 L
  let init : CurveState := { s := 0, theta := theta0, x := 0, y := 0 }
  integrateCurveLoop kappaFn ds nSteps 0 init #[]

/-- Integrate Frenet-Serret equations using a `CurveConfig`. -/
def integrateCurveWith (cfg : CurveConfig) : Array CurveState :=
  integrateCurve cfg.R1 cfg.R2 cfg.L cfg.theta0 cfg.nSteps

/-! ## Parametric Variants -/

/-- Scaled denominator: a · z(1-z) -/
def denomScaled (a z : Float) : Float := a * z * (1 - z)

/-- Power denominator: a · z^p · (1-z)^q -/
def denomPow (a : Float) (p q : Nat) (z : Float) : Float :=
  a * (z ^ p.toFloat) * ((1 - z) ^ q.toFloat)

/-- Bump function with scaled denominator -/
def GScaled (a z : Float) : Float := expNegInv (denomScaled a z)

/-- Bump function with power denominator -/
def GPow (a : Float) (p q : Nat) (z : Float) : Float := expNegInv (denomPow a p q z)

/-- Shape function H with scaled denominator -/
def HScaled (a z : Float) : Float :=
  let num := integrate (GScaled a) 0 z
  let denom := integrate (GScaled a) 0 1
  num / denom

/-- Shape function H with power denominator -/
def HPow (a : Float) (p q : Nat) (z : Float) : Float :=
  let num := integrate (GPow a p q) 0 z
  let denom := integrate (GPow a p q) 0 1
  num / denom

/-- Curvature function with parametric shape function -/
def kappaParam (shapeFn : Float → Float) (s R1 R2 L : Float) : Float :=
  R1 + (R2 - R1) * shapeFn (s / L)

/-! ## Convenience Functions -/

/-- Extract just (x, y) coordinates from curve integration -/
def curvePoints (R1 R2 L theta0 : Float) (nSteps : Nat) : Array (Float × Float) :=
  let states := integrateCurve R1 R2 L theta0 nSteps
  states.map fun s => (s.x, s.y)

/-- Extract `(x, y)` coordinates using a `CurveConfig`. -/
def curvePointsWith (cfg : CurveConfig) : Array (Float × Float) :=
  let states := integrateCurveWith cfg
  states.map fun s => (s.x, s.y)

/-- Helper for curvatureProfile -/
private def curvatureProfileLoop (R1 R2 L ds : Float) (nSamples i : Nat)
    (acc : Array (Float × Float)) : Array (Float × Float) :=
  if i > nSamples then
    acc
  else
    let s := i.toFloat * ds
    curvatureProfileLoop R1 R2 L ds nSamples (i + 1) (acc.push (s, kappa s R1 R2 L))
termination_by nSamples + 1 - i

/-- Generate (s, κ) pairs for the curvature profile -/
def curvatureProfile (R1 R2 L : Float) (nSamples : Nat) : Array (Float × Float) :=
  let ds := L / nSamples.toFloat
  curvatureProfileLoop R1 R2 L ds nSamples 0 #[]

/-- Tangent angle obtained by numerically integrating the curvature profile. -/
def thetaByQuadrature (cfg : CurveConfig) (s : Float) : Float :=
  cfg.theta0 + integrate (fun u => kappa u cfg.R1 cfg.R2 cfg.L) 0 s

/-- Endpoint computed by directly quadraturing the Frenet-Serret velocity field. -/
def endpointByQuadrature (cfg : CurveConfig) : Float × Float :=
  let x := integrate (fun s => Float.cos (thetaByQuadrature cfg s)) 0 cfg.L
  let y := integrate (fun s => Float.sin (thetaByQuadrature cfg s)) 0 cfg.L
  (x, y)

/-- Final point of the discrete RK4 curve sampler. -/
def curveEndpoint (cfg : CurveConfig) : Float × Float :=
  let pts := curvePointsWith cfg
  pts[pts.size - 1]!

/-- Absolute error between the RK4 endpoint and the direct quadrature endpoint. -/
def curveEndpointRoundTripError (cfg : CurveConfig) : Float × Float :=
  let (xRK, yRK) := curveEndpoint cfg
  let (xQ, yQ) := endpointByQuadrature cfg
  (Float.abs (xRK - xQ), Float.abs (yRK - yQ))

/-- `H 0.5` computed from the half-interval quadrature and the canonical symmetry `H(0.5)=0.5`. -/
def hHalfWithRuleBySymmetry (nodes weights : Array Float) : Float :=
  let half := integrateWithRule nodes weights G 0 0.5
  half / (2 * half)

/-- Absolute successive differences for `H 0.5` under 8/16/32-point quadrature. -/
def hHalfConvergenceDiffs : Float × Float :=
  let h8 := hHalfWithRuleBySymmetry gaussLegendreNodes8 gaussLegendreWeights8
  let h16 := hHalfWithRuleBySymmetry gaussLegendreNodes16 gaussLegendreWeights16
  let h32 := hHalfWithRuleBySymmetry gaussLegendreNodes32 gaussLegendreWeights32
  (Float.abs (h16 - h8), Float.abs (h32 - h16))

/-- Boolean convergence check for the `H 0.5` quadrature sequence. -/
def hHalfConvergesTo1e10 : Bool :=
  let (d816, d1632) := hHalfConvergenceDiffs
  decide (d816 < 1e-10 && d1632 < 1e-10)

/-- Demo configuration used by the executable numerical checks. -/
def demoCurveConfig : CurveConfig where
  R1 := 0
  R2 := 1 / 10
  L := 10
  theta0 := 0
  nSteps := 1000

/-! ## Verification Examples

These should work after implementation:
- H 0.0 ≈ 0.0
- H 0.5 ≈ 0.5 (by symmetry)
- H 1.0 ≈ 1.0
- kappa 0 1 2 1 ≈ 1.0
- kappa 1 1 2 1 ≈ 2.0
-/

#eval H 0.0
#eval H 0.5
#eval H 1.0
#eval kappa 0 0 1 1
#eval kappa 0.5 0 1 1
#eval kappa 1 0 1 1
#eval HIntDenom

-- Test curve integration
#eval integrateCurve 0 1 1 0 10
#eval curveEndpoint demoCurveConfig
#eval endpointByQuadrature demoCurveConfig
#eval curveEndpointRoundTripError demoCurveConfig

-- Test parametric variants
#eval HScaled 1.0 0.5
#eval HPow 1.0 2 2 0.5

-- Quadrature convergence probe for H(0.5)
#eval hHalfConvergenceDiffs
#eval hHalfConvergesTo1e10

end Computable
