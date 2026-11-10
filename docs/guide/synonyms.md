# Synonyms: names from other systems and our tools

`guide` with `topic` set to any name in the first column (case does not matter) returns the card of the last column. The second column is what to call here: `tool` names are MCP tools (also `math` function names), the rest are Lisp functions. Names from Mathematica, Maple and other systems are given when they differ.

| Name (Mathematica, Maple, tool) | Here | Topic |
|---|---|---|
| `Simplify`, `FullSimplify`, `simplify`, `radsimp`, `nsimplify` | `simplify` (tool; Lisp `simplify`) | `algebra` |
| `Expand`, `expand`, `ExpandAll` | `expand` | `algebra` |
| `Factor`, `factor`, `FactorTerms` | `factor`, `factor-list` (over the integers) | `algebra` |
| `Together`, `Cancel`, `together`, `cancel`, `normal` | `together` | `algebra` |
| `Apart`, `apart`, `convert/parfrac`, `parfrac` | `apart` | `algebra` |
| `Numerator`, `Denominator`, `numer`, `denom`, `fraction` | `numer`, `denom` | `algebra` |
| `TrigReduce`, `TrigExpand`, `TrigFactor`, `trigsimp`, `combine` | `trigsimp` | `algebra` |
| `gammasimp`, `combsimp` | `combsimp` | `algebra` |
| `Gamma`, `Beta`, `PolyGamma`, `Hypergeometric2F1`, `Hypergeometric1F1`, `HypergeometricPFQ`, `FunctionExpand`, `hyperexpand`, `hyper`, `gamma`, `beta`, `digamma`, `loggamma` | `sf-gamma`, `sf-beta`, `sf-digamma`, `hyperexpand`, `specfun-simplify`, `specfun-check` | `specfun` |
| `RadicalDenest`, `sqrtdenest`, `denest` | `sqrt-denest` | `algebra` |
| `ReplaceAll`, `subs`, `eval`, `Rule`, `Replace` | `subst` (RULE first) | `algebra` |
| `MatchQ`, `Pattern`, `match`, `ReplacePart`, `Rewrite` | `ac-match`, `defrule` | `algebra` |
| `equivalent`, `Equivalent`, `equals`, `is_zero`, `testeq`, `PossibleZeroQ` | `equivalent` (tool) | `algebra` |
| `Solve`, `solve`, `Reduce`, `solve_poly_system`, `solveset`, `NSolve`, `Roots` | `solve` (tool and Lisp) | `solve` |
| `RealRoots`, `real_roots`, `RootIntervals`, `fsolve`, `nroots` | `real-roots` (exact), `isolate-roots` | `solve` |
| `Resultant`, `resultant`, `Discriminant` | `resultant` | `solve` |
| `D`, `Derivative`, `diff`, `Differentiate` | `diff` (tool; Lisp: variable first) | `calculus` |
| `Limit`, `limit`, `Gruntz`, `limitinf` | `limit`, `gruntz-limitinf` | `calculus` |
| `Series`, `series`, `Taylor`, `taylor`, `Laurent`, `SeriesCoefficient` | `series`, `taylor`, `series-coeff` | `calculus` |
| `Integrate`, `int`, `integrate`, `Antiderivative` | `integrate` (tool; Lisp `integrate`) | `integration` |
| `manualintegrate`, `risch_integrate`, `RischNorman`, `DifferentialAlgebra` | `risch-integrate`, `risch-nonelementary?` | `integration` |
| `Erf`, `ExpIntegralEi`, `LogIntegral`, `SinIntegral`, `erf`, `Ei`, `li`, `Si` | `risch-special` | `integration` |
| `DSolve`, `dsolve`, `odeadvisor`, `checkodesol`, `ode`, `DifferentialEquations` | `dsolve`, `dsolve-check` | `ode` |
| `Sum`, `sum`, `summation`, `Gosper`, `SumTools`, `gosper_sum`, `gosper_normal` | `sum` (tool), `sum-symbolic`, `gosper-sum` | `sums` |
| `Product`, `product`, `Prod` | `product-symbolic` | `sums` |
| `RSolve`, `rsolve`, `RecurrenceTable`, `rec` | `rsolve` | `sums` |
| `Zeilberger`, `creative-telescoping`, `WZ` | `zeilberger`, `wz-certificate` | `sums` |
| `LinearRecurrence`, `FindLinearRecurrence`, `FindSequenceFunction`, `holonomic` | `cfinite`, `cf-from-terms`, `cf-prove` | `sums` |
| `Det`, `Determinant`, `det`, `Inverse`, `inverse`, `MatrixRank`, `rank`, `Transpose` | `det`, `inv`, `rank`, `mat-t` | `linear-algebra` |
| `Eigenvalues`, `eigenvals`, `Eigenvectors`, `eigenvects`, `Eigensystem`, `CharacteristicPolynomial`, `charpoly` | `eigenvalues`, `eigenvectors`, `charpoly` | `linear-algebra` |
| `NullSpace`, `nullspace`, `ColumnSpace`, `columnspace`, `RowReduce`, `rref` | `nullspace`, `columnspace`, `rref` | `linear-algebra` |
| `MatrixExp`, `MatrixPower`, `MatrixFunction`, `exp(A)`, `JordanDecomposition`, `jordan_form`, `Diagonalize`, `diagonalize` | `mat-exp`, `mat-power`, `mat-fn`, `jordan-form`, `diagonalize` | `linear-algebra` |
| `Dot`, `Cross`, `Norm`, `dot`, `cross`, `Outer`, `Tensor`, `Dimensions` | `dot`, `cross`, `norm`, `outer`, `shape` | `linear-algebra` |
| `GroebnerBasis`, `groebner`, `gbasis`, `Gröbner`, `fglm`, `Eliminate` | `groebner`, `eliminate`, `fglm`, `normal-form` | `polynomials` |
| `PolynomialGCD`, `PolynomialLCM`, `PolynomialQuotient`, `PolynomialRemainder`, `quo`, `rem` | `poly-gcd`, `poly-lcm`, `poly-quotient`, `poly-remainder` | `polynomials` |
| `CoefficientList`, `Coefficient`, `coeff`, `coeffs`, `Degree`, `degree`, `Exponent` | `coefficients`, `coeff`, `degree` | `polynomials` |
| `FactorExtension`, `Extension`, `AlgebraicNumber`, `factor_extension`, `minpoly`, `MinimalPolynomial`, `RootOf` | `factor-over`, `alg-field`, `alg-minpoly` | `polynomials` |
| `GF`, `FiniteField`, `GaloisField`, `GF(p)`, `FactorMod` | `field-gf`, `gf-field`, `gf-factor` | `polynomials` |
| `FactorInteger`, `ifactor`, `factorint`, `PrimeQ`, `isprime`, `NextPrime`, `nextprime`, `Prime` | `factor-integer`, `prime?`, `next-prime` | `number-theory` |
| `Pratt`, `pratt`, `PrimeCertificate`, `primality certificate` | `pratt-certificate`, `pratt-check` | `number-theory` |
| `PowerMod`, `powmod`, `ModularInverse`, `mod_inverse`, `invert`, `ExtendedGCD`, `igcdex` | `powmod`, `invmod`, `egcd` | `number-theory` |
| `ChineseRemainder`, `chrem`, `crt`, `EulerPhi`, `phi`, `totient`, `Divisors`, `divisors` | `crt`, `totient`, `divisors` | `number-theory` |
| `MultiplicativeOrder`, `n_order`, `PrimitiveRoot`, `primitive_root`, `JacobiSymbol`, `jacobi_symbol`, `sqrt_mod` | `order`, `primitive-root`, `jacobi`, `sqrtmod` | `number-theory` |
| `PellEquation`, `diop_DN`, `pell`, `SquaresR`, `diophantine`, `isolve`, `DiophantineSolve` | `pell`, `sum-of-two-squares`, `solve-linear-diophantine` | `number-theory` |
| `PowersRepresentations`, `sum_of_squares`, `FindInstance` (целые), `diop_linear`, `diop_DN`, `DiscreteLog`, `discrete_log`, `MultiplicativeOrder` | `two-squares`, `four-squares`, `dioph-linear-system`, `dioph-pell`, `discrete-log`, `multiplicative-order` | `number-theory` |
| `SingularPoints`, `singularities`, `Genus`, `genus`, `algcurves`, `RationalParametrization`, `parametrization` | `singular-points`, `curve-genus`, `parametrize-curve` | `curves` |
| `PuiseuxSeries`, `puiseux`, `NewtonPolygon`, `newton_polygon` | `puiseux`, `newton-polygon` | `curves` |
| `Plot`, `plot`, `ListPlot`, `ParametricPlot`, `plot_parametric`, `PolarPlot`, `polarplot`, `plot_implicit`, `implicitplot`, `ContourPlot` | `plot`, `plot-svg`, `plot-implicit` | `plots` |
| `N`, `evalf`, `Interval`, `IntervalArithmetic`, `ball`, `iv`, `interval_arithmetic`, `rigorous` | `iv`, `iv-eval`, `eval-num` (uncertified) | `numerics` |
| `FindRoot`, `NIntegrate`, `NSum`, `RootIsolation`, `certified`, `RealRootIntervals`, `CertifiedIntegral` | `certified-roots`, `isolate-roots`, `certified-integral`, `certified-sum` | `numerics` |
| `ConstantZero`, `IntegerRelation`, `FindIntegerNullVector`, `pslq`, `TranscendentalQ`, `AlgebraicQ`, `is_transcendental`, `constant_zero` | `const-zero?`, `const-relations`, `const-class` | `constants` |
| `Minimize`, `Maximize`, `NMinimize`, `FindMinimum`, `minimize`, `StationaryPoints`, `critical_points` | `extrema`, `critical-points` | `optimization` |
| `LagrangeMultipliers`, `lagrange`, `Hessian`, `hessian` | `lagrange`, `hessian` | `optimization` |
| `LinearProgramming`, `linprog`, `LPSolve`, `simplex`, `lp`, `ilp`, `linear-programming`, `Optimization`, `milp`, `IntegerProgramming` | `linear-programming` (tool), `lp-solve`, `ilp-solve` | `optimization` |
| `Knapsack`, `LongestCommonSubsequence`, `EditDistance`, `FindShortestPath`, `ShortestPath`, `dp`, `DynamicProgramming`, `levenshtein`, `bellman` | `knapsack`, `lcs`, `edit-distance`, `shortest-paths`, `coin-change` | `optimization` |
| `Grad`, `Div`, `Curl`, `Laplacian`, `Gradient`, `Divergence`, `VectorPotential`, `ScalarPotential` | `vf-grad`, `vf-div`, `vf-curl`, `vf-laplacian`, `vf-potential` | `forms` |
| `ExteriorD`, `ExteriorDerivative`, `Wedge`, `WedgeProduct`, `DifferentialForm`, `Hodge`, `HodgeStar`, `Stokes`, `Pullback` | `form-d`, `wedge`, `form-hodge`, `stokes-check`, `form-pullback` | `forms` |
| `LaplaceTransform`, `InverseLaplaceTransform`, `laplace_transform`, `inverse_laplace_transform`, `DiracDelta`, `HeavisideTheta`, `Heaviside`, `Convolve`, `convolution` | `laplace`, `inverse-laplace`, `laplace-check`, `convolve`, `dirac`, `heaviside` | `transforms` |
| `ZTransform`, `InverseZTransform`, `z_transform`, `inverse_z_transform`, `KroneckerDelta` | `ztransform`, `inverse-ztransform`, `ztransform-check`, `zsolve`, `kdelta` | `ztransform` |
| `EulerEquations`, `VariationalD`, `euler_equations`, `EulerLagrange` | `euler-lagrange`, `var-first-integrals` | `variational` |
| `FourierTransform`, `InverseFourierTransform`, `fourier_transform`, `inverse_fourier_transform` | `fourier`, `inverse-fourier`, `fourier-check` | `fourier` |
| `Quantity`, `UnitConvert`, `convert_to`, `convert`, `Units`, `DimensionalAnalysis`, `Buckingham`, `pi-groups`, `NondimensionalizationTransform` | `quantity`, `convert`, `pi-groups`, `dimension-check` | `units` |
| `Assumptions`, `Assuming`, `assume`, `refine`, `Element`, `Reals`, `Integers`, `declare`, `undeclare`, `declarations` | `declare`, `assuming`, `in?` | `domains` |
| `Union`, `Intersection`, `Complement`, `FiniteSet`, `Subset`, `PowerSet`, `Subsets` | `union`, `set-intersection`, `set-difference`, `power-set` | `domains` |
| `three-valued`, `Kleene`, `and3`, `or3`, `not3` | `and3`, `or3`, `not3`, `true?` | `domains` |
| `ShowSolution`, `Student`, `StepByStep`, `step-by-step`, `explain`, `steps`, `Steps`, `attempts` | `steps`, `explain` | `steps` |
