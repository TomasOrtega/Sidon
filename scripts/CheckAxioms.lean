module

public import Sidon
public import Lean.Util.CollectAxioms

@[expose] public section

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``Sidon.sidon_fourier_uniformity,
    ``Sidon.sidon_improved_fourier_uniformity,
    ``Sidon.sidon_smooth_equidistribution,
    ``Sidon.sidon_regular_bohr_equidistribution,
    ``Sidon.FourierSpace.colouring_dense_model,
    ``Sidon.QuantitativeRado.exists_many_monochromatic_linearSolutions,
    ``Sidon.sidon_partition_regularity,
    ``Sidon.BoseChowla.exists_prime_sidon,
    ``Sidon.NumberTheory.Tauberian.WeakPNT,
    ``Sidon.relativePrimeIntervals,
    ``Sidon.eventually_exists_sharp_odd_obstruction,
    ``Sidon.BandwidthCounterexample.not_exists_uniform_dimension_bandwidth,
    ``Sidon.exists_logarithmicZetaZeroFreeWidth,
    ``Sidon.exists_riemannZeta_critical_growth,
    ``Sidon.card_mul_jensen_mass_le_integral,
    ``Sidon.verticalL2_logConvex,
    ``Sidon.gaussian_integral_of_cumulative,
    ``RiemannGaussian.RosserSchoenfeldExplicitFormula.finite_prime_explicitFormula,
    ``RiemannGaussian.RosserSchoenfeldZeroMass.norm_square_mass_summable,
    ``Sidon.integral_circleAverage_vertical_le,
    ``Sidon.smoothed_explicit_formula,
    ``Sidon.zetaZeroCount_zero_le_fourThirds,
    ``Sidon.exists_uniformZetaZeroDensity,
    ``Sidon.exists_primeIntervalBound_two_thirds,
    ``Sidon.largest_sidon_fourier_uniformity,
    ``Sidon.QuantitativeRado.exists_finite_colouring_without_monochromatic_linearSolution,
    ``Sidon.QuantitativeRado.exists_integer_colouring_without_positive_monochromatic_linearSolution]
  for declaration in declarations do
    let dependencies ← collectAxioms declaration
    let unexpected := dependencies.filter (!allowed.contains ·)
    unless unexpected.isEmpty do
      throwError "Unexpected dependencies for {declaration}: {unexpected}"
    logInfo m!"{declaration}: {dependencies}"
