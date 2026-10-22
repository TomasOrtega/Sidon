import Sidon
import Lean.Util.CollectAxioms

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
    ``Sidon.BandwidthCounterexample.not_exists_uniform_dimension_bandwidth]
  for declaration in declarations do
    let dependencies ← collectAxioms declaration
    let unexpected := dependencies.filter (!allowed.contains ·)
    unless unexpected.isEmpty do
      throwError "Unexpected dependencies for {declaration}: {unexpected}"
    logInfo m!"{declaration}: {dependencies}"
