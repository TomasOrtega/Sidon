# Compact smoothing used by the checked Bohr theorems

The checked proof uses a continuous probability bump and Parseval rather than explicit sinc coefficients. It proves the same dimension-uniform approximation statement as blueprint `app:compact-smoothing` and avoids any claim of dimension-uniform finite bandwidth.

Work with probability Haar measure on the unit circle and its finite products. Let `0 < η ≤ 1/2`. Put

\[
 w(t)=\min(1,\max(0,((\eta/2)-\|t\|)/(\eta/4))),\qquad
 c=\int w,\qquad v=w/c.
\]

The ramp is continuous, takes values in `[0,1]`, equals one on the closed ball of radius `η/4`, and vanishes outside the ball of radius `η/2`. The measure of the smaller circle ball is `η/2`: the general ball formula is `min(1,2r)`, and here `r=η/4`. Consequently `c≥η/2>0`, so the normalization is legitimate. We have `v≥0`, `∫v=1`, and `v=0` when `‖t‖>η/2`. Since `w²≤w`,

\[
 \int |v|^2=c^{-2}\int w^2\le c^{-1}\le2/\eta.
\]

These are the theorems in `Sidon/Analysis/CircleBump.lean`; `exists_circleBump` supplies the weaker convenient bound `10/η`.

For dimension `d`, form `V(β)=∏ⱼv(βⱼ)`. Finite-product integration gives `∫V=1` and `∫|V|²=(∫|v|²)^d≤(10/η)^d`. The function is nonnegative. If its maximum-metric argument satisfies `‖β‖>η/2`, at least one coordinate has norm greater than `η/2`, so the corresponding factor vanishes. Thus `V` is supported on the required maximum-metric ball. These product identities and the support argument are checked as `torusTensor_nonneg`, `torusTensor_eq_zero_of_support`, `integral_torusTensor`, and `integral_sq_norm_torusTensor`.

Let `V*(β)=V(-β)` and `g=V*V*`, where convolution means

\[
 (f*h)(x)=\int f(x-y)h(y)\,dy.
\]

All functions are continuous on a compact space. Their integrands, including the product-space integrands used below, are integrable. Fubini and translation invariance therefore apply. They give `g≥0` and `∫g=(∫V)²=1`. If both factors in the integrand for `g(x)` are nonzero, then `‖x-y‖≤η/2` and `‖y‖≤η/2`; the triangle inequality implies `‖x‖≤η`. Hence `g(x)=0` for `‖x‖>η`.

Write `χᵤ(β)=∏ⱼe(uⱼβⱼ)` and `f̂(u)=∫conj(χᵤ(β))f(β)dβ`. The characters multiply under addition of arguments. In the coefficient of a convolution, apply Fubini and substitute `x=z+y` in the inner integral. The factors then separate, proving `(f*h)̂(u)=f̂(u)ĥ(u)`. Reflection combined with complex conjugation sends a coefficient to its conjugate. Therefore

\[
 \widehat g(u)=|\widehat V(u)|^2\ge0.
\]

The tensor characters form a complete orthonormal basis of `L²`: finite-product integration proves orthogonality, and their star algebra separates points by the frequency supported at one coordinate. Stone–Weierstrass gives density in continuous functions; the dense inclusion of continuous functions in `L²` gives completeness. Parseval now proves

\[
 \sum_u|\widehat g(u)|=\sum_u|\widehat V(u)|^2
   =\int|V|^2\le(10/\eta)^d.
\]

This summability is established before using pointwise inversion. The Hilbert-basis expansion converges in `L²`; the coefficient norm bound also gives uniform convergence of the continuous character series. The two limits agree in `L²`, and continuity makes them equal everywhere. `TorusFourier.lean` checks the basis and inversion, and `TorusConvolution.lean` checks the convolution identities and the absolute coefficient sum.

For a real continuous `K`-Lipschitz function `F` with `0≤F≤1`, set `A=F*g`. Positivity and unit mass show `0≤A≤1`. Also

\[
 |A(x)-F(x)|\le\int |F(x-y)-F(x)|g(y)\,dy
 \le K\eta\int g=K\eta,
\]

because the integrand vanishes outside `‖y‖≤η`. The coefficient of `A` is `aᵤ=F̂(u)ĝ(u)`. Probability normalization and `|F|≤1` give `|F̂(u)|≤1`, so `Σ|aᵤ|≤Σ|ĝ(u)|≤(10/η)^d`. The preceding absolute-convergence argument proves the character series equals `A` pointwise and uniformly. This is `Sidon.exists_torus_smoothing`.

Finally, an integer orbit evaluates `χᵤ(xα)` at the one-dimensional frequency `Σⱼuⱼαⱼ`. If an integer coefficient function `f` has Fourier transform bounded by `D`, its test against this series is bounded by `DΣ|aᵤ|`. Finite summation interchanges with an absolutely convergent series. Changing `F` to `A` costs at most `KηΣₓ|f(x)|`. Hence

\[
 \left|\sum_x f(x)F(x\alpha)\right|
 \le K\eta\sum_x|f(x)|+D(10/\eta)^d.
\]

This is `Sidon.norm_torusTest_le_compact_smoothing`. For the difference of normalized counting measures, the coefficient norm sum is at most two. Fourier uniformity and `|S|≥√N/100` give `D≤1600√E`. The resulting scalar optimization, checked separately in `SmoothingOptimization.lean`, yields the absolute constant `48000` in `Sidon.sidon_smooth_equidistribution`.
