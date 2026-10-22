# The Ingham route to the remaining prime-interval input

This document expands the quantitative route needed for Corollary 1.4.
It does not declare its analytic prerequisites proved in Lean. The finite
zero-layer estimate, actual finite zero occurrences, prime-power removal,
and the Bose–Chowla/extremal-set reductions are checked separately. The
unproved analytic obligations are identified at the end.

The source is A. E. Ingham, *On the difference between consecutive primes*,
Quarterly Journal of Mathematics 8 (1937), 255–266,
[DOI](https://doi.org/10.1093/qmath/os-8.1.255),
[primary scan](https://www.dustri.org/b/files/On_the_difference_between_consecutive_primes_-_A.E.Ingham.pdf).
The scan's printed pages 259–263 were inspected as images: mathematical
OCR loses several essential exponents. The arguments below supply
independent elementary proofs of the divisor estimates and a direct
three-lines proof of the interpolation step.

## 1. Exact target and conventions

For real `x`, let

\[
 \psi(x)=\sum_{1\le n\le x}\Lambda(n),\qquad
 \vartheta(x)=\sum_{p\le x}\log p.
\]

A sum over natural integers uses the floor of its real endpoint. At an
integer endpoint, `psi` includes its full Mangoldt weight. A symmetric
Perron formula instead gives half weight; the difference is at most
`log x` and must be retained in the error estimate.

We seek absolute `C>0` and `X` such that every real `x≥X` has a prime

\[
 x-Cx^{2/3}\le p\le x.
\tag{P}
\]

Natural endpoint versions must be transferred to all real `x`: apply the
natural statement to `N=floor x`, use `x-1<N≤x`, and absorb the one-unit
loss into `Cx^(2/3)`. This is valid after `x≥1`, when `x^(2/3)≥1`.
No subsequence of endpoints is sufficient.

Write a nontrivial zero as `rho=beta+i gamma`; all zero sums count its
analytic multiplicity. We use positive heights in `N(sigma,T)` and both
signs in the explicit formula. Complex conjugation doubles the
positive-height bound; no simplicity of zeros is assumed.

The fixed parameters used below are

\[
 c=7/32,\quad A=2+4c=23/8,\quad
 \tau=17/50,\quad \theta=2/3.
\tag{1}
\]

They satisfy `A*tau=391/400<1` and `1-tau=33/50<theta`.
Thus there is room both for the zero-density sum and for the contour
truncation error. Numerical thresholds need not be evaluated: the final
paper statement is asymptotic. Every implicit constant below is uniform
in the variables explicitly quantified in the accompanying statement.

## 2. The arithmetic estimates used by the mean square

Let `d(n)` count positive divisors and `H_m=sum_(1≤j≤m)1/j`. Integral
comparison gives `H_m≤1+log m` for `m≥1`.

### 2.1. The second moment of the divisor function

For every integer `x≥2`,

\[
 \sum_{n\le x}d(n)^2\le x(1+\log x)^3.
\tag{2}
\]

For fixed `n`, a pair of divisors `(d1,d2)` determines the ordered
factorization

\[
 (a,b,c,e)=(\gcd(d1,d2),d1/a,d2/a,n/\operatorname{lcm}(d1,d2)).
\]

All four entries are positive integers and `a*b*c*e=n`, because
`lcm(d1,d2)=a*b*c`. This map is injective: recover `d1=a*b` and
`d2=a*c`. Consequently `d(n)^2≤d_4(n)`, where `d_4(n)` counts ordered
factorizations of `n` into four positive factors. Summing and then
forgetting the restriction on the first three factors gives

\[
 \sum_{n\le x}d_4(n)
 =\sum_{abc\le x}\lfloor x/(abc)\rfloor
 \le x\sum_{a,b,c\le x}(abc)^{-1}=xH_{\lfloor x\rfloor}^3.
\]

The same bound holds for real `x≥2` by replacing the summation endpoint
by its floor and using monotonicity of `log`.

### 2.2. The logarithmic off-diagonal sum

Uniformly for real `x≥2`,

\[
 S(x):=\sum_{1\le m<n\le x}
 {d(m)d(n)\over\sqrt{mn}\log(n/m)}
 \ll x(1+\log x)^3.
\tag{3}
\]

First split at `m=n/2`. In the far part `log(n/m)≥log 2`; hence that
part is at most

\[
 {1\over\log2}\left(\sum_{n\le x}{d(n)\over\sqrt n}\right)^2
 \ll x(1+\log x)^2.
\]

Here `sum_(n≤u)d(n)≤u(1+log u)`, obtained by counting pairs `ab≤u`, and
summation by parts give the displayed weighted estimate.

For the near part, put `h=n-m`, so `1≤h<n/2`. The inequality
`log(1+v)≥v/(1+v)` for `v≥0`, obtained by integrating `1/(1+t)`, gives

\[
 {1\over\sqrt{mn}\log(n/m)}\le {n\over h\sqrt{mn}}
 \le {\sqrt2\over h}.
\]

We need a uniform shifted divisor estimate. Every divisor of `n` is
paired with `n/d`; thus

\[
 d(n)\le2\sum_{a\le\sqrt x}1_{a\mid n}\qquad(1\le n\le x).
\]

For `a,b≤sqrt x`, the simultaneous congruences `a|m`, `b|m+h` have
solutions only when `gcd(a,b)|h`. If that divisibility holds, the
solutions form one residue class modulo `lcm(a,b)`; in an interval of
length at most `x` there are at most `x/lcm(a,b)+1` solutions. Therefore

\[
 \sum_{m\le x-h}d(m)d(m+h)
 \le4x\left((1+\log x)^2\sum_{g\mid h}{1\over g}+1\right).
\tag{4}
\]

For the first term, write `a=g*u,b=g*v` with `g=gcd(a,b)`; dropping
`gcd(u,v)=1` bounds the corresponding reciprocal sum by
`(1/g)*H_(floor(sqrt x/g))^2`. For the second term, simply count at
most `floor(sqrt x)^2≤x` pairs `(a,b)`; the congruence compatibility
restriction may be dropped in this upper bound.

Finally,

\[
 \sum_{h\le x}{1\over h}\sum_{g\mid h}{1\over g}
 =\sum_{g\le x}{1\over g^2}H_{\lfloor x/g\rfloor}
 \le(1+\log x)\sum_{g\ge1}g^{-2}\ll1+\log x.
\]

Sum (4) against `sqrt(2)/h`. Together with the far part this proves (3),
with a single constant independent of `h` and `x`.

### 2.3. Two convergent tails

For `X≥2` and `0<xi<3`, Tonelli and (2) imply

\[
 \sum_{n\ge X}{d(n)^2\over n^{1+\xi}}
 \le {C\over \xi X^\xi}(\xi^{-1}+\log X)^3.
\tag{5}
\]

Use `n^(-1-xi)=integral_n^infinity (1+xi)u^(-2-xi)du`, interchange the
nonnegative sum and integral, and bound its counting function by
`C*u*log(u)^3`. Substitute `u=X*exp(v)`; the remaining integral is a
linear combination of `integral_0^infinity exp(-xi*v)*v^j dv=j!/xi^(j+1)`
for `0≤j≤3`. These identities follow by integration by parts, with
boundary limits supplied by exponential domination of powers.

For `0<delta<1`,

\[
 \sum_{n>m\ge X}
 {d(m)d(n)\over(mn)^{1+\delta}\log(n/m)}\ll\delta^{-4}.
\tag{6}
\]

This does not follow merely by inserting a weight depending on `n` into
(3); that would mishandle small `m`. The required split is as follows.
For `lambda>1`, `1≤log lambda+lambda^(-1/2)`, since the right-hand side
is increasing from one. Multiply this inequality by the summand. The
result is bounded by the sum of

\[
 {d(m)d(n)\over(mn)^{1+\delta}},\qquad
 {d(m)d(n)\over n^{1+\delta}\sqrt{mn}\log(n/m)}.
\]

In the second term we used `m^delta≥1`. The first double sum is at most
`zeta(1+delta)^4≪delta^(-4)` by the absolutely convergent divisor
Dirichlet series and the integral bound `zeta(1+delta)≤1+1/delta`.
For the second, use the cumulative function `S(u)` from (3) and
summation by parts; its bound is at most

\[
 C(1+\delta)\int_1^\infty u^{-1-\delta}(1+\log u)^3du
 \ll\delta^{-4}.
\]

All interchanges here involve nonnegative summands, so no conditional
rearrangement is being used.

## 3. The mollifier and its two endpoint mean squares

For real `X≥2`, put

\[
 M_X(s)=\sum_{1\le n<X}\mu(n)n^{-s},\qquad
 f_X(s)=\zeta(s)M_X(s)-1.
\]

The strict inequality `n<X` is intentional. For `Re s>1`, absolute
Dirichlet-series multiplication gives

\[
 f_X(s)=\sum_{n\ge X}a_X(n)n^{-s},\qquad
 a_X(n)=\sum_{d\mid n,\ d<X}\mu(d).
\tag{7}
\]

For `1<n<X`, every divisor satisfies `d<X`, so the full Möbius divisor
sum is zero. The constant coefficient cancels the subtracted one.
Always `|a_X(n)|≤d(n)`.

For any real frequency `u≠0`,

\[
 \left|\int_0^T e^{itu}dt\right|\le2/|u|.
\tag{8}
\]

This follows from its explicit antiderivative. Expand the square of
(7), first for a finite truncation; (5) and (6) then justify passage to
the infinite limit by an absolutely summable diagonal/off-diagonal
majorant. The diagonal and the pair of conjugate off-diagonal terms
give

\[
 \int_0^T|f_X(1+\delta+it)|^2dt
 \le T\sum_{n\ge X}{d(n)^2\over n^{2+2\delta}}
   +4\sum_{n>m\ge X}{d(m)d(n)\over(mn)^{1+\delta}\log(n/m)}.
\]

Apply (5) with `xi=1+2delta` and (6). The elementary maximum bound
`u^j*exp(-2delta*u)≤C_j*delta^(-j)` for `u≥0, j≤3` absorbs `log X`.
We obtain, uniformly in `X≥2,T≥0,0<delta<1`,

\[
 \int_0^T|f_X(1+\delta+it)|^2dt
 \ll (T/X+1)\delta^{-4}.
\tag{9}
\]

At the other boundary we need a zeta growth exponent `0<c<1/2`:

\[
 |\zeta(1/2+it)|\le C_c(1+|t|)^c\quad(t\in\mathbb R).
\tag{G_c}
\]

The factor `1+|t|` handles bounded heights. Expanding the finite
Dirichlet polynomial and using (8),

\[
 \int_0^T|M_X(1/2+it)|^2dt
 \le T\sum_{n<X}{1\over n}
   +4\sum_{m<n<X}{1\over\sqrt{mn}\log(n/m)}
 \ll(T+X)\log(2X).
\tag{10}
\]

Indeed the kernel is at most `1/sqrt(mn)+1/(n-m)`, using
`1/log lambda≤1+sqrt(lambda)/(lambda-1)`. The two resulting sums are
`O(X)` and `O(X log(2X))`. Since `|z-1|^2≤2|z|^2+2`, (G_c) and
(10) imply for `T≥1`

\[
 \int_0^T|f_X(1/2+it)|^2dt
 \ll T^{2c}(T+X)\log(2X).
\tag{11}
\]

For `0≤T≤1`, boundedness of zeta on the compact segment and
`|M_X|≤sum_(n<X)n^(-1/2)≪sqrt X` give `O(TX)`. Since `2c<1`,
`T≤T^(2c)` in this range, so (11) extends to every `T>0`.

## 4. Interpolation, with its analytic justification

The pole of `f_X` at one prevents direct use of three-lines. For
`R≥2`, define

\[
 \Phi(s)={s-1\over s\cos(s/(2R))}f_X(s).
\tag{12}
\]

In `1/2≤Re s≤1+delta`, the factor `s-1` removes the possible pole;
`s` does not vanish. The zeros of the cosine are real and the first
positive one is `pi R`, outside this strip. Thus `Phi` is holomorphic
on a neighborhood of the strip. Its absolute value is bounded by
`C*exp(-|Im s|/(2R))*|f_X(s)|`. On every smaller horizontal compact
range of real parts, the same bound holds for its derivatives, by
Cauchy's integral estimate on a fixed-radius disc. Polynomial growth
of zeta on fixed vertical strips consequently makes the line integrals
below absolutely convergent and permits differentiation under the
integral sign.

Let `J(u)=integral_R |Phi(u+it)|^2 dt`. Then

\[
 J((1-v)a+vb)\le J(a)^{1-v}J(b)^v\quad(0\le v\le1)
\tag{13}
\]

for `a=1/2,b=1+delta`. Here is a direct proof from three-lines.
For any compactly supported continuous `g` with `L2` norm one, the
function

\[
 F_g(z)=\int_{\mathbb R}\Phi(z+it)\overline{g(t)}dt
\]

is holomorphic in the strip and bounded there. Cauchy–Schwarz and the
translation invariance of Lebesgue measure give
`|F_g(a+iy)|≤sqrt J(a)` and `|F_g(b+iy)|≤sqrt J(b)` for every real `y`.
The scalar three-lines theorem gives
`|F_g(u)|≤J(a)^((1-v)/2)*J(b)^(v/2)`. By density of compactly supported
continuous functions in `L2`, the supremum of the left side over these
`g` equals `sqrt J(u)`: approximate the normalized conjugate-pairing
vector `Phi(u+it)/sqrt J(u)` in `L2`; if `J(u)=0`, the desired inequality
already holds. Squaring proves (13). This also covers a zero boundary
norm by first adding a positive epsilon to the scalar boundary bounds
and taking its limit to zero.

Integrating the endpoint cumulative estimates (9), (11) against
`exp(-t/R)` and using integration by parts gives

\[
 J(1+\delta)\ll(R/X+1)\delta^{-4},\qquad
 J(1/2)\ll R^{2c}(R+X)\log(2X).
\tag{14}
\]

For `1≤t≤T`, choose `R` to be a fixed sufficiently large multiple of
`T`; then the prefactor in (12) is bounded below by a positive
absolute constant. Combining (13) and (14), and putting
`delta=1/log(T+X)` after enlarging the harmless lower threshold, yields

\[
 \int_1^T|f_X(\sigma+it)|^2dt
 \ll T^{4c(1-\sigma)}X^{1-2\sigma}(T+X)\log^4(T+X)
\tag{15}
\]

uniformly for `1/2≤sigma≤1,T≥2,X≥2`. To check the exponent bookkeeping,
the interpolation weight of the left boundary is
`(1+delta-sigma)/(1/2+delta)`. Its difference from `2(1-sigma)` is
`O(delta)`, uniformly in `sigma`. All extra powers of `T` and `X`
are therefore bounded by `exp(C*delta*log(T+X))≤exp C`.
The factor `(R+X)` has total interpolation exponent one, and the
`X` exponent is `-(sigma-1/2)/(1/2+delta)=1-2sigma+O(delta)`.
Finally the product of logarithmic factors has exponent at most four.
Compact ranges omitted in choosing `delta<1` are absorbed by enlarging
the single constant.

## 5. From the mollifier to a uniform zero-density bound

Set `h_X=1-f_X^2=zeta*M_X*(2-zeta*M_X)`. At a zeta zero of
multiplicity `m` away from the pole, `h_X` vanishes to order at least
`m`; multiplication by the remaining holomorphic factor can only add
zeros. Also

\[
 \log|h_X|\le\log(1+|f_X|^2)\le|f_X|^2.
\tag{16}
\]

For `Re s≥2`, (7) and `d(n)≤2sqrt n` give
`|f_X(s)|≤C X^(-1/2)`. Choose one absolute `X_min` so large that
`|f_X(s)|^2≤1/2` on this half-plane whenever `X≥X_min`. Then
`Re h_X≥1/2`, and

\[
 |\log|h_X(2+it)||\le C/X.
\tag{17}
\]

For `T≥4`, choose heights `T1∈(3,4)` and `T2∈(T,T+1)` at which no
zero lies on either horizontal segment from `sigma0` to two. Such
choices exist because the zeros in the relevant compact rectangles
are finite. Avoid vertical zero boundaries initially as well; all
endpoint versions follow by one-sided limits and monotonicity.
The zero at the pole is absent from this rectangle because `T1>0`.

Littlewood's rectangle identity, counting analytic multiplicity, is

\[
 2\pi\int_{\sigma_0}^{2}N_h(u;T_1,T_2)du
 =\int_{T_1}^{T_2}\log\left|{h_X(\sigma_0+it)\over h_X(2+it)}\right|dt
 +\int_{\sigma_0}^{2}[\arg h_X(u+iT_2)-\arg h_X(u+iT_1)]du.
\tag{18}
\]

The argument branch starts on the zero-free right edge, where
`Re h_X>0`. Formula (18) follows by integrating the logarithmic
derivative around an indented zero-free rectangle and applying the
argument principle, then integrating in the left edge; each zero
contributes its multiplicity times its horizontal distance from that
edge. The real and imaginary boundary contributions give exactly the
two terms displayed. This proof requires the argument principle for
meromorphic functions and a justified limit around the finitely many
small indentation circles.

The horizontal argument term is `O(log(T+X))`, uniformly in `sigma0`.
To see this, for `r=1,2`, reflect the analytic function to obtain

\[
 H_r(z)=\tfrac12(h_X(z+iT_r)+\overline{h_X(\overline z+iT_r)}).
\]

For real `u`, this is `Re h_X(u+iT_r)`. On the disc centered at two
of outer radius `7/4`, it is holomorphic: the possible shifted poles
have imaginary parts of absolute value greater than three. Its value
at two is at least `1/2`. Zeta polynomial growth on a fixed strip and
the finite bound `|M_X|≤C X^C` give an outer maximum at most
`C(T+X)^C`. Jensen's formula bounds the number of zeros in the inner
disc of radius `3/2` by

\[
 {\log(C(T+X)^C)-\log(1/2)\over\log((7/4)/(3/2))}
 \ll\log(T+X).
\]

That inner disc contains the real segment `[sigma0,2]` for every
`sigma0≥1/2`. Between successive zeros of the real part, the argument
remains in a fixed interval of length `pi`; moving through each such
zero changes its continuous branch by at most one further `pi`.
The zero-free right edge supplies the initial bounded argument.
This proves the required horizontal bound.

Insert (15)–(17) into (18), and discard the nonnegative zeros of the
other factors of `h_X`. We obtain

\[
 \int_{\sigma_0}^{2}N_\zeta(u;T_1,T_2)du
 \ll T^{4c(1-\sigma_0)}
       [TX^{1-2\sigma_0}+X^{2(1-\sigma_0)}]\log^4(T+X).
\tag{19}
\]

The terms `T/X` and `log(T+X)` are absorbed by the displayed expression
for `sigma0≤1,T≥4,X≥X_min`. For `delta>0`, monotonicity in `u` gives

\[
 \delta N_\zeta(\sigma_0+\delta;T_1,T_2)
 \le\int_{\sigma_0}^{\sigma_0+\delta}N_\zeta(u;T_1,T_2)du.
\]

Put `X=T`, `delta=1/log T`. For `sigma≥1/2+delta`, apply (19) at
`sigma0=sigma-delta`; the change in a power of `T` costs only a fixed
factor. The `1/delta` adds one logarithm. The finitely many zeros below
height four are absorbed into the constant. For
`1/2≤sigma<1/2+delta`, the crude total count `N(0,T)≪T log T` suffices,
because `A/2>1`. For `0≤sigma≤1/2`, that same crude count is bounded
by `T^(A*(1-sigma))*log^5T`, again because `A/2>1`. Thus

\[
 N(\sigma,T)\le K T^{A(1-\sigma)}(\log T)^5
 \quad(0\le\sigma\le1,\ T\ge T_0),\qquad A=2+4c.
\tag{D_A}
\]

There is one `K,T0`, independent of `sigma`. A separate estimate for
each fixed `sigma` would not justify the later moving-layer argument.

## 6. A deliberately weaker sufficient critical-line estimate

The implementation only needs an exponent strictly below `1/4`. The
following elementary derivative route obtains

\[
 |\zeta(1/2+it)|\ll |t|^{3/16}\log(2|t|),
 \tag{20}
\]

which is sufficient: `log t=o(t^(1/32))`, so it implies (G_c) with
`c=7/32`. This avoids paying for the optimal second-derivative test.

First consider a finite sequence `z_n=exp(2*pi*i*f(n))` whose successive
phase increments `theta_n=f(n+1)-f(n)` are monotone and stay in one
interval `[m+delta,m+1-delta]`, where `m` is an integer and
`0<delta≤1/2`. Put

\[
 b(u)=(1-e^{2\pi i u})^{-1}.
\]

Since `z_n=b(theta_n)*(z_n-z_(n+1))`, discrete summation by parts
bounds `|sum z_n|` by twice the supremum of `|b|` plus the total
variation of `b(theta_n)`, with at most one final endpoint term.
On that interval,
`|1-exp(2*pi*i*u)|=2|sin(pi*u)|≥4*delta`.
Also `|b'(u)|≤2*pi/(4*delta)^2`. Monotonicity of `theta_n` and the
fundamental theorem of calculus therefore give total variation at most
`C*delta^(-2)`; the parameter interval has length at most one.
Thus

\[
 |\sum z_n|\ll\delta^{-2}.
 \tag{21}
\]

No cotangent identity is needed. Each division has a denominator bounded
away from zero, and truncating a block only changes its two endpoints.

Now suppose a phase has second derivative of constant sign with
`lambda≤|f''|≤C*lambda` on an interval of length at most `N+2`.
Reflect the phase if necessary. Its discrete increments are increasing,
with each successive increment difference between `lambda` and
`C*lambda`; this follows by integrating `f''` over two adjacent unit
intervals. Their total range has length at most `C*lambda*N`.
Call an index bad when its increment is within `delta` of an integer.
There are `O(lambda*N+1)` relevant integers and at most
`O(delta/lambda+1)` bad indices at each one. Removing them leaves
`O(lambda*N+1)` good runs, each governed by (21). Consequently

\[
 |\sum z_n|\ll N\delta+\lambda N+
      \delta/\lambda+1+(\lambda N+1)\delta^{-2}.
\]

For `0<lambda≤1/8`, take `delta=lambda^(1/3)`; every term is bounded by
`C*(N*lambda^(1/3)+lambda^(-2/3))`. For `lambda>1/8`, the trivial bound
`N` is already at most `2*N*lambda^(1/3)`. We have proved the weaker
but sufficient second-derivative test

\[
 |\sum z_n|\ll N\lambda^{1/3}+\lambda^{-2/3}.
 \tag{22}
\]

Apply differencing to `f(u)=-(t/(2*pi))*log u` on `N<n≤2N`.
The shift-`h` difference phase has second derivative comparable to
`h*|t|/N^3`, with one sign. Test (22), followed by summing `h^(1/3)`
and `h^(-2/3)`, gives

\[
 |S|^2\ll N^2/H+N|t|^{1/3}H^{1/3}
                   +N^3|t|^{-2/3}H^{-2/3}.
 \tag{23}
\]

If `N<|t|^(1/3)`, the trivial weighted sum bound `sqrt N` is at most
`|t|^(1/6)`. Otherwise choose the positive integer `H` comparable to
`N^(3/4)*|t|^(-1/4)`, rounded up. This quantity lies between one and
`N`; since `N` is an integer, its ceiling is still at most `N`.
Equation (23), square roots, and division by `sqrt N` then give

\[
 N^{-1/2}|S|\ll N^{1/8}|t|^{1/8}
                       +N^{3/4}|t|^{-1/4}.
\]

For `N≤C*sqrt |t|`, these terms are `O(|t|^(3/16)+|t|^(1/8))`.
The same bound holds uniformly for every partial dyadic block, so
partial summation also permits the coefficient `n^(-1/2)`.

The symmetric approximate functional equation at the critical line
has two Dirichlet polynomials of lengths comparable to `sqrt |t|`,
with coefficients `n^(-1/2)` and `n^(-1/2)` times a factor of absolute
value one, plus an `O(|t|^(-1/4))` remainder. Each dyadic block therefore
costs `O(|t|^(3/16))`. There are `O(log(2|t|))` blocks, proving (20).

There is also a route that avoids the approximate functional equation
entirely, if sharp first- and second-derivative estimates are reused.
For `s=1/2+it` and an integer `X` comparable to `t^2`, Euler summation
and analytic continuation give

\[
 \zeta(s)=\sum_{n\le X}n^{-s}+{X^{1-s}\over s-1}
             -s\int_X^\infty\{u\}u^{-s-1}du.
\]

The integral is absolutely convergent and bounded by
`2|s|/sqrt X=O(1)`, while the pole term is `O(sqrt X/|t|)=O(1)`.
The sign of the fractional-part term does not affect the bound, but
its endpoint convention must agree with the finite sum.
The polynomial extends to `X` rather than `sqrt |t|`; divide it into
these four ranges, retaining uniform estimates for partial blocks:

- `N≤|t|^(1/3)`: the trivial weighted sum is `O(|t|^(1/6))`.
- `|t|^(1/3)≤N≤|t|^(2/3)`: the sharp third-derivative estimate gives
  weighted bound `O(|t|^(1/6)+|t|^(-1/6)*sqrt N)=O(|t|^(1/6))`.
- `|t|^(2/3)≤N≤C|t|`: the sharp second-derivative test with
  `lambda≈|t|/N^2` gives weighted bound
  `O(sqrt(|t|/N)+sqrt(N/|t|))=O(|t|^(1/6))`.
- `C|t|≤N≤C'|t|^2`: choose fixed `C` large enough that all phase
  increments lie between `c|t|/N` and `1/2`. The sharp first-derivative
  bound is `O(N/|t|)`, hence weighted `O(sqrt N/|t|)=O(1)`.

Summing `O(log |t|)` dyadic blocks gives the stronger Weyl estimate
`|zeta(1/2+it)|≪|t|^(1/6)log(2|t|)` with only first Euler summation,
not a Mellin/gamma contour proof of an approximate functional equation.
The strong first-derivative bound itself can be obtained from the Abel
proof above by integrating the derivative bound instead of taking its
supremum: `|b'(u)|≤C*min(u,1-u)^(-2)` has integral `O(1/delta)` on
`[delta,1-delta]`. The good/bad integer-band proof then balances at
`delta=sqrt lambda`, producing the sharp second-derivative test.
The strong third-derivative test follows by one differencing step and
`H≈N*|t|^(-1/3)`, as in the parameter computation of the original Weyl
route. This gives a complete elementary analytic dependency plan whose
proofs are shorter than the approximate-functional-equation route.

The exact existing primary Lean theorem is now identified:
`RiemannGaussian.ZetaEulerLineBound.bound_abs` at the audited revision,
with `k=1`, has `line 1=1/2` and `alpha 1=1/6`, and bounds the literal
zeta function by `8192*|t|^(1/6)*log|t|` for `|t|≥2`. Its direct-Euler
and dyadic assembly is already present in that source. This is a
checked-source candidate undergoing current-toolchain compilation and
axiom audit; it is not an imported Sidon theorem until that audit passes.
The applications agent owns the specialization and logarithm absorption;
its detailed source audit is in `docs/weyl-subconvexity-research.md`. The density proof remains generic in `c`; the safe
choice `7/32` used in this document accepts either the weak estimate
(20) or the stronger Euler-summation Weyl estimate.

## 7. Exact zero-free strength required

A fixed classical region `1-beta≥a/log T` is insufficient here: the
remaining density bound has a factor `(log T)^5`. Even replacing `a`
by an arbitrary fixed constant does not, by itself, absorb that factor.
A sufficient region is any positive function `eta(T)` satisfying

\[
 N(1-\eta(T),T)=0,\qquad
 {\eta(T)\log T\over\log\log T}\longrightarrow\infty.
\tag{ZF}
\]

Boundary inclusion can be handled by replacing the width by half its
value. Fixed low-height zeros do not create an exception: there are
finitely many in a bounded rectangle, none on `Re s=1`, so their
positive distances from that line have a positive minimum. Shrink the
width below that minimum after increasing the threshold.

Ingham invokes Tchudakoff's zero-free region of width
`(log T)^(-a)` with `a<1`. Its ratio in (ZF) tends to infinity because
`log log T=o((log T)^(1-a))`. The stronger Vinogradov–Korobov width
`C/(log T)^(2/3)/(log log T)^(1/3)` also satisfies (ZF).
Neither region follows from the fixed-order critical-line estimate (20).
A proof must retain the high-order exponential-sum bounds, their
constants as the order grows with `T`, and the analytic zero detector.

A new primary Lean source was found during the latest-version audit:
[David Sanftenberg's RiemannGaussian](https://github.com/dbsanfte/RiemannGaussian/tree/6e969fd6e9c639eed280c595732248c106187603)
contains `ZetaVinogradovSummedZeroFree.exists_eventual_strip` for actual
zeta zeros, with no zeta-growth or zero-free hypothesis in its theorem
type. It states an eventual VK region for every
`0<C<3*pi/10640`. Its raw local import closure has 1067 modules and
266100 lines, including unrelated option-bearing proof files. The
repository has not yet been imported or accepted as a checked Sidon
dependency. Exact proof closure, current-toolchain compilation, standard
axiom audit, and removal of forbidden options remain required before
it can discharge (ZF) here.

## 8. The truncated explicit formula and its endpoints

The precise sufficient formula is: for all sufficiently large `x`,
with `h=x^(2/3)` and a height `U` in `[x^tau,2*x^tau]` chosen away from
zero ordinates,

\[
 \psi(x)-\psi(x-h)
 =h-\sum_{|\gamma|\le U}{x^\rho-(x-h)^\rho\over\rho}+R(x),
 \qquad |R(x)|\le C[x\log^2x/U+\log x].
\tag{EF}
\]

The zero sum includes multiplicities. A stronger uniform formula for
every `U` must not be assumed: horizontal contour edges can approach
zeros. The proof chooses one admissible height in `[T,2T]`; replacing
`T` by `2T` in the density bound changes only the constant.

A complete contour proof can be organized as follows.

1. On `Re s=a=1+1/log x`, use the absolutely convergent identity
   `-zeta'/zeta(s)=sum_n Lambda(n)n^(-s)`. Truncate the Perron integral
   `integral_(a-iU)^(a+iU) (-zeta'/zeta(s))*y^s/s ds/(2pi i)`.
   The scalar truncated Perron kernel differs from `1_(n<y)` by at most
   `C*(y/n)^a*min(1,1/(U*|log(y/n)|))`, with half value at equality.
   Prove this by integrating `exp(s*log(y/n))/s`, closing the contour
   to the appropriate side, and bounding the two tails by integration
   by parts.
2. Summing against `Lambda(n)≤log n`, partition `n` into
   `n≤y/2`, `y/2<n<2y`, `n≥2y`. The outer ranges are bounded by integral
   comparisons. In the middle range use
   `|log(y/n)|≥c*|y-n|/y`; summing reciprocal distances costs at most
   `log y`, with the nearest integer term treated by the `min(1,...)`.
   This gives `O(y*log^2(yU)/U+log y)` uniformly, including integer `y`.
3. Shift the contour left past the simple pole of `-zeta'/zeta` at
   one and its poles at the nontrivial zeros. Their residues are one
   and minus the zero multiplicities. Trivial zeros and the factor
   `1/s` contribute the usual bounded/logarithmic elementary terms;
   these remain `O(log x)` after subtracting the formulas at `x` and
   `x-h`.
4. Choose `U∈[T,2T]` separated from zero ordinates. The local zero count
   in each unit interval is `O(log(T+2))`; a measure pigeonhole argument
   finds a common height at distance at least `c/log(T+2)` from every
   relevant ordinate. The logarithmic derivative's partial-fraction
   expansion and that separation bound the horizontal edges by
   `O(x*log^2(xT)/T)`. A global height count alone is not sufficient
   for this local separation estimate.
5. Let the left edge tend left, using the functional equation and gamma
   estimates to control the horizontal and remaining vertical tails.
   The finite contour formulas converge to the asserted formula.

Steps 1–5 identify all analytic inputs needed for (EF). In particular,
the logarithmic-derivative partial fractions, local zero count, gamma
bounds, and contour tail convergence are still mathematical work, not
formal consequences of `riemannZetaZeros` being discrete.

## 9. Bounding the finite zero sum

Assume (D_A), (ZF), and (EF). For `x` large enough, `h≤x/2`. The
fundamental theorem of calculus on the positive real axis gives

\[
 {x^\rho-(x-h)^\rho\over\rho}
   =\int_{x-h}^x u^{\rho-1}du.
\]

Every nontrivial zero has `0<beta<1` and `rho≠0`, so

\[
 \left|{x^\rho-(x-h)^\rho\over\rho}\right|
 \le h(x-h)^{\beta-1}\le2h x^{\beta-1}.
\tag{22}
\]

Put `L=log x`, `b=A*tau=391/400`. Replacing the actual cutoff `U` by
`2*x^tau` in the density estimate introduces the constant `2^A` and
`log(2*x^tau)^5≤C L^5`. For each zero occurrence define

\[
 j=\lfloor L(1-\beta)\rfloor.
\]

The corresponding weight is at most `exp(-j)`. Membership in layer
`j` implies `beta>1-(j+1)/L`; hence (D_A) bounds the number in that
layer by `K' L^5 exp(b*(j+1))`. If this real-part threshold is negative,
use the count at zero instead: `j+1≥L`, so the same exponential bound
still holds. Thus the estimate is uniform over all layers, including
those near `beta=0`.

Set `r=floor(L*eta(2*x^tau))`. The zero-free region says that no layer
with `j<r` occurs. Summing the geometric series,

\[
 \sum_{0<\gamma\le U}x^{\beta-1}
 \le {K'e^b L^5\exp(-(1-b)r)\over1-\exp(-(1-b))}.
\tag{23}
\]

This is exactly the pattern checked by
`Sidon.finite_zero_layer_bound`; the factor `exp b` and the floor
cannot be dropped. Since `r≥L*eta-1`, the floor costs at most the fixed
factor `exp(1-b)`. By (ZF), eventually
`(1-b)*L*eta(2*x^tau)≥7*log L`; therefore (23) is `O(L^-2)=o(1)`.
The negative-height zeros contribute the same bound by conjugation.
This argument handles the whole critical strip; splitting at
`beta=1/2` is unnecessary once (D_A) has been extended to `sigma=0`.

Consequently the zero term in (EF) is `o(h)`. Its remainder is also
`o(h)`:

\[
 {x\log^2x/U\over x^{2/3}}
 \le x^{-1/150}\log^2x\longrightarrow0,
 \qquad {\log x\over x^{2/3}}\longrightarrow0.
\]

The exponent is `1-tau-2/3=-1/150`. Thus

\[
 \psi(x)-\psi(x-h)=h(1+o(1)).
\tag{24}
\]

## 10. Removing prime powers and obtaining actual primes

The checked elementary finite proof in `PrimePowerError.lean` gives

\[
 0\le\psi(x)-\vartheta(x)\ll\sqrt x\log^2x=o(x^{2/3}).
\tag{25}
\]

Indeed every nonprime prime power `p^k≤x` has `k≥2`,
`p≤sqrt x`, and `k≤log_2 x`. The map `(p,k)↦p^k` covers these
integers, so there are at most `floor(sqrt x)*floor(log_2 x)` of them;
each has Mangoldt weight at most `log x`. Duplicates in this covering
only improve the bound. The exponent gap `2/3-1/2=1/6` absorbs two
logarithms. Latest mathlib additionally proves the stronger
`psi-theta=O(sqrt x)` in `NumberTheory/Chebyshev.lean`.

For large `x`, (24) gives a Mangoldt increment at least `h/2`, while
(25) is less than `h/4`. If there were no prime in `(x-h,x]`, theta
would be constant there. Since `psi-theta` is nonnegative at `x-h`,
that would imply `psi(x)-psi(x-h)≤psi(x)-theta(x)<h/4`, a contradiction.
Thus there is a prime in `(x-x^(2/3),x]`, proving (P) with a harmless
fixed enlargement of `C` when transferring between natural and real
endpoints.

## 11. Formal modules and exact remaining frontier

| Module | Contents | Status |
|---|---|---|
| `NumberTheory/PrimeIntervals` | All-real interval predicate, exponent weakening | Checked |
| `NumberTheory/PrimePowerError` | Finite prime-power counting, little-o bound, prime extraction | Checked |
| `NumberTheory/ZeroLayers` | Arbitrary finite-layer geometric bound including floors | Checked |
| `NumberTheory/ZetaZeroCount` | Actual bounded zeta-zero occurrences with analytic multiplicity; uniform input predicates | Checked |
| `Constructions/Extremal` | Maximal cardinality, Bose–Chowla lower bound, exact Cor. 1.4 reduction | Checked conditional on (P) |
| `NumberTheory/DivisorMeanSquare` | Equations (2)–(6) | Natural proof above; Lean pending |
| `NumberTheory/DirichletMeanSquare`, `LogarithmicMeanSquare`, `HarmonicGaps`, `MollifierEndpoint` | Uniform oscillatory kernel, finite L2, logarithmic gap bound, exact critical-line mollifier endpoint | Checked, constant 12 |
| `NumberTheory/DirichletMollifier` | Entire complex mollifier, exact critical-line bridge, divisor coefficients and cancellation | Checked; right-of-one infinite series endpoint pending |
| `NumberTheory/VerticalMeanSquare` | Interpolation, pole removal, equation (15) | Natural proof above; Lean pending |
| `NumberTheory/ZetaDensity` | Littlewood/Jensen count, equation (D_A) | Natural proof above; analytic counting infrastructure pending |
| `NumberTheory/WeylZeta` | Derivative tests, Euler continuation, equation (G_c) | Weak and strong derivative optimizations expanded; Euler continuation and tests pending |
| `NumberTheory/ZetaZeroFree` | A genuine region satisfying (ZF) | Primary Lean source candidate under audit; not yet imported |
| `NumberTheory/TruncatedExplicitFormula` | Formula (EF), local zero count, contour errors | Precise obligations above; Lean pending |
| `NumberTheory/InghamPrimeIntervals` | Assemble (D_A), (ZF), (EF), prime-power removal | Algebraic/asymptotic reduction above; Lean assembly pending |

The remaining frontier is substantial analytic number theory. None of
its missing prerequisites is recorded as an axiom or `theorem_wanted`,
and an unconditional all-length power-saving prime-gap theorem has not
yet been claimed in the checked root graph.
