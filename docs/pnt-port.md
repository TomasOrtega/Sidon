# Prime number theorem: proof-only dependency port

The latest stable releases checked on 22 October 2026 are
[Lean 4.35.0](https://github.com/leanprover/lean4/releases/tag/v4.35.0) and
[mathlib 4.35.0](https://github.com/leanprover-community/mathlib4/releases/tag/v4.35.0),
the latter at 56a005855ea17e0b0958f73ec801ae140b0a1679.
They match the toolchain and mathlib requirement of
[PrimeNumberTheoremAnd at 127b50e33f6033e2147921167a117af96d9ba4ea](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/127b50e33f6033e2147921167a117af96d9ba4ea).

## Exact source boundary and verification

The local files under Sidon/NumberTheory/Tauberian/ adapt the Apache-2.0
PNT+ development. Attribution is retained in every adapted file.
The extracted files are:

- Sobolev.lean: compactly supported smooth functions, an integrable
  two-derivative Sobolev class, and truncation approximation.
- Fourier.lean: the two integrations by parts that control Fourier decay.
- SmoothCutoff.lean: the first smooth-cutoff theorem of upstream
  SmoothExistence.lean.
- Asymptotics.lean: the small asymptotic and natural-cast helper interface,
  from upstream Mathlib/Analysis/Asymptotics/Asymptotics.lean.
- Wiener.lean: the argument through WeakPNT.

The extraction ends immediately after WeakPNT. It excludes the optional
later arithmetic-progression and automatic-Chebyshev arguments. It also
excludes prelim_decay_2, prelim_decay_3, AbsolutelyContinuous, and
decay_alt: the first two have placeholder proofs upstream, and dependency
inspection shows that this entire bounded-variation alternative is unused
by the selected Wiener–Ikehara proof. The proof instead uses the proved
two-derivative Sobolev decay identity.

Architect metadata, blueprint attributes, and all source option commands
are removed. No dependency on LeanArchitect, leancert, or PrimeCert is
needed. Definitional-equality issues exposed by removing source
transparency settings are repaired by explicit Fourier-integrand
identities. All five extracted modules and the local
PrimeNumberTheorem.lean and RelativePrimeIntervals.lean compile on 4.35.0.
The kernel dependency audit for WeakPNT reports exactly
propext, Classical.choice, and Quot.sound. No additional logical premise
is used to obtain the prime number theorem or relative prime intervals.

The older PNT+ [4.14 port](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/pull/214)
was audited before the user requested the latest toolchain. That older
port is not used in the latest development.

## Detailed proof of the selected Tauberian theorem

Let \(f:\mathbb N\to\mathbb R_{\geq0}\). Assume absolute convergence of
\(F(s)=\sum_{n\geq1}f(n)n^{-s}\) for \(\Re s>1\), a Chebyshev bound
\(\sum_{n<N}f(n)\leq CN\), and a continuous extension of
\(G(s)=F(s)-A/(s-1)\) to the closed half-plane \(\Re s\geq1\).
We prove \(\sum_{n<N}f(n)/N\to A\).

1. For an integrable twice differentiable test function \(\psi\) with
   integrable first and second derivatives, Fourier differentiation gives
   \[
     (1+u^2)\widehat\psi(u)
       =\widehat{\psi-\psi''/(4\pi^2)}(u).
   \]
   The integral triangle inequality bounds the right side by
   \(\|\psi\|_1+(4\pi^2)^{-1}\|\psi''\|_1\). Thus
   \(|\widehat\psi(u)|\leq C_\psi/(1+u^2)\).
   Compactly supported \(C^2\) functions belong to this class. Multiplying
   a Sobolev function by a smooth cutoff at scale \(R\), differentiating
   the product twice, and applying dominated convergence proves
   convergence in this two-derivative norm.

2. For \(\sigma>1\), expand \(F(\sigma+it)\) in the integral and use absolute
   convergence to interchange sum and integral. The elementary identity
   \(n^{-(\sigma+it)}x^{it}=n^{-\sigma}
   \exp(-it\log(n/x))\) gives
   \[
      \sum_{n\geq1} f(n)n^{-\sigma}
        \widehat\psi\!\left(\frac{\log(n/x)}{2\pi}\right)
      =\int_{\mathbb R}F(\sigma+it)\psi(t)x^{it}\,dt.
   \]
   Each interchange has an explicit integrable dominating function
   \(\sum f(n)n^{-\sigma}|\psi(t)|\).

3. Compute the pole contribution using
   \[
      (\sigma+it-1)^{-1}
       =\int_0^\infty \exp(-u(\sigma-1+it))\,du.
   \]
   Fubini and the substitution at \(-\log x\) express it as a Fourier
   integral on \([-\log x,\infty)\). Subtracting this identity from the
   previous identity isolates \(G\).

4. Let \(\sigma\downarrow1\). For the series side, summation by parts
   combines \(\sum_{n<N}f(n)\leq CN\) with the
   \(1/(1+\log^2(n/x))\) Fourier majorant. This proves summability and a
   bound uniform for \(\sigma\) near one. Dominated convergence applies.
   On the integral side, \(\psi\) has compact support and \(G\) is
   continuous on the closed half-plane, so a compact rectangle supplies
   a uniform integrable bound. The limiting identity is
   \[
      \sum_{n\geq1}\frac{f(n)}n
        \widehat\psi\!\left(\frac{\log(n/x)}{2\pi}\right)
      -A\int_{-\log x}^{\infty}\widehat\psi(u/(2\pi))\,du
      =\int_{\mathbb R}G(1+it)\psi(t)x^{it}\,dt.
   \]

5. The last integral tends to zero as \(x\to\infty\) by the
   Riemann–Lebesgue lemma: its frequency is
   \(-\log x/(2\pi)\), which tends to \(-\infty\).
   Fourier inversion and the logarithmic change of variables convert
   this identity into
   \[
      \frac1x\sum_n f(n)\Psi(n/x)\longrightarrow
      A\int_0^\infty\Psi(u)\,du
   \]
   for a smooth test function \(\Psi\) compactly supported inside
   \((0,\infty)\). The Sobolev cutoff approximation justifies passage
   from compact Fourier tests to these tests.

6. For \(0<a<b\), choose smooth functions
   \(0\leq\Psi_-\leq1_{[a,b]}\leq\Psi_+\) supported away from zero
   whose integrals differ from \(b-a\) by at most an arbitrary
   \(\delta>0\). Nonnegativity of \(f\) sandwiches the interval sum.
   Send \(x\to\infty\), then \(\delta\downarrow0\), obtaining normalized
   interval mass \(A(b-a)\). Rounding endpoints to natural ceilings
   gives the corresponding discrete interval statement.

7. Apply this with \([a,b]=[\varepsilon,1]\).
   The omitted initial mass is bounded by
   \(C\lceil\varepsilon N\rceil/N\), which tends to \(C\varepsilon\).
   The interval limit is \(A(1-\varepsilon)\).
   Sending \(\varepsilon\downarrow0\) proves the full Tauberian
   conclusion.

## From Wiener–Ikehara to relative prime intervals

For the von Mangoldt function \(\Lambda\), mathlib proves:

- nonnegativity and absolute convergence of its L-series on \(\Re s>1\);
- \(F(s)=-\zeta'(s)/\zeta(s)\) there;
- nonvanishing of \(\zeta\) on \(\Re s\geq1\), apart from its pole;
- continuity of \(F(s)-1/(s-1)\) on the closed half-plane;
- the needed Chebyshev linear upper bound.

These instantiate the previous theorem with \(A=1\).
The local PrimeNumberTheorem.lean then changes strict natural sums to
inclusive sums: the extra term is at most \(\log N/N\), which tends to zero.
Composing with the natural floor and using
\(0\leq x-\lfloor x\rfloor<1\) gives \(\psi(x)\sim x\).
Mathlib's bound
\[
  0\leq\psi(x)-\theta(x)\leq2\sqrt{x}\log x
\]
and \(\sqrt{x}\log x=o(x)\) imply \(\theta(x)\sim x\).

For \(0<\varepsilon<1\), set \(a=(1-\varepsilon)x\).
For large \(x\), both errors in \(\theta(x)\) and \(\theta(a)\) are at most
\((\varepsilon/4)\) times their arguments. Consequently
\[
 \theta(x)-\theta(a)\geq
  \left(\varepsilon-\frac{\varepsilon}{4}(2-\varepsilon)\right)x>0.
\]
If there were no prime in \((a,x]\), the two finite sets of primes in
the defining sums for \(\theta(a)\) and \(\theta(x)\) would be equal,
contradicting this strict inequality. For arbitrary positive
\(\varepsilon\), apply the result to
\(\min(\varepsilon,1/2)\). This proves the relative interval theorem
needed for the sharp all-length obstruction construction.

This theorem gives a relative error tending to zero. It does not provide
the power-saving interval input needed for Corollary 1.4; that separate
dependency is tracked in [prime-gap-research.md](prime-gap-research.md).
