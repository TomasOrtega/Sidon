# Blueprint tooling for Lean 4.35.0

Verified against primary sources on 22 October 2026. This records compatibility targets; a successful project and documentation build remains the validation.

- **Lean/mathlib:** mathlib's latest stable release is [v4.35.0](https://github.com/leanprover-community/mathlib4/releases/tag/v4.35.0), whose release commit bumps the Lean toolchain to that version.
- **doc-gen4:** pin `rev = "v4.35.0"`, locally resolved to commit `0e1ffe2e4ba5ecfdfaf15c65b8d3805dbb7134ae`. Its [toolchain file](https://github.com/leanprover/doc-gen4/blob/v4.35.0/lean-toolchain) specifies `leanprover/lean4:v4.35.0`. The [official README](https://github.com/leanprover/doc-gen4#usage) instructs projects on stable Lean releases to use the matching version branch rather than `main`.
- **leanblueprint:** [PyPI's latest release](https://pypi.org/project/leanblueprint/) is **0.0.20**, released 23 December 2025. Its [package metadata](https://github.com/PatrickMassot/leanblueprint/blob/master/setup.cfg) requires Python >=3.7, plasTeX >=3.1, plastexdepgraph >=0.0.4, and Jinja2 >=3.1.0. It does not pin Lean. Pinning `leanblueprint==0.0.20` makes the currently latest release explicit and reproducible.
- **Graphviz:** leanblueprint's [installation instructions](https://github.com/PatrickMassot/leanblueprint#installation) still require Graphviz and its development libraries through plastexdepgraph. Retain the verified Alpine library-search and runtime-search flags in the publishing workflow; upgrading Lean does not resolve that separate linker-path issue.
- **checkdecls:** the upstream [toolchain file](https://github.com/PatrickMassot/checkdecls/blob/master/lean-toolchain) remains at Lean 4.18.0. Its [25-line executable](https://github.com/PatrickMassot/checkdecls/blob/master/Main.lean) uses Lake workspace-loading APIs. Direct compilation of the downloaded latest source at commit `3d42585` under Lean 4.35.0 passed; the complete executable audit still requires the project build. leanblueprint's [current client](https://github.com/PatrickMassot/leanblueprint/blob/master/leanblueprint/client.py) still invokes `lake exe checkdecls blueprint/lean_decls`.

The doc-gen4 README now recommends a separate `docbuild` project with `packagesDir = "../.lake/packages"`, a path dependency on the parent project, and matching-version doc-gen4. Its update command for a mathlib project is `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4`; generation is `lake build Sidon:docs` inside `docbuild`, with output at `docbuild/.lake/build/doc`. Adopting that layout also requires changing API-doc cache and copy paths. Keeping the existing root-level dependency while pinning its matching stable version is the smaller migration; test it first before changing the layout.

Validation should include the complete Lean build, the complete API-doc facet, `leanblueprint pdf`, `leanblueprint web`, and the declaration audit. The blueprint client still builds PDF before web so that bibliography output can be copied for plasTeX.

The latest doc-gen4 writes incremental extraction data to
`.lake/build/api-docs.db` and `.lake/build/doc-data`, then generates HTML from
that database. The publishing cache now includes both locations and isolates
keys by Lean toolchain. Project `Sidon*` markers are excluded so project API
data is regenerated. A regression check first failed on the omitted database
and marker directory, then passed after both restore/save path lists were fixed.
