# ParisiFormula

A Lean 4 formalisation project for the **Parisi formula** for the Sherrington–Kirkpatrick
spin glass, following Guerra's interpolation bounds and Talagrand's proof
(*Ann. of Math.* 163, 2006).

**Status (September 4, 2026):** the SK-model version of Talagrand's **Theorem 2.1**
(`guerra_identity`) is proved, including endpoint continuity and an explicit nonnegative,
bounded squared-overlap remainder. The Guerra RSB upper bound and its thermodynamic
upper-bound consequence are also proved without `sorry` dependencies. Build-time axiom
checks live in [`Targets/GuerraAudit.lean`](Targets/GuerraAudit.lean).

**The full Parisi formula is not yet complete:** Theorem 2.2 remains the one open theorem
on the current critical path. Three older, off-path placeholders remain in
`Targets/Milestones.lean`. See [`docs/ROADMAP.md`](docs/ROADMAP.md) for the current status;
the older [`blueprint/blueprint.tex`](blueprint/blueprint.tex) records the broader milestones.

## Project milestones

1. **Existence of the thermodynamic limit** (Guerra–Toninelli superadditivity + Fekete).
2. **The finite-step Parisi functional** (Talagrand's recursion; no PDE) and its continuity.
3. **Guerra's replica-symmetry-breaking upper bound** `F_N ≤ 𝒫_k(m,q)`.
4. **Talagrand's lower bound**, hence the Parisi formula. (Long-term.)

The active proof route is Talagrand (2006); the next critical step is Theorem 2.2, not
the separate Guerra–Toninelli development in milestone 1.

---

## Setting up (no prior Lean experience assumed)

You need about 30 minutes and ~10 GB of disk. Steps are for macOS/Linux; on Windows use
WSL or follow the equivalent installer links.

### 1. Install `elan` (the Lean version manager)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Restart your terminal afterwards. `elan` reads the file `lean-toolchain` in this
repository and automatically installs the exact Lean version we use (`v4.32.1`).

### 2. Install VS Code and the Lean 4 extension

Download [VS Code](https://code.visualstudio.com/), open it, go to Extensions
(`Ctrl/Cmd+Shift+X`), search **"lean4"** and install the extension by *leanprover*.

### 3. Get this repository and the prebuilt Mathlib

```bash
git clone <your-repo-url> ParisiFormula
cd ParisiFormula
lake exe cache get      # downloads compiled Mathlib (~5–10 min). Do NOT skip this:
                        # compiling Mathlib from source takes hours.
```

### 4. Build

```bash
lake build              # Tier 1: the vendored, verified core. First run: ~5–15 min.
```

If this succeeds, your setup works. Then:

```bash
lake build ParisiFormula   # Tier 2: our own work
lake build Targets         # Tier 3: target statements (warnings about `sorry` are expected)
```

Open the folder in VS Code and click into any `.lean` file: the Lean extension shows the
proof state live in the side panel ("Lean Infoview").

### If something fails

Copy the **entire** error message (the terminal output, or the red squiggle text in
VS Code) and paste it to your collaborator/assistant. Most first-run errors are one of:

- forgot `lake exe cache get` (symptom: build runs for hours, or "missing .olean" errors);
- network hiccup during cache download (just rerun `lake exe cache get`);
- Tier 3 elaboration errors (expected; these files were drafted without a Lean environment).

---

## Project layout and the three build tiers

```
ParisiFormula/
├── lakefile.lean            build configuration (three targets, see below)
├── lean-toolchain           pins Lean v4.32.1
├── lake-manifest.json       pins Mathlib v4.32.1 and transitive deps (identical to RSAT)
│
├── Lemmas/SpinGlass/        TIER 1  vendored core, verbatim from RSAT (verified, no sorry)
│   ├── Defs.lean                configurations, overlap, Gibbs weights, free energy, Hessian
│   ├── Calculus.lean            smoothness/Lipschitz bounds for the free energy
│   ├── GaussianIntegrationByParts.lean   1-D Gaussian IBP (Stein's lemma)
│   ├── Gaussian_IBP_Hilbert.lean         Hilbert-space Gaussian IBP with covariance operator
│   ├── gaussian_concentration.lean       Gaussian concentration of measure
│   ├── SKModel.lean             SK disorder as a Gaussian vector with prescribed covariance
│   ├── Replicas.lean            replica calculus, derivative of the smart path
│   └── GuerraBound.lean         algebraic core of Guerra's RS bound (Talagrand (1.65))
│
├── ParisiFormula/           TIER 2  our work
│   └── GuerraToninelli.lean     ported from RSAT; superadditivity conditional on 2 hypotheses
│
├── Targets/                 TIER 3  precise statements of every milestone, with `sorry`
│   └── Milestones.lean
│
├── port/                    upstream files on an OLDER Lean (4.28); not built; to be ported
│   ├── GuerraInterpolation.lean, GuerraIBP.lean, GuerraTrace.lean, GuerraPipeline.lean
│   │                            the three-step derivative pipeline for Guerra's RS smart path
│   └── ParisiOperator.lean      the operator T_{m,v} and its semigroup law
│
├── blueprint/blueprint.tex  the mathematical plan, lemma by lemma, with Lean names
├── docs/ROADMAP.md          what to do next, concretely
├── docs/PROVENANCE.md       exact origin (repo, path, commit) of every vendored file
└── scripts/check.sh         builds all tiers and scans Tier 1–2 for `sorry`
```

**Why three tiers?** So that a mistake in new, unverified code can never block you from
building the verified base. `lake build` alone only touches Tier 1.

---

## Credits and licence

This project would not exist without two open-source Lean libraries, both Apache-2.0:

- **[or4nge19/SpinGlass](https://github.com/or4nge19/SpinGlass)** by Matteo Cipollina —
  the finite-volume spin-glass calculus and the Gaussian IBP machinery.
- **[njimaMath/research_public](https://github.com/njimaMath/research_public)** —
  the RSAT and perceptronFixed artifacts (arXiv:2608.23413), which extend the above and
  contain the Guerra–Toninelli blueprint we build on.

All vendored files keep their original copyright headers. See `NOTICE` and
`docs/PROVENANCE.md`. This project is released under the Apache License 2.0 (`LICENSE`).

## Contributing

Not yet open for external contributions; the plan is to announce on the
[Lean Zulip](https://leanprover.zulipchat.com) once Milestone 1 is complete and the
blueprint website is up. Until then, issues and questions are welcome.
