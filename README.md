# The Unique Minimizer of Ridge Regression in Lean 4

**Authors:** Chelsea Zhang, Sherry Meng, Xiaodi Yuan, and Xiaoyi Chang · **Course:** STAT 4052, Fall 2026

## Theorem

For any real design matrix $X$ with $n$ rows and $p$ columns, any response vector $y$ of length $n$, and any $\lambda>0$, exactly one coefficient vector minimizes the ridge loss

$$
L(\beta)=\lVert y-X\beta\rVert_2^2+\lambda\lVert\beta\rVert_2^2.
$$

The penalty applies to all $p$ coefficients. The dimensions are arbitrary nonnegative integers, and the design may be rank-deficient.

The exact statement of [`ridge_unique_minimizer`](RidgeUniqueMinimizer.lean#L141-L156) is

```lean
theorem ridge_unique_minimizer {n p : ℕ} (X : Fin n → Fin p → ℝ)
    (y : Fin n → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    ∃! beta_hat : Fin p → ℝ,
      ∀ beta : Fin p → ℝ,
        ridgeLoss X y lam beta_hat ≤ ridgeLoss X y lam beta
```

| Step in the report | Where it is proved |
|---|---|
| 1. Positive definiteness | [Positive definiteness](RidgeUniqueMinimizer.lean#L42-L51) and the [quadratic form](RidgeUniqueMinimizer.lean#L68-L86) show that $A=X^{\mathsf T}X+\lambda I$ is positive definite. |
| 2. Invertibility | [The inverse identity](RidgeUniqueMinimizer.lean#L53-L59) gives $AA^{-1}=I$. |
| 3. Existence | [The normal-equation solution](RidgeUniqueMinimizer.lean#L88-L93) constructs $b=A^{-1}X^{\mathsf T}y$. The [loss difference](RidgeUniqueMinimizer.lean#L95-L126) is a sum of two nonnegative terms, so $b$ attains the minimum. |
| 4. Uniqueness | [Strict minimality](RidgeUniqueMinimizer.lean#L128-L137) gives $L(b)<L(\beta)$ for every $\beta\ne b$. The final theorem rules out a second minimizer. |

## External axioms used

No additional external axioms are used beyond the stated theorem hypotheses and the standard Lean/mathlib foundations.

The positive penalty is an explicit theorem hypothesis. The proof uses mathlib's verified results on Gram matrices, positive diagonal matrices, and invertibility. The [axiom audit](RidgeUniqueMinimizer.lean#L158) reports only `propext` (propositional extensionality), `Classical.choice` (classical choice), and `Quot.sound` (quotient soundness).

## Build and check

Install Git and [Lean with elan](https://github.com/leanprover/elan). From the repository root, run:

```sh
lake exe cache get
lake build
lake env lean RidgeUniqueMinimizer.lean
```

The first command downloads compiled dependencies. The second builds the project. The third checks the proof file and prints the final theorem's axiom dependencies:

```text
'ridge_unique_minimizer' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Files

- [RidgeUniqueMinimizer.lean](RidgeUniqueMinimizer.lean) contains the loss definition, eleven supporting lemmas, the main theorem, and the axiom audit.
- [lean-toolchain](lean-toolchain) pins Lean 4.36.0.
- [lakefile.toml](lakefile.toml) specifies the build target and pins mathlib v4.36.0 at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
- [lake-manifest.json](lake-manifest.json) records the dependency revisions used for the build.

The theorem establishes uniqueness for a fixed positive penalty. Choosing the penalty for prediction or fitting an unpenalized intercept requires a separate analysis.

OpenAI Codex assisted with mathematical exposition, Lean development and verification, documentation, and LaTeX preparation.
