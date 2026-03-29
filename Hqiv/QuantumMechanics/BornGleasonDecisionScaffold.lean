import Hqiv.QuantumMechanics.BornRuleFirstPrinciples

/-!
# Gleason-type and decision-theoretic Born programs vs.\ the HQIV finite layer

This module does **not** prove Gleason’s theorem or a Deutsch–Wallace-style decision-theoretic
derivation. It **pins down exactly** what those programs require, and points to what is already
proved in-repo (`BornRuleFirstPrinciples`).

## Gleason (measure on projections)

**Classical statement (sketch).** On a separable Hilbert space `H` with `dim H ≥ 3`, every
σ-additive probability measure `μ` on the lattice of orthogonal projections, with `μ(𝟙) = 1`,
is induced by a density operator `ρ`:
`∀` (orthogonal projections `P`), `μ P = \mathrm{tr}(ρ P)`.

**Ingredients not in the three HQIV axioms:** a fixed infinite-dimensional (or at least
`dim ≥ 3`) Hilbert space, the full projection lattice, countable additivity on orthogonal
families, and analytic closure (typically `Analysis` / operator algebras in Mathlib).

**What HQIV already formalizes instead:** on a **finite** outcome space `Fin n`, if probabilities
are nonnegative, sum to `1`, and satisfy squared-amplitude coherence (`BornCoherent`), then they
are **uniquely** the Born weights (`bornProbN_unique_of_coherence`). That is the standard
finite-dimensional **ratio uniqueness** argument, not Gleason’s measure-theoretic theorem.

## Decision-theoretic (e.g.\ Deutsch–Wallace style)

Typical assumptions include: rational preferences over **quantum games** (acts whose outcomes are
quantum branches), constraints tying preferences to unitary equivalence of states, and
branch-counting or measure arguments in a many-worlds reading.

**Ingredients not in the three HQIV axioms:** a theory of preferences, decision acts, and usually
an Everett-style branching semantics. None of these are encoded in `OctonionicLightCone`,
`MonogamyTangles`, or `DiscreteQuantumState` as stated in this repository.

## Navigation

Use `bornProbN_unique_of_coherence` for the proved finite uniqueness statement. The definitions
below are **documentation anchors** so the roadmap “Gleason / decision-theoretic from axioms” can
cite a single Lean module.
-/

namespace Hqiv.QM

/-- **Roadmap marker:** a full analytic Gleason-style statement packaged in Mathlib (dimension ≥ 3,
σ-additivity on projections, conclusion `∃ ρ, ∀ P, μ P = tr(ρ P)`). Not formalized here.

The proposition is intentionally left abstract: instantiating it is future work once the analytic
stack is in scope. -/
structure GleasonAnalyticTarget : Prop where
  /-- Placeholder: the real content would be a `Prop` quantifying over Hilbert spaces and measures. -/
  roadmap : True

/-- Trivial witness: the scaffold type is inhabited so downstream files can `import` without
`open Classical`. -/
theorem gleason_analytic_target_inhabited : GleasonAnalyticTarget :=
  ⟨trivial⟩

/-- **Roadmap marker:** preferences over quantum acts + rationality constraints strong enough to
force Born weights (decision-theoretic program). Not formalized here. -/
structure DecisionTheoreticBornTarget : Prop where
  roadmap : True

theorem decision_theoretic_born_target_inhabited : DecisionTheoreticBornTarget :=
  ⟨trivial⟩

/-- The finite substitute already proved: coherence + normalization ⇒ Born weights
(`BornRuleFirstPrinciples`). -/
abbrev born_from_coherence_unique :=
  @bornProbN_unique_of_coherence

end Hqiv.QM
