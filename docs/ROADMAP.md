# General causal-set research roadmap

This repository contains a reusable Lean formalization of elementary causal-set order theory. Research directions below are proposals, not established conclusions.

## A1: foundational public library
- Maintain a stable order/link API and explicit assumptions.
- Keep reproducible kernel and axiom verification.
- Add small, reviewed examples and documentation.

## Finite causal sets and invariants
- Prove transport of intervals and links under order isomorphisms.
- Investigate invariance under order duality.
- Prefer existing mathlib structures and small, independently useful theorems.

## Limits of reconstruction
- Investigate explicit finite posets with identical summary statistics but distinct isomorphism types.
- State precisely which invariants fail to identify a finite order.
- Verify literature and minimality claims before asserting novelty.

## Statistical reconstruction
- Study fixed-size random two-dimensional orders as a tractable first model.
- Separate deterministic combinatorial statements from probability assumptions.
- Investigate exact finite-sample expectations and error bounds, with literature checks.

No continuum, metric, or physical-field interpretation is implied by these milestones.
