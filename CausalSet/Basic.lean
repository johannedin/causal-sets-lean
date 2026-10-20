/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Cover

/-!
# Causal-set foundations

Mathematically, a causal set is a locally finite partial order. This project proves its elementary
interval and link lemmas at the weaker, reusable level of existing mathlib structure:

* `Preorder α` supplies reflexive causal precedence `≤` and its strict part `<`;
* `LocallyFiniteOrder α` says every closed order interval is finite.

This module deliberately introduces no competing order typeclass.  The convention makes the
formalization directly interoperable with mathlib's interval and cover-relation theorems. Results
that require a causal set rather than merely its generic order-theoretic fragment explicitly assume
`PartialOrder α`.

## Scope

This is the order-theoretic core only.  It does not assert that an arbitrary locally finite
preorder faithfully embeds into a Lorentzian spacetime, nor does it include a probability
law, number density, dimension, differentiable structure, or metric reconstruction.
-/
