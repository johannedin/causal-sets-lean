/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

import CausalSet

/-!
# Axiom audit

These guarded commands make the trusted dependencies of foundational results visible and cause
their dedicated CI step to fail if they drift.
-/

/-- info: 'CausalSet.mem_alexandrovInterval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.mem_alexandrovInterval

/-- info: 'CausalSet.intervalCard_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.intervalCard_eq_zero

/-- info: 'CausalSet.isLink_iff_covBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.isLink_iff_covBy

/-- info: 'CausalSet.isLink_iff_lt_and_intervalCard_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.isLink_iff_lt_and_intervalCard_eq_zero

/-- info: 'CausalSet.lt_iff_transGen_isLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.lt_iff_transGen_isLink

/-- info: 'CausalSet.reflTransGen_isLink_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.reflTransGen_isLink_iff

/-- info: 'CausalSet.le_iff_eq_or_transGen_isLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.le_iff_eq_or_transGen_isLink

/-- info: 'CausalSet.le_iff_reflTransGen_isLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.le_iff_reflTransGen_isLink
