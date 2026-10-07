/-
Root module for the Six Birds cosmology Lean receipts.

This mathlib-free root imports the fast structural receipts. It deliberately does not import the
mathlib-backed T3 module `SbtCosmo.Adequacy.Reconciliation`; that module lives
in the separate `SbtCosmoAdequacy` target declared in `lakefile.lean`.
-/

import SbtCosmo.Idempotence
import SbtCosmo.RouteMismatch
import SbtCosmo.LocalGlobal
import SbtCosmo.Holonomy
import SbtCosmo.PhantomStableReadout
import SbtCosmo.AORStatus
