/- Copyright 2025 Cryspen
Licensed under the Apache License, Version 2.0.
See Hax/LICENSE for the full license text.

Adapted for libcrux-lean-specs by Bas Spitters. -/

-- This module serves as the root of the `Hax` library.
-- Import modules here that should be built as part of the library.

/- Additions to the Lean library -/
import Hax.MissingLean

/- Implementation of Rust primitives in Lean -/
import Hax.Rust_primitives

/- Core Models, extracted from our model written in Rust -/
import Hax.Core_models

/- Tactics -/
import Hax.Tactic
