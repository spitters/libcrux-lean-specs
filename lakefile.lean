import Lake
open Lake DSL

package «libcrux-lean-specs» where
  version := v!"0.0.1-alpha.1"
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]
  -- `-E <kind>` reports Lean messages of that kind as errors. `hasSorry` is the
  -- kind Lean attaches to a declaration whose proof term reaches `sorryAx`, so
  -- building this package refuses such a declaration and no separate step has to
  -- read the build's output. The word in a comment, a docstring or a string
  -- literal carries no such message; a declaration reaching `sorryAx` through a
  -- tactic carries one even though the word appears nowhere in its source.
  moreLeanArgs := #["-E", "hasSorry"]

-- Hax prelude library (Rust primitives, core models, tactics)
@[default_target]
lean_lib «HaxPrelude» where
  srcDir := "."

-- libcrux-specs: pure crypto function signatures
@[default_target]
lean_lib «LibcruxSpecs» where
  srcDir := "."

require Qq from git
  "https://github.com/leanprover-community/quote4" @ "707efb56d0696634e9e965523a1bbe9ac6ce141d"
