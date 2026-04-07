import Lake
open Lake DSL

package «libcrux-lean-specs» where
  version := v!"0.0.1-alpha.1"
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Hax prelude library (Rust primitives, core models, tactics)
@[default_target]
lean_lib «HaxPrelude» where
  srcDir := "."

-- libcrux-specs: pure crypto function signatures
@[default_target]
lean_lib «LibcruxSpecs» where
  srcDir := "."

require Qq from git
  "https://github.com/leanprover-community/quote4" @ "b8f98e9087e02c8553945a2c5abf07cec8e798c3"
