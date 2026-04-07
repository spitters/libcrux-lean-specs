/-
# Fuel-bounded loop combinators for hax extraction

The hax `while_loop` requires proof parameters (`pureInv`, `pureCond`,
`pureTermination`) that `mvcgen` can't synthesize for complex extracted loops.
These fuel-bounded wrappers avoid the proof obligations entirely.

### Soundness caveat

The fuel bounds (10 000 / 100 000) are **not** verified to be sufficient for
all inputs. If a loop exceeds the fuel budget, the wrapper silently returns the
current intermediate state rather than signalling an error. For crypto spec loops
on fixed-length inputs the actual iteration counts are small (SHA-256: 64,
AES: 10), so the bounds are conservative by orders of magnitude. A proper fix
would replace fuel with a termination proof or return `Option β` on exhaustion.
-/

import HaxPrelude

set_option autoImplicit false

/-- while_loop_return: like while_loop but the body returns ControlFlow.
    Break exits the loop early, Continue provides the next state.
    **Fuel-bounded** (10 000 iterations). -/
noncomputable def Rust_primitives.Hax.while_loop_return {β R : Type}
    (inv : β → RustM Prop)
    (cond : β → RustM Bool)
    (termination : β → RustM Hax_lib.Int.Int)
    (init : β)
    (body : β → RustM (Core_models.Ops.Control_flow.ControlFlow R β)) :
    RustM (Core_models.Ops.Control_flow.ControlFlow R β) := do
  let rec loop (fuel : Nat) (state : β) : RustM (Core_models.Ops.Control_flow.ControlFlow R β) :=
    match fuel with
    | 0 => pure (Core_models.Ops.Control_flow.ControlFlow.Continue state)
    | n + 1 => do
      let c ← cond state
      if c then
        match (← body state) with
        | Core_models.Ops.Control_flow.ControlFlow.Break r =>
          pure (Core_models.Ops.Control_flow.ControlFlow.Break r)
        | Core_models.Ops.Control_flow.ControlFlow.Continue next =>
          loop n next
      else
        pure (Core_models.Ops.Control_flow.ControlFlow.Continue state)
  loop 10000 init

/-- while_loop_cf: like while_loop but the body returns ControlFlow.
    On Break, extracts the continuation value. On Continue, provides next state.
    **Fuel-bounded** (10 000 iterations). -/
noncomputable def Rust_primitives.Hax.while_loop_cf {β : Type}
    (inv : β → RustM Prop)
    (cond : β → RustM Bool)
    (termination : β → RustM Hax_lib.Int.Int)
    (init : β)
    (body : β → RustM (Core_models.Ops.Control_flow.ControlFlow β β)) :
    RustM β := do
  let rec loop (fuel : Nat) (state : β) : RustM β :=
    match fuel with
    | 0 => pure state
    | n + 1 => do
      let c ← cond state
      if c then
        match (← body state) with
        | Core_models.Ops.Control_flow.ControlFlow.Break v => pure v
        | Core_models.Ops.Control_flow.ControlFlow.Continue next =>
          loop n next
      else
        pure state
  loop 10000 init

/-- Fuel-bounded while_loop. **Fuel = 100 000 iterations.** -/
private def while_loop_fuel {β : Type}
    (cond : β → RustM Bool) (body : β → RustM β) : Nat → β → RustM β
  | 0, state => pure state
  | n + 1, state => do
    if (← cond state) then while_loop_fuel cond body n (← body state)
    else pure state

def Rust_primitives.Hax.while_loop' {β : Type}
    (_inv : β → RustM Prop)
    (cond : β → RustM Bool)
    (_termination : β → RustM Hax_lib.Int.Int)
    (init : β)
    (body : β → RustM β) : RustM β :=
  while_loop_fuel cond body 100000 init
