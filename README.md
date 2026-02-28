# libcrux-lean-specs

Pure Lean 4 specifications for [libcrux](https://github.com/cryspen/libcrux) cryptographic primitives, along with the [hax](https://github.com/hacspec/hax) prelude library for Rust-to-Lean extraction.

## Contents

### Hax Prelude (`Hax/`)

The Lean prelude for hax extraction, providing:

- **Rust primitives** (`Rust_primitives/`): Array, Vec, numeric types, casting, indexing, loops
- **Core models** (`Core_models/`): Lean models of Rust core types (iterators, slices, comparison, etc.)
- **MissingLean** (`MissingLean/`): Extensions to Lean's standard library (BitVec, UInt, SInt, Vector)
- **MissingCore** (`MissingCore/`): Clone, Marker traits
- **Tactics** (`Tactic/`): `hax_bv_decide`, `hax_construct_pure`, `hax_zify`, `native_panic_freedom`

### Libcrux Specs (`LibcruxSpecs/`)

Pure opaque declarations for libcrux cryptographic functions:

| Module | Functions |
|--------|-----------|
| SHA-256 | `sha256_32` |
| HMAC-SHA256 | `hmac_sha256_32` |
| HKDF-SHA256 | `hkdf_extract_32`, `hkdf_expand_32` |
| AES-128 | `aes128_encrypt` |
| AES-128-GCM | `aes128_gcm_seal_32`, `aes128_gcm_open_32` |
| X25519 | `x25519_scalarmult`, `x25519_base` |
| P-256 | `p256_scalar_mult_32`, `p256_base_mult_32` |

These are modeled as `opaque` constants (no axioms in `#print axioms`).

## Building

```
lake build
```

Requires Lean 4.28.0 (no other dependencies except Qq).

## Origin

These files originate from the [SSProve-lean](https://github.com/spitters/SSProve-lean) project.
The hax prelude is adapted from [Cryspen's hax](https://github.com/hacspec/hax) Lean backend.
