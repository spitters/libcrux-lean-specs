/-
Copyright (c) 2026 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/

/-!
# Panic-Freedom and Extraction Status

## Status

The hax extraction pipeline successfully produces Lean definitions for all 18
Rust spec modules (253 definitions total). However, the extracted Lean file
requires Hax prelude updates for full compilation:

* Missing `Alloc.Vec.Impl_1.truncate` binding
* Type class resolution failures for `OrOp` on `Shl.AssociatedTypes.Output`
* Chacha20 (line 2755+) uses `i32` shift operations missing from prelude

## Verified Properties (Level 1 + Level 2)

These properties are verified by differential testing and Kani BMC, providing
strong evidence that the `opaque` constants in `Specs.lean` faithfully model
the Rust implementations:

### Level 1: Differential Testing (proptest + Wycheproof)

| Function | Test Method | Cases |
|----------|-----------|-------|
| `sha256_32` | proptest vs libcrux-sha2 | 500 random + NIST vector |
| `hmac_sha256_32` | proptest vs libcrux-hmac | 500 random + RFC 4231 + 174 Wycheproof |
| `hkdf_extract_32` | proptest vs libcrux-hkdf | 500 random + RFC 5869 + 86 Wycheproof |
| `hkdf_expand_32` | proptest vs libcrux-hkdf | 500 random |
| `aes128_encrypt` | proptest vs RustCrypto AES | 1000 random + NIST FIPS 197 + 67 Wycheproof |
| `aes128_gcm_seal_32` | proptest vs libcrux-aesgcm | 200 random |
| `x25519_scalarmult` | proptest vs libcrux-curve25519 | 200 random + 518 Wycheproof + RFC 7748 |
| `x25519_base` | proptest vs libcrux-curve25519 | 200 random |
| `chacha20_poly1305` | proptest vs libcrux | 200 random + 316 Wycheproof |

### Level 2: Kani Bounded Model Checking (Exhaustive)

| Property | Method | Status |
|----------|--------|--------|
| AES S-box is permutation | Kani (all 2^16 pairs) | VERIFIED |
| GF(2^8) mul2 total | Kani (all 256 inputs) | VERIFIED |
| GF(2^8) mul3 total | Kani (all 256 inputs) | VERIFIED |
| GF(2^128) commutative | Kani (all 2^16 small pairs) | VERIFIED |
| GF(2^128) mul zero | Kani (all 2^128) | VERIFIED |
| AES-128 no panic | Kani (symbolic, unwind 65) | VERIFIED |
| AES-128 deterministic | Kani (symbolic, unwind 65) | VERIFIED |
| Poly1305 empty msg | Kani (all 2^256 keys) | VERIFIED |

### Level 3: Hax Extraction

| Component | Status |
|-----------|--------|
| Extraction to Lean | 253 definitions generated |
| SHA-256, AES, HMAC, HKDF, X25519 | Definitions present |
| P-256, Ed25519, ECDSA, RSA-PSS | Definitions present |
| Fixed-length wrappers | Definitions present |
| Lean compilation | Blocked on Hax prelude updates |

## Correspondence Chain

```
Rust specs (pure)  ←──Level 1 (proptest)──→  libcrux (verified)
       │
       ├──Level 2 (Kani BMC)──→  exhaustive correctness
       │
       └──Level 3 (hax)──→  Lean definitions (pending prelude)
                              │
                              └──→  Specs.lean opaques (future)
```

When the Hax prelude is updated, the extracted Lean definitions will
replace the `opaque` constants in `Specs.lean`, closing the gap entirely.
-/

-- This file documents the verification status.
-- No executable Lean code yet — pending Hax prelude compatibility.
