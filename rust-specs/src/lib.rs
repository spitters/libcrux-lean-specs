//! Pure Rust hacspec-style specifications of all libcrux primitives.
//!
//! Zero dependencies. All functions are pure, value-passing, and use only
//! plain Rust types (`u8`, `u32`, `u64`, `[u8; N]`, `Vec<u8>`).
//!
//! Hacspec-style specs intentionally use explicit element-by-element loops
//! (rather than `copy_from_slice`/iterators) to mirror the textual structure
//! of the underlying RFCs/NIST documents and to keep the code amenable to
//! verification via `hax`. The lint allows below silence clippy suggestions
//! to "modernize" these loops into idiomatic Rust.

#![allow(clippy::manual_memcpy)]
#![allow(clippy::needless_range_loop)]
#![allow(clippy::manual_repeat_n)]
#![allow(clippy::assign_op_pattern)]
#![allow(clippy::needless_late_init)]
#![allow(clippy::needless_borrow)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::manual_div_ceil)]
#![allow(clippy::manual_range_contains)]
#![allow(clippy::manual_rotate)]
#![allow(clippy::same_item_push)]
#![allow(clippy::unnecessary_cast)]
#![allow(clippy::let_and_return)]
#![allow(clippy::len_zero)]
#![allow(unused_mut)]
#![allow(unexpected_cfgs)]

// Phase 1: Hash functions
pub mod sha256;
pub mod sha512;
pub mod sha3;
pub mod blake2;

// Phase 2: MACs & KDFs
pub mod hmac;
pub mod hkdf;
pub mod chacha20;
pub mod poly1305;
pub mod chacha20poly1305;

// Phase 3: Block ciphers & AEAD
pub mod aes;
pub mod gf128;
pub mod aes_gcm;

// Phase 4: Elliptic curves
pub mod curve25519;
pub mod p256;
pub mod edwards25519;
pub mod ed25519;
pub mod ecdsa_p256;

// Phase 5: RSA
pub mod rsa_pss;

// Fixed-length wrappers for SSProve bridge
pub mod fixed;

// Kani bounded model checking proofs (only compiled with cargo kani)
#[cfg(kani)]
pub mod kani_proofs;
