//! Pure Rust hacspec-style specifications of all libcrux primitives.
//!
//! Zero dependencies. All functions are pure, value-passing, and use only
//! plain Rust types (`u8`, `u32`, `u64`, `[u8; N]`, `Vec<u8>`).

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
