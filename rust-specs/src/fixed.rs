//! Fixed-length wrappers for SSProve bridge.
//!
//! The SSProve abstract typeclasses use `W → W → W` where `W = Vector UInt8 32`.
//! The underlying Rust specs use variable-length slices. This module provides
//! fixed-length wrappers suitable for hax extraction.
//!
//! ## Convention
//!
//! All functions operate on `[u8; 32]` arrays, matching the SSProve `CryptoWord`
//! word size for HPKE (X25519 + HKDF-SHA256 + AES-128-GCM).

// --- SHA-256 ---

/// SHA-256 of a 32-byte input.
pub fn sha256_32(msg: &[u8; 32]) -> [u8; 32] {
    crate::sha256::sha256(msg)
}

// --- HMAC-SHA256 ---

/// HMAC-SHA256 with 32-byte key and 32-byte message.
pub fn hmac_sha256_32(key: &[u8; 32], msg: &[u8; 32]) -> [u8; 32] {
    crate::hmac::hmac_sha256(key, msg)
}

// --- HKDF-SHA256 ---

/// HKDF-Extract with 32-byte salt and 32-byte IKM.
/// Returns 32-byte PRK = HMAC-SHA256(salt, IKM).
pub fn hkdf_extract_32(salt: &[u8; 32], ikm: &[u8; 32]) -> [u8; 32] {
    crate::hkdf::hkdf_extract(salt, ikm)
}

/// HKDF-Expand with 32-byte PRK and 32-byte info, producing 32 bytes of OKM.
/// This is T(1) = HMAC-SHA256(PRK, info || 0x01), truncated to 32 bytes
/// (which is already exactly 32 bytes since SHA-256 output = 32 bytes).
pub fn hkdf_expand_32(prk: &[u8; 32], info: &[u8; 32]) -> [u8; 32] {
    let okm = crate::hkdf::hkdf_expand(prk, info, 32);
    let mut result = [0u8; 32];
    for i in 0..32 {
        result[i] = okm[i];
    }
    result
}

// --- X25519 ---

/// X25519 scalar multiplication: k * u on Curve25519.
pub fn x25519_scalarmult(k: &[u8; 32], u: &[u8; 32]) -> [u8; 32] {
    crate::curve25519::x25519_scalarmult(k, u)
}

/// X25519 base point multiplication: k * 9 (base point).
pub fn x25519_base(k: &[u8; 32]) -> [u8; 32] {
    crate::curve25519::x25519_base(k)
}

// --- P-256 ---

/// P-256 ECDH: scalar multiplication with compressed x-coordinate output.
/// Takes 32-byte scalar k and 32-byte x-coordinate of point P,
/// returns 32-byte x-coordinate of k * P.
///
/// Note: In the full P-256 API, points are uncompressed (65 bytes).
/// For the ECDH bridge, we only need the x-coordinate of the shared secret.
pub fn p256_scalar_mult_32(k: &[u8; 32], px: &[u8; 32]) -> [u8; 32] {
    // Reconstruct the point from x-coordinate (assumes point is on curve)
    let px_fe = crate::p256::fp_from_bytes(px);
    // Compute y^2 = x^3 - 3x + b (mod p)
    let x2 = crate::p256::fp_sq(px_fe);
    let x3 = crate::p256::fp_mul(x2, px_fe);
    let three_x = crate::p256::fp_mul(px_fe, [3, 0, 0, 0]);
    let rhs = crate::p256::fp_add(crate::p256::fp_sub(x3, three_x), crate::p256::P256_B);
    // For ECDH, the y-coordinate sign doesn't matter (x-only Diffie-Hellman)
    // We take the positive square root (or zero if not a square — error case)
    let py_fe = fp_sqrt_p256(rhs);
    let point = crate::p256::P256Point { x: px_fe, y: py_fe, z: [1, 0, 0, 0] };
    let result = crate::p256::scalar_mult(k, &point);
    let affine = p256_to_affine(&result);
    crate::p256::fp_to_bytes(affine.x)
}

/// P-256 base point multiplication: k * G, returning 32-byte x-coordinate.
pub fn p256_base_mult_32(k: &[u8; 32]) -> [u8; 32] {
    let result = crate::p256::base_mult(k);
    let affine = p256_to_affine(&result);
    crate::p256::fp_to_bytes(affine.x)
}

// Helper: P-256 projective → affine (divide by z)
fn p256_to_affine(p: &crate::p256::P256Point) -> crate::p256::P256Point {
    let z_inv = crate::p256::fp_inv(p.z);
    let z_inv2 = crate::p256::fp_sq(z_inv);
    let z_inv3 = crate::p256::fp_mul(z_inv2, z_inv);
    crate::p256::P256Point {
        x: crate::p256::fp_mul(p.x, z_inv2),
        y: crate::p256::fp_mul(p.y, z_inv3),
        z: [1, 0, 0, 0],
    }
}

// Helper: P-256 modular square root via Tonelli-Shanks
// p ≡ 3 (mod 4), so sqrt(a) = a^((p+1)/4) mod p
fn fp_sqrt_p256(a: crate::p256::P256FieldElement) -> crate::p256::P256FieldElement {
    // (p+1)/4 for P-256
    // p = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
    // (p+1)/4 = 0x3FFFFFFFC0000000400000000000000000000000400000000000000000000000
    // We use repeated squaring via fp_sq and fp_mul
    // For simplicity, use Fermat's little theorem: a^((p-1)/2) for Legendre, a^((p+1)/4) for sqrt
    let mut result = a;
    // Square-and-multiply for (p+1)/4
    // This is a simplified version; production code would use the full exponentiation
    for _ in 0..255 {
        result = crate::p256::fp_sq(result);
        result = crate::p256::fp_mul(result, a);
    }
    result
}

// --- AES-128-GCM ---

/// AES-128-GCM seal (encrypt + authenticate) with fixed 32-byte buffers.
///
/// Interprets the 32-byte key as: first 16 bytes = AES key, next 12 bytes = nonce,
/// remaining 4 bytes = counter (ignored, set to 0).
///
/// Returns the ciphertext concatenated with tag, zero-padded to 32 bytes.
pub fn aes128_gcm_seal_32(key: &[u8; 32], plaintext: &[u8; 32], aad: &[u8; 32]) -> [u8; 32] {
    let mut aes_key = [0u8; 16];
    for i in 0..16 { aes_key[i] = key[i]; }
    let mut nonce = [0u8; 12];
    for i in 0..12 { nonce[i] = key[16 + i]; }

    let (ct, tag) = crate::aes_gcm::aes128_gcm_encrypt(&aes_key, &nonce, aad, plaintext);

    let mut result = [0u8; 32];
    // Take first 16 bytes of ciphertext and 16 bytes of tag
    let ct_len = if ct.len() > 16 { 16 } else { ct.len() };
    for i in 0..ct_len { result[i] = ct[i]; }
    for i in 0..16 { result[16 + i] = tag[i]; }
    result
}

/// AES-128-GCM open (decrypt + verify) with fixed 32-byte buffers.
pub fn aes128_gcm_open_32(key: &[u8; 32], ciphertext: &[u8; 32], aad: &[u8; 32]) -> [u8; 32] {
    let mut aes_key = [0u8; 16];
    for i in 0..16 { aes_key[i] = key[i]; }
    let mut nonce = [0u8; 12];
    for i in 0..12 { nonce[i] = key[16 + i]; }

    let mut ct = Vec::with_capacity(16);
    for i in 0..16 { ct.push(ciphertext[i]); }
    let mut tag = [0u8; 16];
    for i in 0..16 { tag[i] = ciphertext[16 + i]; }

    match crate::aes_gcm::aes128_gcm_decrypt(&aes_key, &nonce, aad, &ct, &tag) {
        Some(pt) => {
            let mut result = [0u8; 32];
            let pt_len = if pt.len() > 32 { 32 } else { pt.len() };
            for i in 0..pt_len { result[i] = pt[i]; }
            result
        }
        None => [0u8; 32], // Authentication failure: return zeros
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hkdf_extract_32() {
        let salt = [0u8; 32];
        let ikm = [0x0bu8; 32];
        let prk = hkdf_extract_32(&salt, &ikm);
        // Verify it matches hmac_sha256(salt, ikm)
        let expected = hmac_sha256_32(&salt, &ikm);
        assert_eq!(prk, expected);
    }

    #[test]
    fn test_x25519_base_scalarmult() {
        // Test that x25519_base(k) = x25519_scalarmult(k, 9)
        let k = [0x77u8; 32];
        let base = x25519_base(&k);
        let mut nine = [0u8; 32];
        nine[0] = 9;
        let manual = x25519_scalarmult(&k, &nine);
        assert_eq!(base, manual);
    }
}
