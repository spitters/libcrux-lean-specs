//! Pure Rust RSA-PSS specification (RFC 8017 / PKCS#1 v2.2).
//!
//! Implements RSA-PSS signing and verification with SHA-256 as the hash
//! function and salt length = hash length = 32 bytes.
//!
//! No external dependencies. All functions are pure and value-passing.
//! Uses `crate::sha256::sha256` for the underlying hash.

use crate::sha256::sha256;

// ========================================================================
// Minimal bignum arithmetic (little-endian u64 limbs)
// ========================================================================

/// Convert big-endian bytes to a little-endian limb vector.
pub fn bn_from_bytes_be(bytes: &[u8]) -> Vec<u64> {
    if bytes.is_empty() {
        return vec![0];
    }

    // Number of 8-byte limbs needed
    let num_limbs = (bytes.len() + 7) / 8;
    let mut limbs = vec![0u64; num_limbs];

    // Walk bytes from least significant (end) to most significant (start)
    for i in 0..bytes.len() {
        let byte_pos = bytes.len() - 1 - i; // position in big-endian array
        let limb_idx = i / 8;
        let bit_offset = (i % 8) * 8;
        limbs[limb_idx] |= (bytes[byte_pos] as u64) << bit_offset;
    }

    limbs
}

/// Serialize a limb vector to fixed-length big-endian bytes.
pub fn bn_to_bytes_be(a: &[u64], byte_len: usize) -> Vec<u8> {
    let mut result = vec![0u8; byte_len];

    for i in 0..byte_len {
        let limb_idx = i / 8;
        let bit_offset = (i % 8) * 8;
        if limb_idx < a.len() {
            result[byte_len - 1 - i] = ((a[limb_idx] >> bit_offset) & 0xff) as u8;
        }
    }

    result
}

/// Compare two bignum values. Returns Ordering.
pub fn bn_cmp(a: &[u64], b: &[u64]) -> std::cmp::Ordering {
    // Find effective lengths (ignoring leading zero limbs)
    let a_len = effective_len(a);
    let b_len = effective_len(b);

    if a_len != b_len {
        return a_len.cmp(&b_len);
    }

    // Same effective length: compare from most significant limb downward
    if a_len == 0 {
        return std::cmp::Ordering::Equal;
    }
    let mut i = a_len;
    while i > 0 {
        i -= 1;
        let la = if i < a.len() { a[i] } else { 0 };
        let lb = if i < b.len() { b[i] } else { 0 };
        if la != lb {
            return la.cmp(&lb);
        }
    }
    std::cmp::Ordering::Equal
}

/// Return the number of significant limbs (ignoring trailing zero limbs in
/// the little-endian representation, i.e. leading zeros of the number).
fn effective_len(a: &[u64]) -> usize {
    let mut n = a.len();
    while n > 0 && a[n - 1] == 0 {
        n -= 1;
    }
    n
}

/// Check whether a bignum is zero.
pub fn bn_is_zero(a: &[u64]) -> bool {
    effective_len(a) == 0
}

/// Remove trailing zero limbs (normalize the representation).
fn bn_trim(a: &[u64]) -> Vec<u64> {
    let n = effective_len(a);
    if n == 0 {
        vec![0]
    } else {
        a[..n].to_vec()
    }
}

/// Add two bignums. Returns a + b (may grow by one limb).
pub fn bn_add(a: &[u64], b: &[u64]) -> Vec<u64> {
    let len = if a.len() > b.len() { a.len() } else { b.len() };
    let mut result = vec![0u64; len + 1];
    let mut carry: u64 = 0;

    for i in 0..len {
        let la = if i < a.len() { a[i] } else { 0 };
        let lb = if i < b.len() { b[i] } else { 0 };
        let (sum1, c1) = la.overflowing_add(lb);
        let (sum2, c2) = sum1.overflowing_add(carry);
        result[i] = sum2;
        carry = (c1 as u64) + (c2 as u64);
    }
    result[len] = carry;

    bn_trim(&result)
}

/// Subtract two bignums. Assumes a >= b.
pub fn bn_sub(a: &[u64], b: &[u64]) -> Vec<u64> {
    let len = a.len();
    let mut result = vec![0u64; len];
    let mut borrow: u64 = 0;

    for i in 0..len {
        let la = a[i];
        let lb = if i < b.len() { b[i] } else { 0 };
        let (diff1, b1) = la.overflowing_sub(lb);
        let (diff2, b2) = diff1.overflowing_sub(borrow);
        result[i] = diff2;
        borrow = (b1 as u64) + (b2 as u64);
    }

    result
}

/// Schoolbook multiplication of two bignums.
pub fn bn_mul(a: &[u64], b: &[u64]) -> Vec<u64> {
    let a = bn_trim(a);
    let b = bn_trim(b);

    if bn_is_zero(&a) || bn_is_zero(&b) {
        return vec![0];
    }

    let mut result = vec![0u64; a.len() + b.len()];

    for i in 0..a.len() {
        let mut carry: u64 = 0;
        for j in 0..b.len() {
            // Multiply a[i] * b[j] as 128-bit, add to result[i+j] + carry
            let prod = (a[i] as u128) * (b[j] as u128)
                + (result[i + j] as u128)
                + (carry as u128);
            result[i + j] = prod as u64;
            carry = (prod >> 64) as u64;
        }
        result[i + b.len()] = carry;
    }

    bn_trim(&result)
}

/// Return the number of significant bits in a bignum.
pub fn bn_bit_length(a: &[u64]) -> usize {
    let elen = effective_len(a);
    if elen == 0 {
        return 0;
    }
    let top = a[elen - 1];
    (elen - 1) * 64 + (64 - top.leading_zeros() as usize)
}

/// Division and modulus: returns (quotient, remainder) such that a = q * b + r.
/// Panics if b is zero.
pub fn bn_divmod(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    let a = bn_trim(a);
    let b = bn_trim(b);

    assert!(!bn_is_zero(&b), "division by zero");

    if bn_cmp(&a, &b) == std::cmp::Ordering::Less {
        return (vec![0], a.to_vec());
    }

    let a_bits = bn_bit_length(&a);

    // Long division, one bit at a time, with in-place remainder manipulation
    let rem_limbs = b.len() + 1; // enough limbs for the remainder
    let mut remainder = vec![0u64; rem_limbs];
    let q_limbs = if a.len() > 0 { a.len() } else { 1 };
    let mut quotient = vec![0u64; q_limbs];

    for i in (0..a_bits).rev() {
        // Shift remainder left by 1 (in-place)
        let mut carry = 0u64;
        for k in 0..rem_limbs {
            let new_carry = remainder[k] >> 63;
            remainder[k] = (remainder[k] << 1) | carry;
            carry = new_carry;
        }

        // Set the lowest bit of remainder to bit i of a
        let limb_idx = i / 64;
        let bit_idx = i % 64;
        if limb_idx < a.len() {
            remainder[0] |= (a[limb_idx] >> bit_idx) & 1;
        }

        // If remainder >= b, subtract b and set quotient bit
        if bn_cmp(&remainder, &b) != std::cmp::Ordering::Less {
            // In-place subtraction: remainder -= b
            let mut borrow: u64 = 0;
            for k in 0..rem_limbs {
                let bk = if k < b.len() { b[k] } else { 0 };
                let (d1, b1) = remainder[k].overflowing_sub(bk);
                let (d2, b2) = d1.overflowing_sub(borrow);
                remainder[k] = d2;
                borrow = (b1 as u64) + (b2 as u64);
            }

            let q_limb = i / 64;
            let q_bit = i % 64;
            if q_limb < quotient.len() {
                quotient[q_limb] |= 1u64 << q_bit;
            }
        }
    }

    (bn_trim(&quotient), bn_trim(&remainder))
}

/// Compute a mod m.
pub fn bn_mod(a: &[u64], m: &[u64]) -> Vec<u64> {
    let (_, r) = bn_divmod(a, m);
    bn_trim(&r)
}

/// Modular exponentiation: base^exp mod modulus (square-and-multiply).
pub fn bn_modpow(base: &[u64], exp: &[u64], modulus: &[u64]) -> Vec<u64> {
    assert!(!bn_is_zero(modulus), "modulus must be nonzero");

    let exp_bits = bn_bit_length(exp);
    if exp_bits == 0 {
        // base^0 = 1 (when modulus > 1)
        return bn_mod(&[1], modulus);
    }

    let mut result = vec![1u64];
    let mut base_acc = bn_mod(base, modulus);

    for i in 0..exp_bits {
        let limb_idx = i / 64;
        let bit_idx = i % 64;
        let bit = if limb_idx < exp.len() {
            (exp[limb_idx] >> bit_idx) & 1
        } else {
            0
        };

        if bit == 1 {
            result = bn_mod(&bn_mul(&result, &base_acc), modulus);
        }
        base_acc = bn_mod(&bn_mul(&base_acc, &base_acc), modulus);
    }

    result
}

// ========================================================================
// RSA primitives
// ========================================================================

/// RSAEP: RSA encryption / verification primitive.
/// Computes m^e mod n.
pub fn rsaep(n: &[u64], e: &[u64], m: &[u64]) -> Vec<u64> {
    bn_modpow(m, e, n)
}

/// RSADP: RSA decryption / signing primitive.
/// Computes c^d mod n.
pub fn rsadp(n: &[u64], d: &[u64], c: &[u64]) -> Vec<u64> {
    bn_modpow(c, d, n)
}

// ========================================================================
// OS2IP / I2OSP (Octet String <-> Integer conversions, RFC 8017 Sec 4)
// ========================================================================

/// OS2IP: Convert an octet string to a nonneg integer (big-endian).
pub fn os2ip(bytes: &[u8]) -> Vec<u64> {
    bn_from_bytes_be(bytes)
}

/// I2OSP: Convert a nonneg integer to an octet string of length `len`.
pub fn i2osp(n: &[u64], len: usize) -> Vec<u8> {
    bn_to_bytes_be(n, len)
}

// ========================================================================
// MGF1-SHA256 (RFC 8017 Appendix B.2.1)
// ========================================================================

/// MGF1 mask generation function using SHA-256.
///
/// T = T || SHA-256(seed || counter) for counter = 0, 1, 2, ...
/// Returns the first `mask_len` bytes of T.
pub fn mgf1_sha256(seed: &[u8], mask_len: usize) -> Vec<u8> {
    let mut t = Vec::new();
    let mut counter: u32 = 0;

    while t.len() < mask_len {
        // Build seed || counter (big-endian 4 bytes)
        let counter_bytes = counter.to_be_bytes();
        let mut input = Vec::with_capacity(seed.len() + 4);
        for i in 0..seed.len() {
            input.push(seed[i]);
        }
        for i in 0..4 {
            input.push(counter_bytes[i]);
        }

        let hash = sha256(&input);
        for i in 0..32 {
            t.push(hash[i]);
        }
        counter += 1;
    }

    t.truncate(mask_len);
    t
}

// ========================================================================
// EMSA-PSS (RFC 8017 Section 9.1)
// ========================================================================

/// Hash length in bytes (SHA-256).
pub const HASH_LEN: usize = 32;

/// Salt length in bytes (= hash length for RSA-PSS with SHA-256).
pub const SALT_LEN: usize = 32;

/// EMSA-PSS encoding (RFC 8017 Section 9.1.1).
///
/// Inputs:
///   - `msg_hash`: the SHA-256 hash of the message to sign
///   - `em_bits`: the maximal bit length of the encoded message (typically
///     `bit_length(n) - 1`)
///   - `salt`: a 32-byte random salt
///
/// Returns the encoded message EM of length ceil(em_bits / 8).
pub fn emsa_pss_encode(msg_hash: &[u8; 32], em_bits: usize, salt: &[u8; 32]) -> Vec<u8> {
    let em_len = (em_bits + 7) / 8;

    // Step 3: M' = (0x)00 00 00 00 00 00 00 00 || mHash || salt
    let mut m_prime = Vec::with_capacity(8 + HASH_LEN + SALT_LEN);
    for _ in 0..8 {
        m_prime.push(0x00);
    }
    for i in 0..HASH_LEN {
        m_prime.push(msg_hash[i]);
    }
    for i in 0..SALT_LEN {
        m_prime.push(salt[i]);
    }

    // Step 4: H = SHA-256(M')
    let h = sha256(&m_prime);

    // Step 5: PS = zero bytes of length em_len - SALT_LEN - HASH_LEN - 2
    let ps_len = em_len - SALT_LEN - HASH_LEN - 2;

    // Step 6: DB = PS || 0x01 || salt
    let db_len = em_len - HASH_LEN - 1;
    let mut db = Vec::with_capacity(db_len);
    for _ in 0..ps_len {
        db.push(0x00);
    }
    db.push(0x01);
    for i in 0..SALT_LEN {
        db.push(salt[i]);
    }

    // Step 7: dbMask = MGF1(H, em_len - hLen - 1)
    let db_mask = mgf1_sha256(&h, db_len);

    // Step 8: maskedDB = DB XOR dbMask
    let mut masked_db = vec![0u8; db_len];
    for i in 0..db_len {
        masked_db[i] = db[i] ^ db_mask[i];
    }

    // Step 9: Set the leftmost (8 * em_len - em_bits) bits of maskedDB[0] to zero
    let top_bits_to_clear = 8 * em_len - em_bits;
    if top_bits_to_clear > 0 {
        let mask = 0xffu8 >> top_bits_to_clear;
        masked_db[0] &= mask;
    }

    // Step 10: EM = maskedDB || H || 0xbc
    let mut em = Vec::with_capacity(em_len);
    for i in 0..db_len {
        em.push(masked_db[i]);
    }
    for i in 0..HASH_LEN {
        em.push(h[i]);
    }
    em.push(0xbc);

    em
}

/// EMSA-PSS verification (RFC 8017 Section 9.1.2).
///
/// Inputs:
///   - `msg_hash`: the SHA-256 hash of the received message
///   - `em`: the encoded message to verify
///   - `em_bits`: the maximal bit length (same value used in encoding)
///
/// Returns true iff the encoded message is consistent with the hash.
pub fn emsa_pss_verify(msg_hash: &[u8; 32], em: &[u8], em_bits: usize) -> bool {
    let em_len = (em_bits + 7) / 8;

    // Step 3: If emLen < hLen + sLen + 2, output "inconsistent"
    if em_len < HASH_LEN + SALT_LEN + 2 {
        return false;
    }

    // Step 4: If the rightmost byte of EM is not 0xbc, output "inconsistent"
    if em[em_len - 1] != 0xbc {
        return false;
    }

    // Step 5: Let maskedDB be the leftmost em_len - hLen - 1 bytes of EM,
    //         and let H be the next hLen bytes
    let db_len = em_len - HASH_LEN - 1;
    let masked_db = &em[0..db_len];
    let h = &em[db_len..db_len + HASH_LEN];

    // Step 6: Check that the top (8 * em_len - em_bits) bits of maskedDB[0] are zero
    let top_bits_to_clear = 8 * em_len - em_bits;
    if top_bits_to_clear > 0 {
        let top_mask = 0xffu8 << (8 - top_bits_to_clear);
        if (masked_db[0] & top_mask) != 0 {
            return false;
        }
    }

    // Step 7: dbMask = MGF1(H, em_len - hLen - 1)
    let db_mask = mgf1_sha256(h, db_len);

    // Step 8: DB = maskedDB XOR dbMask
    let mut db = vec![0u8; db_len];
    for i in 0..db_len {
        db[i] = masked_db[i] ^ db_mask[i];
    }

    // Step 9: Set the leftmost (8 * em_len - em_bits) bits of DB[0] to zero
    if top_bits_to_clear > 0 {
        let mask = 0xffu8 >> top_bits_to_clear;
        db[0] &= mask;
    }

    // Step 10: Check that the leftmost (em_len - hLen - sLen - 2) bytes of DB are zero
    //          and that the byte at position (em_len - hLen - sLen - 2) is 0x01
    let ps_len = em_len - HASH_LEN - SALT_LEN - 2;
    for i in 0..ps_len {
        if db[i] != 0x00 {
            return false;
        }
    }
    if db[ps_len] != 0x01 {
        return false;
    }

    // Step 11: Extract the last sLen bytes of DB as salt
    let salt_start = db_len - SALT_LEN;
    let salt = &db[salt_start..salt_start + SALT_LEN];

    // Step 12: M' = (0x)00 00 00 00 00 00 00 00 || mHash || salt
    let mut m_prime = Vec::with_capacity(8 + HASH_LEN + SALT_LEN);
    for _ in 0..8 {
        m_prime.push(0x00);
    }
    for i in 0..HASH_LEN {
        m_prime.push(msg_hash[i]);
    }
    for i in 0..SALT_LEN {
        m_prime.push(salt[i]);
    }

    // Step 13: H' = SHA-256(M')
    let h_prime = sha256(&m_prime);

    // Step 14: If H == H', output "consistent"; otherwise "inconsistent"
    for i in 0..HASH_LEN {
        if h[i] != h_prime[i] {
            return false;
        }
    }

    true
}

// ========================================================================
// Bit-length helper for byte-encoded modulus
// ========================================================================

/// Return the bit length of an integer given its big-endian byte encoding.
/// This is the position of the highest set bit.
pub fn byte_bit_length(bytes: &[u8]) -> usize {
    // Skip leading zero bytes
    let mut start = 0;
    while start < bytes.len() && bytes[start] == 0 {
        start += 1;
    }
    if start == bytes.len() {
        return 0;
    }
    let top_byte = bytes[start];
    let bits_in_top = 8 - top_byte.leading_zeros() as usize;
    bits_in_top + (bytes.len() - start - 1) * 8
}

// ========================================================================
// RSA-PSS Sign and Verify (RFC 8017 Section 8.1)
// ========================================================================

/// RSA-PSS signature generation (RFC 8017 Section 8.1.1).
///
/// Inputs:
///   - `n`: the RSA modulus (big-endian bytes)
///   - `d`: the RSA private exponent (big-endian bytes)
///   - `msg`: the message to sign
///   - `salt`: a 32-byte random salt
///
/// Returns the signature as big-endian bytes with the same byte length as `n`.
pub fn rsa_pss_sign(n: &[u8], d: &[u8], msg: &[u8], salt: &[u8; 32]) -> Vec<u8> {
    let mod_bits = byte_bit_length(n);
    let k = (mod_bits + 7) / 8; // byte length of n

    // Step 1: msg_hash = SHA-256(msg)
    let msg_hash = sha256(msg);

    // Step 2: em_bits = modBits - 1
    let em_bits = mod_bits - 1;

    // Step 3: EM = EMSA-PSS-ENCODE(msg_hash, em_bits, salt)
    let em = emsa_pss_encode(&msg_hash, em_bits, salt);

    // Step 4: m = OS2IP(EM)
    let m = os2ip(&em);

    // Step 5: s = RSASP1(n, d, m) = m^d mod n
    let n_bn = bn_from_bytes_be(n);
    let d_bn = bn_from_bytes_be(d);
    let s = rsadp(&n_bn, &d_bn, &m);

    // Step 6: S = I2OSP(s, k)
    i2osp(&s, k)
}

/// RSA-PSS signature verification (RFC 8017 Section 8.1.2).
///
/// Inputs:
///   - `n`: the RSA modulus (big-endian bytes)
///   - `e`: the RSA public exponent (big-endian bytes)
///   - `msg`: the message whose signature is being verified
///   - `sig`: the signature to verify (big-endian bytes)
///
/// Returns true iff the signature is valid.
pub fn rsa_pss_verify(n: &[u8], e: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    let mod_bits = byte_bit_length(n);
    let em_len = ((mod_bits - 1) + 7) / 8;

    // Step 1: s = OS2IP(S)
    let s = os2ip(sig);

    // Step 2: m = RSAVP1(n, e, s) = s^e mod n
    let n_bn = bn_from_bytes_be(n);
    let e_bn = bn_from_bytes_be(e);
    let m = rsaep(&n_bn, &e_bn, &s);

    // Step 3: EM = I2OSP(m, emLen)
    let em = i2osp(&m, em_len);

    // Step 4: msg_hash = SHA-256(msg)
    let msg_hash = sha256(msg);

    // Step 5: EMSA-PSS-VERIFY(msg_hash, EM, modBits - 1)
    emsa_pss_verify(&msg_hash, &em, mod_bits - 1)
}

// ========================================================================
// Tests
// ========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --- Bignum unit tests ---

    #[test]
    fn test_bn_from_to_bytes_roundtrip() {
        let bytes = vec![0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0xfe];
        let bn = bn_from_bytes_be(&bytes);
        let out = bn_to_bytes_be(&bn, bytes.len());
        assert_eq!(out, bytes);
    }

    #[test]
    fn test_bn_add() {
        // 255 + 1 = 256
        let a = bn_from_bytes_be(&[0xff]);
        let b = bn_from_bytes_be(&[0x01]);
        let sum = bn_add(&a, &b);
        let out = bn_to_bytes_be(&sum, 2);
        assert_eq!(out, vec![0x01, 0x00]);
    }

    #[test]
    fn test_bn_sub() {
        // 256 - 1 = 255
        let a = bn_from_bytes_be(&[0x01, 0x00]);
        let b = bn_from_bytes_be(&[0x01]);
        let diff = bn_sub(&a, &b);
        let out = bn_to_bytes_be(&diff, 1);
        assert_eq!(out, vec![0xff]);
    }

    #[test]
    fn test_bn_mul() {
        // 255 * 255 = 65025 = 0xfe01
        let a = bn_from_bytes_be(&[0xff]);
        let b = bn_from_bytes_be(&[0xff]);
        let prod = bn_mul(&a, &b);
        let out = bn_to_bytes_be(&prod, 2);
        assert_eq!(out, vec![0xfe, 0x01]);
    }

    #[test]
    fn test_bn_divmod() {
        // 65025 / 255 = (255, 0)
        let a = bn_from_bytes_be(&[0xfe, 0x01]);
        let b = bn_from_bytes_be(&[0xff]);
        let (q, r) = bn_divmod(&a, &b);
        assert_eq!(bn_to_bytes_be(&q, 1), vec![0xff]);
        assert!(bn_is_zero(&r));
    }

    #[test]
    fn test_bn_divmod_remainder() {
        // 100 / 7 = (14, 2)
        let a = bn_from_bytes_be(&[100]);
        let b = bn_from_bytes_be(&[7]);
        let (q, r) = bn_divmod(&a, &b);
        let q_val = bn_to_bytes_be(&q, 1);
        let r_val = bn_to_bytes_be(&r, 1);
        assert_eq!(q_val, vec![14]);
        assert_eq!(r_val, vec![2]);
    }

    #[test]
    fn test_bn_modpow() {
        // 3^13 mod 497 = 444
        let base = bn_from_bytes_be(&[3]);
        let exp = bn_from_bytes_be(&[13]);
        let modulus = bn_from_bytes_be(&[0x01, 0xf1]); // 497
        let result = bn_modpow(&base, &exp, &modulus);
        let out = bn_to_bytes_be(&result, 2);
        assert_eq!(out, vec![0x01, 0xbc]); // 444

        // 2^10 mod 1000 = 1024 mod 1000 = 24
        let base2 = bn_from_bytes_be(&[2]);
        let exp2 = bn_from_bytes_be(&[10]);
        let mod2 = bn_from_bytes_be(&[0x03, 0xe8]); // 1000
        let result2 = bn_modpow(&base2, &exp2, &mod2);
        let out2 = bn_to_bytes_be(&result2, 1);
        assert_eq!(out2, vec![24]);
    }

    #[test]
    fn test_bn_cmp() {
        let a = bn_from_bytes_be(&[0x01, 0x00]);
        let b = bn_from_bytes_be(&[0xff]);
        assert_eq!(bn_cmp(&a, &b), std::cmp::Ordering::Greater);

        let c = bn_from_bytes_be(&[0x01, 0x00]);
        assert_eq!(bn_cmp(&a, &c), std::cmp::Ordering::Equal);
    }

    #[test]
    fn test_bn_bit_length() {
        assert_eq!(bn_bit_length(&bn_from_bytes_be(&[0x00])), 0);
        assert_eq!(bn_bit_length(&bn_from_bytes_be(&[0x01])), 1);
        assert_eq!(bn_bit_length(&bn_from_bytes_be(&[0x80])), 8);
        assert_eq!(bn_bit_length(&bn_from_bytes_be(&[0x01, 0x00])), 9);
    }

    // --- MGF1 test ---

    #[test]
    fn test_mgf1_sha256_basic() {
        // MGF1 with empty seed, mask_len = 32: should be SHA-256([] || 0x00000000)
        let mask = mgf1_sha256(&[], 32);
        let mut input = Vec::new();
        input.extend_from_slice(&0u32.to_be_bytes());
        let expected = sha256(&input);
        assert_eq!(mask.len(), 32);
        assert_eq!(mask, expected.to_vec());
    }

    #[test]
    fn test_mgf1_sha256_longer() {
        // MGF1 with mask_len > 32 produces concatenation of multiple hashes
        let seed = b"test seed";
        let mask = mgf1_sha256(seed, 64);
        assert_eq!(mask.len(), 64);

        // First 32 bytes = SHA-256(seed || 0x00000000)
        let mut in0 = seed.to_vec();
        in0.extend_from_slice(&0u32.to_be_bytes());
        let h0 = sha256(&in0);
        assert_eq!(&mask[0..32], &h0[..]);

        // Next 32 bytes = SHA-256(seed || 0x00000001)
        let mut in1 = seed.to_vec();
        in1.extend_from_slice(&1u32.to_be_bytes());
        let h1 = sha256(&in1);
        assert_eq!(&mask[32..64], &h1[..]);
    }

    // --- EMSA-PSS encode/verify roundtrip ---

    #[test]
    fn test_emsa_pss_roundtrip() {
        let msg = b"test message for EMSA-PSS";
        let msg_hash = sha256(msg);

        let salt: [u8; 32] = [
            0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
            0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00,
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
            0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10,
        ];

        // For a 2048-bit key: em_bits = 2047
        let em_bits = 2047;
        let em = emsa_pss_encode(&msg_hash, em_bits, &salt);

        // Verify the encoded message
        let ok = emsa_pss_verify(&msg_hash, &em, em_bits);
        assert!(ok, "EMSA-PSS encode/verify roundtrip failed");
    }

    #[test]
    fn test_emsa_pss_wrong_hash() {
        let msg_hash = sha256(b"correct message");
        let wrong_hash = sha256(b"wrong message");

        let salt = [0xabu8; 32];
        let em_bits = 2047;
        let em = emsa_pss_encode(&msg_hash, em_bits, &salt);

        // Verify with wrong hash should fail
        let ok = emsa_pss_verify(&wrong_hash, &em, em_bits);
        assert!(!ok, "EMSA-PSS should reject wrong message hash");
    }

    // --- RSA-PSS sign/verify self-consistency test ---

    /// Decode a hex string into bytes.
    fn hex_to_bytes(hex: &str) -> Vec<u8> {
        let hex = hex.replace(' ', "").replace('\n', "");
        let mut bytes = Vec::with_capacity(hex.len() / 2);
        let mut i = 0;
        while i < hex.len() {
            let byte = u8::from_str_radix(&hex[i..i + 2], 16).unwrap();
            bytes.push(byte);
            i += 2;
        }
        bytes
    }

    /// Self-consistency test with a 1024-bit RSA key.
    ///
    /// This is NOT a secure key size by modern standards; it is used only
    /// to verify that the sign/verify logic is internally consistent.
    /// (RSA-PSS with SHA-256 and sLen=32 requires modBits >= 529.)
    #[test]
    fn test_rsa_pss_sign_verify_consistency() {
        // 1024-bit RSA key pair (test-only)
        #[rustfmt::skip]
        let n = hex_to_bytes(
            "735c82f12869b38bb08992f8e42917469c0ae85a4e0fd85855e2c3979aa16c31\
             d324035efc4fe9851b1a401a60eb5b9fac9671267fc77f4db432cbe49ce552e3\
             80b96a4f269c9747023d551c40b55d5fce20750d437d83d8974ba2322008706a\
             a6355839c6a51790ac653c67ed28088844fa40118b8df6b01003d591b31366ff"
        );
        #[rustfmt::skip]
        let e_bytes = hex_to_bytes("010001");
        #[rustfmt::skip]
        let d = hex_to_bytes(
            "2cf88763136a01401755ca219470204eba4dd63e3de817627838aa1ed37cd1fc\
             aa5e83a1e7a20f5a80323f8308fd36fe8bfd29a6e47114c369d7d37c0f5da66d\
             d8cec3ea8ad766a9f055341a618bab5db5818805faaca1b421509981958880f8\
             8cbe25d026c399eaba58b51acd1b36957d399e5c76e8ba84a29c5759ebd649a1"
        );

        let msg = b"RSA-PSS self-consistency test message";
        let salt: [u8; 32] = [
            0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe,
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
            0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10,
            0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
        ];

        // Sign
        let sig = rsa_pss_sign(&n, &d, msg, &salt);
        assert_eq!(sig.len(), n.len(), "Signature length should equal modulus length");

        // Verify
        let ok = rsa_pss_verify(&n, &e_bytes, msg, &sig);
        assert!(ok, "RSA-PSS sign/verify self-consistency failed");

        // Verify with wrong message should fail
        let bad = rsa_pss_verify(&n, &e_bytes, b"wrong message", &sig);
        assert!(!bad, "RSA-PSS verify should reject wrong message");
    }

    /// Verify that byte_bit_length computes correctly.
    #[test]
    fn test_byte_bit_length() {
        assert_eq!(byte_bit_length(&[0x00]), 0);
        assert_eq!(byte_bit_length(&[0x01]), 1);
        assert_eq!(byte_bit_length(&[0x80]), 8);
        assert_eq!(byte_bit_length(&[0x01, 0x00]), 9);
        assert_eq!(byte_bit_length(&[0xff]), 8);
        assert_eq!(byte_bit_length(&[0x00, 0xff]), 8);
        // 2048-bit number: leading 0x80 byte followed by 255 zero bytes
        let mut big = vec![0x80u8];
        big.extend_from_slice(&[0x00; 255]);
        assert_eq!(byte_bit_length(&big), 2048);
    }

    /// Test I2OSP / OS2IP roundtrip.
    #[test]
    fn test_os2ip_i2osp_roundtrip() {
        let bytes = vec![0x00, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef];
        let n = os2ip(&bytes);
        let out = i2osp(&n, bytes.len());
        assert_eq!(out, bytes);
    }
}
