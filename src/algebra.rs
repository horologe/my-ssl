use std::mem;

use num_bigint::{BigInt, RandBigInt};
use num_integer::Integer;
use num_traits::Zero;

/// バイナリー・ユークリッドの互助法により、aとbの最大公約数を返す
pub fn gcd(a: &BigInt, b: &BigInt) -> BigInt {
    assert!(BigInt::from(0) <= *a);
    assert!(BigInt::from(0) <= *b);

    let mut a = a.clone();
    let mut b = b.clone();
    let mut g = 0u32;

    while !a.is_zero() {
        if a.is_even() && b.is_even() {
            a >>= 1;
            b >>= 1;
            g += 1;
        } else if a.is_even() && b.is_odd() {
            a >>= 1;
        } else if a.is_odd() && b.is_even() {
            b >>= 1;
        } else { 
            // aもbも奇数なので、差a-bは偶数になる
            if a < b {
                b -= &a;
                b >>= 1;
            } else {
                a -= &b;
                a >>= 1;
            }
        }
    }

    return b << g;
}

/// ユークリッドの互助法により、ax + by = gcd(a, b)を満たす(gcd, a, b)を返す
pub fn extended_gcd(a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
    let (mut old_r, mut r) = (a.clone(), b.clone());
    let (mut old_x, mut x) = (BigInt::from(1), BigInt::from(0));
    let (mut old_y, mut y) = (BigInt::from(0), BigInt::from(1));

    while !r.is_zero() {
        // old_r = old_x * a + old_y * b
        //     r =     x * a +     y * b
        let (quotient, remainder) = old_r.div_rem(&r);
        old_r = mem::replace(&mut r, remainder);
        let temp_x =  old_x - &quotient * &x;
        let temp_y =  old_y - &quotient * &y;
        old_x = mem::replace(&mut x, temp_x);
        old_y = mem::replace(&mut y, temp_y);
    }

    return (old_r, old_x, old_y);
}

// スライディングウィンドウ法を用いた冪乗の計算
// mod_pow(a, b, n, w) = a^m (mod n)
pub fn mod_pow(a: &BigInt, m: &BigInt, n: &BigInt, w: usize) -> BigInt {
    assert!(BigInt::from(0) <= *m);
    assert!(BigInt::from(0) < *n);

    let mut ar = vec![BigInt::from(0);1<<(w-1)];
    ar[0] = a % n;
    for j in 1..(1<<(w-1)) {
        ar[j] = &ar[j-1] * (a * a % n) % n;
    }

    let mut s = BigInt::from(1);
    let mut j = m.bits() as i64 - 1;
    while 0 <= j {
        if !m.bit(j as u64) {
            s = &s * &s;
            s %= n;
            j -= 1;
        } else {
            let mut l = i64::max(j - w as i64 + 1, 0) as u64;
            while 1 < j {
                if m.bit(l) {
                    break;
                }
                l += 1;
            }
            let mut mjl = 0;
            for i in (l..=j as u64).rev() {
                mjl <<= 1;
                if m.bit(i) {
                    mjl |= 1;
                }
                s = &s * &s;
                s %= n;
            }
            
            s *= &ar[mjl >> 1];
            s %= n;
            j = l as i64 - 1;
        }
    }
    return s;
}

/// 中国人剰余定理を用いた署名（暗号化）
pub fn sign(c: &BigInt, p: &BigInt, q: &BigInt, dp: &BigInt, dq: &BigInt, v: &BigInt) -> BigInt {
    let cp = c % p;
    let cq = c % q;
    let mp = mod_pow(&cp, dp, p, 4);
    let mq = mod_pow(&cq, dq, q, 4);
    let vv = v * (mq - &mp) % q;
    return vv * p + mp;
}

/// フェルマーテストを用いて素数判定をする
/// ```rust
/// use num_bigint::BigInt;
/// use my_ssl::algebra::is_probable_prime;
/// assert!(is_probable_prime(&BigInt::from(998244353), 134143));
/// ```
pub fn is_probable_prime(r: &BigInt, t: i32) -> bool {
    assert!(BigInt::from(3) <= *r && r.bit(0) && 0 < t);
    let rm1 = r - BigInt::from(1);
    for _ in (0..t).rev() {
        let mut random = rand::thread_rng();
        let mut a;
        while {
            a = random.gen_bigint(r.bits());
        a <= BigInt::from(1) && a >= rm1 } {}
        let sr = mod_pow(&a, &rm1, r, 4);
        if sr != BigInt::from(1) {
            return false;
        }
    }
    return true;
}
