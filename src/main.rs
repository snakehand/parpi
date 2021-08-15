/*
 * Computation of the n'th decimal digit of pi with very little memory.
 * Written by Fabrice Bellard on February 26, 1997.
 *
 * We use a slightly modified version of the method described by Simon
 * Plouffe in "On the Computation of the n'th decimal digit of various
 * transcendental numbers" (November 1996). We have modified the algorithm
 * to get a running time of O(n^2) instead of O(n^3log(n)^3).
 *
 * This program uses a variation of the formula found by Gosper in 1974 :
 *
 * pi = sum( (25*n-3)/(binomial(3*n,n)*2^(n-1)), n=0..infinity);
 *
 * This program uses mostly integer arithmetic. It may be slow on some
 * hardwares where integer multiplications and divisons must be done by
 * software. We have supposed that 'int' has a size of at least 32 bits. If
 * your compiler supports 'long long' integers of 64 bits, you may use the
 * integer version of 'mul_mod' (see HAS_LONG_LONG).
 */

/* Ported to Rust by Frank A. Stevenson 2021 */

fn mul_mod(a: i32, b: i32, n: i32) -> i32 {
    (((a as i64) * (b as i64)) % (n as i64)) as i32
}

/* return the inverse of x mod y */
fn inv_mod(x: i32, y: i32) -> i32 {
    // int q, u, v, a, c, t;

    let mut u = x;
    let mut v = y;
    let mut c = 1;
    let mut a = 0;
    loop {
        let q = v / u;

        let mut t = c;
        c = a - q * c;
        a = t;

        t = u;
        u = v - q * u;
        v = t;
        if u == 0 {
            break;
        }
    }

    a = a % y;
    if a < 0 {
        a = y + a;
    }
    a
}

/* return the inverse of u mod v, if v is odd */
fn inv_mod2(u: i32, v: i32) -> i32 {
    let mut u1 = 1;
    let mut u3 = u;

    let mut v1 = v;
    let mut v3 = v;

    let mut t1;
    let mut t3;
    let mut skip = false;

    if (u & 1) != 0 {
        t1 = 0;
        t3 = -v;
        skip = true;
    } else {
        t1 = 1;
        t3 = u;
    }

    loop {
        loop {
            if !skip {
                if (t1 & 1) == 0 {
                    t1 = t1 >> 1;
                    t3 = t3 >> 1;
                } else {
                    t1 = (t1 + v) >> 1;
                    t3 = t3 >> 1;
                }
            } else {
                skip = false;
            }

            if (t3 & 1) != 0 {
                break;
            }
        }

        if t3 >= 0 {
            u1 = t1;
            u3 = t3;
        } else {
            v1 = v - t1;
            v3 = -t3;
        }
        t1 = u1 - v1;
        t3 = u3 - v3;
        if t1 < 0 {
            t1 = t1 + v;
        }
        if t3 == 0 {
            break;
        }
    }
    u1
}

/* return (a^b) mod m */
fn pow_mod(a: i32, mut b: i32, m: i32) -> i32 {
    let mut r = 1;
    let mut aa = a;
    loop {
        if (b & 1) != 0 {
            r = mul_mod(r, aa, m);
        }
        b = b >> 1;
        if b == 0 {
            break;
        }
        aa = mul_mod(aa, aa, m);
    }
    r
}

/* return true if n is prime */
fn is_prime(n: i32) -> bool {
    if (n % 2) == 0 {
        return false;
    }

    let mut i = 3;
    loop {
        if i * i > n {
            return true;
        }
        if (n % i) == 0 {
            return false;
        }
        i += 2;
    }
}

/* return the prime number immediatly after n */
fn next_prime(mut n: i32) -> i32 {
    loop {
        n += 1;
        if is_prime(n) {
            return n;
        }
    }
}

macro_rules! divn {
    ($t:expr, $a:expr, $v:expr, $vinc:expr, $kq:expr, $kqinc:expr) => {
        $kq += $kqinc;
        if $kq >= $a {
            loop {
                $kq -= $a;
                if $kq < $a {
                    break;
                }
            }
            if $kq == 0 {
                loop {
                    $t = $t / $a;
                    $v += $vinc;
                    if ($t % $a) != 0 {
                        break;
                    }
                }
            }
        }
    };
}

fn calc_digits(n: i32) -> u64 {
    let nl = ((n + 20) as f64 * (10.0_f64).ln() / (13.5_f64).ln()) as i32;
    let mut sum = 0.0;
    let mut num;
    let mut t;
    let mut t1;
    let mut v;

    let mut a = 2;
    let l3n = (3.0 * nl as f64).ln();
    while a <= 3 * nl {
        let mut vmax = (l3n / (a as f64).ln()) as i32;
        if a == 2 {
            vmax = vmax + (nl - n);
            if vmax <= 0 {
                a = next_prime(a);
                continue;
            }
        }
        let mut av = 1;
        for _ in 0..vmax {
            av = av * a;
        }

        let mut s = 0;
        let mut den = 1;
        let mut kq1 = 0;
        let mut kq2 = -1;
        let mut kq3 = -3;
        let mut kq4 = -2;

        if a == 2 {
            num = 1;
            v = -n;
        } else {
            num = pow_mod(2, n, av);
            v = 0;
        }

        for k in 1..nl + 1 {
            t = 2 * k;
            divn!(t, a, v, -1, kq1, 2);
            num = mul_mod(num, t, av);

            t = 2 * k - 1;
            divn!(t, a, v, -1, kq2, 2);
            num = mul_mod(num, t, av);

            t = 3 * (3 * k - 1);
            divn!(t, a, v, 1, kq3, 9);
            den = mul_mod(den, t, av);

            t = 3 * k - 2;
            divn!(t, a, v, 1, kq4, 3);
            if a != 2 {
                t = t * 2;
            } else {
                v += 1;
            }
            den = mul_mod(den, t, av);

            if v > 0 {
                if a != 2 {
                    t = inv_mod2(den, av);
                } else {
                    t = inv_mod(den, av);
                }
                t = mul_mod(t, num, av);
                for _ in v..vmax {
                    t = mul_mod(t, a, av);
                }
                t1 = 25 * k - 3;
                t = mul_mod(t, t1, av);
                s += t;
                if s >= av {
                    s -= av;
                }
            }
        }
        t = pow_mod(5, n - 1, av);
        s = mul_mod(s, t, av);
        sum = (sum + s as f64 / av as f64).fract();
        a = next_prime(a);
    }
    (sum * 1e9) as u64
}

use rayon::prelude::*;
fn main() {
    let num_digits = std::env::args().skip(1).next().unwrap_or("800".to_string());
    let num_digits = (num_digits.parse::<u32>().unwrap_or(800) / 9) as i32;

    let pi: Vec<String> = (0..num_digits)
        .into_par_iter()
        .map(|n| format!("{:09}", calc_digits(9 * n + 1)))
        .collect();
    println!("3.{}", pi.join(""));
}
