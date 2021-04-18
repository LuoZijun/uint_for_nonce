/// Little-endian large integer type
/// 256-bit unsigned integer.
#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(C)]
pub struct U256(pub [u64; 4]);


impl core::convert::From<u64> for U256 {
    fn from(value: u64) -> U256 {
        let mut ret = [0; 4];
        ret[0] = value;
        U256(ret)
    }
}

impl From<u32> for U256 {
    fn from(value: u32) -> U256 {
        From::from(value as u64)
    }
}

impl U256 {
    const WORD_BITS: usize = 64;
    
    /// Maximum value.
    pub const MAX: U256 = U256([u64::max_value(); 4]);

    /// Zero (additive identity) of this type.
    #[inline]
    pub const fn zero() -> Self {
        Self([0; 4])
    }

    /// One (multiplicative identity) of this type.
    #[inline]
    pub fn one() -> Self {
        From::from(1u64)
    }

    /// Conversion to u32
    #[inline]
    pub const fn low_u32(&self) -> u32 {
        let &U256(ref arr) = self;
        arr[0] as u32
    }

    /// Low word (u64)
    #[inline]
    pub const fn low_u64(&self) -> u64 {
        let &U256(ref arr) = self;
        arr[0]
    }

    /// Conversion to usize with overflow checking
    ///
    /// # Panics
    ///
    /// Panics if the number is larger than usize::max_value().
    #[inline]
    pub fn as_usize(&self) -> usize {
        let &U256(ref arr) = self;
        if !self.fits_word() || arr[0] > usize::max_value() as u64 {
            panic!("Integer overflow when casting to usize");
        }
        arr[0] as usize
    }

    /// Whether this is zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        let &U256(ref arr) = self;
        for i in 0..4 {
            if arr[i] != 0 {
                return false;
            }
        }
        return true;
    }

    fn words(bits: usize) -> usize {
        debug_assert!(bits > 0);
        1 + (bits - 1) / Self::WORD_BITS
    }

    /// Return the least number of bits needed to represent the number
    #[inline]
    pub fn bits(&self) -> usize {
        let &U256(ref arr) = self;
        for i in 1..4 {
            if arr[4 - i] > 0 {
                return (0x40 * (4 - i + 1)) - arr[4 - i].leading_zeros() as usize;
            }
        }
        0x40 - arr[0].leading_zeros() as usize
    }

    #[inline]
    fn fits_word(&self) -> bool {
        let &U256(ref arr) = self;
        for i in 1..4 {
            if arr[i] != 0 {
                return false;
            }
        }
        return true;
    }

    #[inline(always)]
    fn sub_slice(a: &mut [u64], b: &[u64]) -> bool {
        Self::binop_slice(a, b, u64::overflowing_sub)
    }

    #[inline(always)]
    fn add_slice(a: &mut [u64], b: &[u64]) -> bool {
        Self::binop_slice(a, b, u64::overflowing_add)
    }

    #[inline(always)]
    fn binop_slice(
        a: &mut [u64],
        b: &[u64],
        binop: impl Fn(u64, u64) -> (u64, bool) + Copy,
    ) -> bool {
        let mut c = false;
        a.iter_mut().zip(b.iter()).for_each(|(x, y)| {
            let (res, carry) = Self::binop_carry(*x, *y, c, binop);
            *x = res;
            c = carry;
        });
        c
    }

    #[inline(always)]
    fn binop_carry(
        a: u64,
        b: u64,
        c: bool,
        binop: impl Fn(u64, u64) -> (u64, bool),
    ) -> (u64, bool) {
        let (res1, overflow1) = b.overflowing_add(u64::from(c));
        let (res2, overflow2) = binop(a, res1);
        (res2, overflow1 || overflow2)
    }

    #[inline(always)]
    const fn mul_u64(a: u64, b: u64, carry: u64) -> (u64, u64) {
        let (hi, lo) = Self::split_u128(a as u128 * b as u128 + carry as u128);
        (lo, hi)
    }

    #[inline(always)]
    const fn split(a: u64) -> (u64, u64) {
        (a >> 32, a & 0xFFFF_FFFF)
    }

    #[inline(always)]
    const fn split_u128(a: u128) -> (u64, u64) {
        ((a >> 64) as _, (a & 0xFFFFFFFFFFFFFFFF) as _)
    }

    /// Overflowing multiplication by u64.
    /// Returns the result and carry.
    fn overflowing_mul_u64(mut self, other: u64) -> (Self, u64) {
        let mut carry = 0u64;
        for d in self.0.iter_mut() {
            let (res, c) = Self::mul_u64(*d, other, carry);
            *d = res;
            carry = c;
        }
        (self, carry)
    }

    fn full_mul_u64(self, by: u64) -> [u64; 4 + 1] {
        let (prod, carry) = self.overflowing_mul_u64(by);
        let mut res = [0u64; 4 + 1];
        res[..4].copy_from_slice(&prod.0[..]);
        res[4] = carry;
        res
    }

    fn full_shl(self, shift: u32) -> [u64; 4 + 1] {
        debug_assert!(shift < Self::WORD_BITS as u32);

        let mut u = [0u64; 4 + 1];
        let u_lo = self.0[0] << shift;
        let u_hi = self >> (Self::WORD_BITS as u32 - shift);
        u[0] = u_lo;
        u[1..].copy_from_slice(&u_hi.0[..]);
        u
    }

    fn full_shr(u: [u64; 4 + 1], shift: u32) -> Self {
        debug_assert!(shift < Self::WORD_BITS as u32);

        let mut res = Self::zero();
        for i in 0..4 {
            res.0[i] = u[i] >> shift;
        }
        if shift > 0 {
            for i in 1..=4 {
                res.0[i - 1] |= u[i] << (Self::WORD_BITS as u32 - shift);
            }
        }
        res
    }

    fn div_mod_small(mut self, other: u64) -> (Self, Self) {
        let mut rem = 0u64;
        self.0.iter_mut().rev().for_each(|d| {
            let (q, r) = Self::div_mod_word(rem, *d, other);
            *d = q;
            rem = r;
        });
        (self, rem.into())
    }

    fn div_mod_knuth(self, mut v: Self, n: usize, m: usize) -> (Self, Self) {
        debug_assert!(self.bits() >= v.bits() && !v.fits_word());
        debug_assert!(n + m <= 4);

        let shift = v.0[n - 1].leading_zeros();
        v <<= shift;
        let mut u = self.full_shl(shift);
        let mut q = Self::zero();
        let v_n_1 = v.0[n - 1];
        let v_n_2 = v.0[n - 2];
        for j in (0..=m).rev() {
            let u_jn = u[j + n];
            let mut q_hat = if u_jn < v_n_1 {
                let (mut q_hat, mut r_hat) = Self::div_mod_word(u_jn, u[j + n - 1], v_n_1);
                loop {
                    let (hi, lo) = Self::split_u128(u128::from(q_hat) * u128::from(v_n_2));
                    if (hi, lo) <= (r_hat, u[j + n - 2]) {
                        break;
                    }
                    q_hat -= 1;
                    let (new_r_hat, overflow) = r_hat.overflowing_add(v_n_1);
                    r_hat = new_r_hat;
                    if overflow {
                        break;
                    }
                }
                q_hat
            } else {
                u64::max_value()
            };
            let q_hat_v = v.full_mul_u64(q_hat);
            let c = Self::sub_slice(&mut u[j..], &q_hat_v[..n + 1]);
            if c {
                q_hat -= 1;
                let c = Self::add_slice(&mut u[j..], &v.0[..n]);
                u[j + n] = u[j + n].wrapping_add(u64::from(c));
            }
            q.0[j] = q_hat;
        }
        let remainder = Self::full_shr(u, shift);
        (q, remainder)
    }

    #[inline(always)]
    fn div_mod_word(hi: u64, lo: u64, y: u64) -> (u64, u64) {
        debug_assert!(hi < y);

        const TWO32: u64 = 1 << 32;
        let s = y.leading_zeros();
        let y = y << s;
        let (yn1, yn0) = Self::split(y);
        let un32 = (hi << s) | lo.checked_shr(64 - s).unwrap_or(0);
        let un10 = lo << s;
        let (un1, un0) = Self::split(un10);
        let mut q1 = un32 / yn1;
        let mut rhat = un32 - q1 * yn1;
        while q1 >= TWO32 || q1 * yn0 > TWO32 * rhat + un1 {
            q1 -= 1;
            rhat += yn1;
            if rhat >= TWO32 {
                break;
            }
        }
        let un21 = un32
            .wrapping_mul(TWO32)
            .wrapping_add(un1)
            .wrapping_sub(q1.wrapping_mul(y));
        let mut q0 = un21 / yn1;
        rhat = un21.wrapping_sub(q0.wrapping_mul(yn1));
        while q0 >= TWO32 || q0 * yn0 > TWO32 * rhat + un0 {
            q0 -= 1;
            rhat += yn1;
            if rhat >= TWO32 {
                break;
            }
        }
        let rem = un21
            .wrapping_mul(TWO32)
            .wrapping_add(un0)
            .wrapping_sub(y.wrapping_mul(q0));
        (q1 * TWO32 + q0, rem >> s)
    }

    /// Returns a pair `(self / other, self % other)`.
    ///
    /// # Panics
    ///
    /// Panics if `other` is zero.
    pub fn div_mod(self, other: Self) -> (Self, Self) {
        let my_bits = self.bits();
        let your_bits = other.bits();

        assert!(your_bits != 0, "division by zero");

        if my_bits < your_bits {
            return (Self::zero(), self);
        }

        if your_bits <= Self::WORD_BITS {
            return self.div_mod_small(other.low_u64());
        }

        let (n, m) = {
            let my_words = Self::words(my_bits);
            let your_words = Self::words(your_bits);
            (your_words, my_words - your_words)
        };

        self.div_mod_knuth(other, n, m)
    }

    #[inline(always)]
    pub fn overflowing_add_small(self, other: u64) -> (U256, bool) {
        let me = &self.0;
        let mut dst = [0u64; 4];

        let (res1, overflow) = me[0].overflowing_add(other);
        dst[0] = res1;

        if overflow {
            let (res2, overflow) = me[1].overflowing_add(res1 + 1);
            dst[1] = res2;

            if overflow {
                let (res3, overflow) = me[2].overflowing_add(res2 + 1);
                dst[2] = res3;

                if overflow {
                    let (res4, overflow) = me[3].overflowing_add(res3 + 1);
                    dst[3] = res4;

                    if overflow {
                        return (U256([res4, 0, 0, 0]), true);
                    }
                } else {
                    dst[3] = me[3];
                }
            } else {
                dst[2] = me[2];
                dst[3] = me[3];
            }
        } else {
            dst[1] = me[1];
            dst[2] = me[2];
            dst[3] = me[3];
        }

        (U256(dst), false)
    }

    /// Add with overflow.
    #[inline(always)]
    pub fn overflowing_add(self, other: U256) -> (U256, bool) {
        let U256(ref me) = self;
        let U256(ref you) = other;

        let mut ret = [0u64; 4];
        let ret_ptr = &mut ret as *mut [u64; 4] as *mut u64;
        let mut carry = 0u64;

        {
            #[allow(non_upper_case_globals)]
            const i: usize = 0;

            if carry != 0 {
                let (res1, overflow1) = (u64::overflowing_add)(me[i], you[i]);
                let (res2, overflow2) = (u64::overflowing_add)(res1, carry);
                unsafe { *ret_ptr.offset(i as _) = res2 }
                carry = (overflow1 as u8 + overflow2 as u8) as u64;
            } else {
                let (res, overflow) = (u64::overflowing_add)(me[i], you[i]);
                unsafe { *ret_ptr.offset(i as _) = res }
                carry = overflow as u64;
            }
        }

        {
            #[allow(non_upper_case_globals)]
            const i: usize = 1;

            if carry != 0 {
                let (res1, overflow1) = (u64::overflowing_add)(me[i], you[i]);
                let (res2, overflow2) = (u64::overflowing_add)(res1, carry);
                unsafe { *ret_ptr.offset(i as _) = res2 }
                carry = (overflow1 as u8 + overflow2 as u8) as u64;
            } else {
                let (res, overflow) = (u64::overflowing_add)(me[i], you[i]);
                unsafe { *ret_ptr.offset(i as _) = res }
                carry = overflow as u64;
            }
        }

        {
            #[allow(non_upper_case_globals)]
            const i: usize = 2;

            if carry != 0 {
                let (res1, overflow1) = (u64::overflowing_add)(me[i], you[i]);
                let (res2, overflow2) = (u64::overflowing_add)(res1, carry);
                unsafe { *ret_ptr.offset(i as _) = res2 }
                carry = (overflow1 as u8 + overflow2 as u8) as u64;
            } else {
                let (res, overflow) = (u64::overflowing_add)(me[i], you[i]);
                unsafe { *ret_ptr.offset(i as _) = res }
                carry = overflow as u64;
            }
        }

        {
            #[allow(non_upper_case_globals)]
            const i: usize = 3;

            if carry != 0 {
                let (res1, overflow1) = (u64::overflowing_add)(me[i], you[i]);
                let (res2, overflow2) = (u64::overflowing_add)(res1, carry);
                unsafe { *ret_ptr.offset(i as _) = res2 }
                carry = (overflow1 as u8 + overflow2 as u8) as u64;
            } else {
                let (res, overflow) = (u64::overflowing_add)(me[i], you[i]);
                unsafe { *ret_ptr.offset(i as _) = res }
                carry = overflow as u64;
            }
        }

        (U256(ret), carry > 0)
    }

    pub fn wrapping_add_small(self, other: u64) -> U256 {
        let (result, _overflow) = self.overflowing_add_small(other);
        result
    }

    pub fn wrapping_add(self, other: U256) -> U256 {
        let (result, _overflow) = self.overflowing_add(other);
        result
    }
}


impl core::ops::Add<u64> for U256 {
    type Output = U256;
    
    fn add(self, other: u64) -> U256 {
        let (result, overflow) = self.overflowing_add_small(other);
        if overflow {
            panic!("arithmetic operation overflow");
        }
        result
    }
}
impl core::ops::Add<U256> for U256 {
    type Output = U256;
    
    fn add(self, other: U256) -> U256 {
        let (result, overflow) = self.overflowing_add(other);
        if overflow {
            panic!("arithmetic operation overflow");
        }
        result
    }
}

impl core::ops::Div<u64> for U256 {
    type Output = U256;

    fn div(self, other: u64) -> U256 {
        self.div_mod_small(other).0
    }
}

impl core::ops::Div<U256> for U256 {
    type Output = U256;

    fn div(self, other: Self) -> U256 {
        self.div_mod(other).0
    }
}

impl core::ops::Rem<u64> for U256 {
    type Output = U256;

    fn rem(self, other: u64) -> U256 {
        let mut sub_copy = self;
        sub_copy %= other;
        sub_copy
    }
}

impl core::ops::Rem<U256> for U256 {
    type Output = U256;

    fn rem(self, other: Self) -> U256 {
        let mut sub_copy = self;
        sub_copy %= other;
        sub_copy
    }
}

impl core::ops::RemAssign<u64> for U256 {
    fn rem_assign(&mut self, other: u64) {
        let rem = self.div_mod_small(other).1;
        *self = rem;
    }
}

impl core::ops::RemAssign<U256> for U256 {
    fn rem_assign(&mut self, other: Self) {
        let rem = self.div_mod(other).1;
        *self = rem;
    }
}
impl<T> core::ops::Shl<T> for U256
where
    T: Into<U256>,
{
    type Output = U256;

    fn shl(self, shift: T) -> U256 {
        let shift = shift.into().as_usize();
        let U256(ref original) = self;
        let mut ret = [0u64; 4];
        let word_shift = shift / 64;
        let bit_shift = shift % 64;
        for i in word_shift..4 {
            ret[i] = original[i - word_shift] << bit_shift;
        }
        if bit_shift > 0 {
            for i in word_shift + 1..4 {
                ret[i] += original[i - 1 - word_shift] >> (64 - bit_shift);
            }
        }
        U256(ret)
    }
}
impl<T> core::ops::ShlAssign<T> for U256
where
    T: Into<U256>,
{
    fn shl_assign(&mut self, shift: T) {
        *self = *self << shift;
    }
}

impl<T> core::ops::Shr<T> for U256
where
    T: Into<U256>,
{
    type Output = U256;
    fn shr(self, shift: T) -> U256 {
        let shift = shift.into().as_usize();
        let U256(ref original) = self;
        let mut ret = [0u64; 4];
        let word_shift = shift / 64;
        let bit_shift = shift % 64;
        for i in word_shift..4 {
            ret[i - word_shift] = original[i] >> bit_shift;
        }
        if bit_shift > 0 {
            for i in word_shift + 1..4 {
                ret[i - word_shift - 1] += original[i] << (64 - bit_shift);
            }
        }
        U256(ret)
    }
}
impl<T> core::ops::ShrAssign<T> for U256
where
    T: Into<U256>,
{
    fn shr_assign(&mut self, shift: T) {
        *self = *self >> shift;
    }
}


impl core::fmt::Debug for U256 {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Display::fmt(&self, f)
    }
}

impl core::fmt::Display for U256 {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        if self.is_zero() {
            return write!(f, "0");
        }

        let mut buf = [0_u8; 4 * 20];
        let mut i = buf.len() - 1;
        let mut current = *self;
        let ten = 10u64;

        loop {
            let digit = (current % ten).low_u64() as u8;
            buf[i] = digit + b'0';
            current = current / ten;
            if current.is_zero() {
                break;
            }
            i -= 1;
        }
        let s = unsafe { core::str::from_utf8_unchecked(&buf[i..]) };
        f.write_str(s)
    }
}

impl core::fmt::LowerHex for U256 {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let &U256(ref data) = self;
        
        if f.alternate() {
            write!(f, "0x")?;
        }

        if self.is_zero() {
            return write!(f, "0");
        }

        let mut latch = false;
        for ch in data.iter().rev() {
            for x in 0..16 {
                let nibble = (ch & (15u64 << ((15 - x) * 4) as u64)) >> (((15 - x) * 4) as u64);
                if !latch {
                    latch = nibble != 0;
                }
                if latch {
                    write!(f, "{:x}", &nibble)?;
                }
            }
        }

        Ok(())
    }
}

#[test]
fn test_u256_wrapping_add_small() {
    // FMT
    assert_eq!(U256::MAX.to_string().as_str(), 
        "115792089237316195423570985008687907853269984665640564039457584007913129639935");

    // wrapping_add u64
    {
        let a = U256::MAX;
        let b = U256::MAX.wrapping_add_small(0u64);
        assert_eq!(a, b);
    }
    {
        let a = U256::from(0u64);
        let b = U256::MAX.wrapping_add_small(1u64);
        assert_eq!(a, b);
    }
    {
        let a = U256::from(1u64);
        let b = U256::MAX.wrapping_add_small(2u64);
        assert_eq!(a, b);
    }
    {
        let a = U256::from(2u64);
        let b = U256::MAX.wrapping_add_small(3u64);
        assert_eq!(a, b);
    }
    {
        let a = U256::from(18446744073709551614u64);
        let b = U256::MAX.wrapping_add_small(u64::MAX);
        assert_eq!(a, b);
    }
}
