#![feature(test)]

#[cfg(test)]
extern crate test;

mod u256;
pub use self::u256::U256;


macro_rules! define_unsigned {
    ($name:tt, $bits:tt) => {
        #[allow(non_camel_case_types)]
        #[derive(Clone, PartialEq, Eq)]
        pub struct $name(u128);

        impl $name {
            pub const BITS: usize  = $bits;
            pub const BYTES: usize = $bits / 8;

            pub const MAX: Self    = Self((1u128 << Self::BITS) - 1); // 2^$bits - 1

            pub const ZERO: Self   = Self(0u128);
            pub const ONE: Self    = Self(1u128);
            

            pub const fn wrapping_add(&self, rhs: Self) -> Self {
                Self((self.0 + rhs.0) & Self::MAX.0)
            }

            pub fn wrapping_add_small(&self, other: u64) -> Self {
                self.wrapping_add(Self(other as u128))
            }

            pub fn to_le_bytes(self) -> [u8; Self::BYTES] {
                let mut bytes = [0u8; Self::BYTES];
                bytes.copy_from_slice(&self.0.to_le_bytes()[0..Self::BYTES]);
                bytes
            }

            pub fn increase(&mut self) {
                *self = self.wrapping_add(Self::ONE);
            }
        }

        impl From<u64> for $name {
            fn from(value: u64) -> Self {
                Self(value as u128)
            }
        }

        impl core::fmt::Debug for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                core::fmt::Debug::fmt(&self.0, f)
            }
        }
        impl core::fmt::Display for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                core::fmt::Display::fmt(&self.0, f)
            }
        }
    }
}

define_unsigned!( u88,  88);
define_unsigned!( u96,  96);
define_unsigned!(u104, 104);
define_unsigned!(u112, 112);
define_unsigned!(u120, 120);


impl core::fmt::Binary for u96 {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        if f.alternate() {
            write!(f, "0b{:096b}", self.0)
        } else {
            write!(f, "{:096b}", self.0)
        }
    }
}

/// The 192-bits unsigned integer type.
#[allow(non_camel_case_types)]
#[derive(Clone, PartialEq, Eq)]
pub struct u192 {
    lo: u128,
    hi: u64,
}

impl u192 {
    pub const BITS: usize  = 192;
    pub const BYTES: usize =  24;

    pub const MAX: Self    = Self { lo: u128::MAX, hi: u64::MAX }; // 2^192 - 1

    pub const ZERO: Self   = Self { lo: 0u128, hi: 0u64 };
    pub const ONE: Self    = Self { lo: 1u128, hi: 0u64 };


    pub fn to_le_bytes(self) -> [u8; Self::BYTES] {
        let mut bytes = [0u8; Self::BYTES];
        bytes[ 0..16].copy_from_slice(&self.lo.to_le_bytes());
        bytes[16..24].copy_from_slice(&self.hi.to_le_bytes());
        bytes
    }

    pub fn wrapping_add_small(&self, other: u64) -> Self {
        let mut out = Self::ZERO;

        let (res1, overflow) = self.lo.overflowing_add(other as u128);
        out.lo = res1;

        if overflow {
            let (res2, overflow) = self.hi.overflowing_add(res1 as u64 + 1);
            
            if overflow {
                out.hi = 0;
                out.lo = res2 as u128;
            } else {
                out.hi = res2;
            }
        } else {
            out.hi = self.hi;
        }

        out
    }

    pub fn increase(&mut self) {
        let res = self.wrapping_add_small(1u64);
        self.lo = res.lo;
        self.hi = res.hi;
    }
}

impl core::fmt::Debug for u192 {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let bytes = self.clone().to_le_bytes();

        let a = u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], 
            bytes[4], bytes[5], bytes[6], bytes[7], 
        ]);

        let b = u64::from_le_bytes([
            bytes[ 8], bytes[ 9], bytes[10], bytes[11], 
            bytes[12], bytes[13], bytes[14], bytes[15], 
        ]);

        let c = u64::from_le_bytes([
            bytes[16], bytes[17], bytes[18], bytes[19], 
            bytes[20], bytes[21], bytes[22], bytes[23], 
        ]);

        let d = 0u64;

        let n = U256([a, b, c, d]);

        core::fmt::Debug::fmt(&n, f)
    }
}
impl core::fmt::Display for u192 {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self, f)
    }
}

impl From<u64> for u192 {
    fn from(value: u64) -> Self {
        Self { lo: value as u128, hi: 0 }
    }
}


#[test]
fn test_uint_wrapping_add_small() {
    // FMT
    assert_eq!(u192::MAX.to_string().as_str(), 
        "6277101735386680763835789423207666416102355444464034512895");
    assert_eq!(u120::MAX.to_string().as_str(), 
        "1329227995784915872903807060280344575");
    assert_eq!(u112::MAX.to_string().as_str(), 
        "5192296858534827628530496329220095");
    assert_eq!(u104::MAX.to_string().as_str(), 
        "20282409603651670423947251286015");
    assert_eq!(u96::MAX.to_string().as_str(), 
        "79228162514264337593543950335");
    assert_eq!(u88::MAX.to_string().as_str(), 
        "309485009821345068724781055");

    macro_rules! test_uint {
        ($name:tt) => {
            // wrapping_add u64
            {
                let a = $name::MAX;
                let b = $name::MAX.wrapping_add_small(0u64);
                assert_eq!(a, b);
            }
            {
                let a = $name::from(0u64);
                let b = $name::MAX.wrapping_add_small(1u64);
                assert_eq!(a, b);
            }
            {
                let a = $name::from(1u64);
                let b = $name::MAX.wrapping_add_small(2u64);
                assert_eq!(a, b);
            }
            {
                let a = $name::from(2u64);
                let b = $name::MAX.wrapping_add_small(3u64);
                assert_eq!(a, b);
            }
            {
                let a = $name::from(18446744073709551614u64);
                let b = $name::MAX.wrapping_add_small(u64::MAX);
                assert_eq!(a, b);
            }
        }
    }

    test_uint!(u88);
    test_uint!(u96);
    test_uint!(u104);
    test_uint!(u112);
    test_uint!(u120);

    test_uint!(u192);
}


#[bench]
fn bench_u192(b: &mut test::Bencher) {
    b.iter(|| {
        let mut zero = test::black_box(u192::from(u64::MAX));
        zero.increase()
    })
}

#[bench]
fn bench_u192_with_u64(b: &mut test::Bencher) {
    b.iter(|| {
        let zero = test::black_box(U256::from(u64::MAX));
        zero.wrapping_add_small(1)
    })
}


fn main() {
    println!("  {:b}", u96::ONE);
    println!("{:#b}", u96::ONE);

    println!("  {:b}", u96::MAX);
    println!("{:#b}", u96::MAX);

    println!("u192 max: {:?}", u192::MAX);
    println!("u192 max +0: {:?}", u192::MAX.wrapping_add_small(0));
    println!("u192 max +1: {:?}", u192::MAX.wrapping_add_small(1));
    println!("u192 max +2: {:?}", u192::MAX.wrapping_add_small(2));
    println!("u192 max +3: {:?}", u192::MAX.wrapping_add_small(3));
}