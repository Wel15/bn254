#[cfg(feature = "asm")]
use crate::assembly::field_arithmetic_asm;
#[cfg(not(feature = "asm"))]
use crate::{field_arithmetic, field_specific};

use crate::arithmetic::{adc, mac, sbb};
use crate::{
    field_bits, field_common, impl_add_binop_specify_output, impl_binops_additive,
    impl_binops_additive_specify_output, impl_binops_multiplicative,
    impl_binops_multiplicative_mixed, impl_sub_binop_specify_output, impl_sum_prod,
};
use core::convert::TryInto;
use core::fmt;
use core::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Neg};
use ff::{Field, PrimeField, FromUniformBytes, WithSmallOrderMulGroup};
use rand::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[cfg(feature = "derive_serde")]
use serde::{Deserialize, Serialize};

/// This represents an element of $\mathbb{F}_r$ where
///
/// `r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001`
///
/// is the scalar field of the BN254 curve.
// The internal representation of this type is four 64-bit unsigned
// integers in little-endian order. `Fr` values are always in
// Montgomery form; i.e., Fr(a) = aR mod r, with R = 2^256.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
#[cfg_attr(feature = "derive_serde", derive(Serialize, Deserialize))]
pub struct Fr(pub(crate) [u64; 4]);

/// Constant representing the modulus
/// r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
const MODULUS: Fr = Fr([
    0x43e1f593f0000001,
    0x2833e84879b97091,
    0xb85045b68181585d,
    0x30644e72e131a029,
]);

/// The modulus as u32 limbs.
#[cfg(not(target_pointer_width = "64"))]
const MODULUS_LIMBS_32: [u32; 8] = [
    0xf000_0001,
    0x43e1_f593,
    0x79b9_7091,
    0x2833_e848,
    0x8181_585d,
    0xb850_45b6,
    0xe131_a029,
    0x3064_4e72,
];

const MODULUS_STR: &str = "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";

/// INV = -(r^{-1} mod 2^64) mod 2^64
const INV: u64 = 0xc2e1f593efffffff;

/// `R = 2^256 mod r`
const R: Fr = Fr([
    0xac96341c4ffffffb,
    0x36fc76959f60cd29,
    0x666ea36f7879462e,
    0x0e0a77c19a07df2f,
]);

/// `R^2 = 2^512 mod r`
const R2: Fr = Fr([
    0x1bb8e645ae216da7,
    0x53fe3ab1e35c59e3,
    0x8c49833d53bb8085,
    0x0216d0b17f4e44a5,
]);

/// `R^3 = 2^768 mod r`
const R3: Fr = Fr([
    0x5e94d8e1b4bf0040,
    0x2a489cbe1cfbb6b8,
    0x893cc664a19fcfed,
    0x0cf8594b7fcc657c,
]);

/// `GENERATOR = 7 mod r`
const GENERATOR: Fr = Fr::from_raw([0x07, 0x00, 0x00, 0x00]);

const S: u32 = 28;

/// GENERATOR^t where t * 2^s + 1 = r
const ROOT_OF_UNITY: Fr = Fr::from_raw([
    0xd34f1ed960c37c9c,
    0x3215cf6dd39329c8,
    0x98865ea93dd31f74,
    0x03ddb9f5166d18b7,
]);

/// 1 / 2 mod r
const TWO_INV: Fr = Fr::from_raw([
    0xa1f0fac9f8000001,
    0x9419f4243cdcb848,
    0xdc2822db40c0ac2e,
    0x183227397098d014,
]);

/// 1 / ROOT_OF_UNITY mod r
const ROOT_OF_UNITY_INV: Fr = Fr::from_raw([
    0x0ed3e50a414e6dba,
    0xb22625f59115aba7,
    0x1bbe587180f34361,
    0x048127174daabc26,
]);

/// GENERATOR^{2^s} where t * 2^s + 1 = r with t odd.
const DELTA: Fr = Fr::from_raw([
    0x870e56bbe533e9a2,
    0x5b5f898e5e963f25,
    0x64ec26aad4c86e71,
    0x09226b6e22c6f0ca,
]);

/// `ZETA^3 = 1 mod r` where `ZETA^2 != 1 mod r`
const ZETA: Fr = Fr::from_raw([
    0x8b17ea66b99c90dd,
    0x5bfc41088d8daaa7,
    0xb3c4d79d41a91758,
    0x00,
]);

impl_binops_additive!(Fr, Fr);
impl_binops_multiplicative!(Fr, Fr);
field_common!(
    Fr,
    MODULUS,
    INV,
    MODULUS_STR,
    TWO_INV,
    ROOT_OF_UNITY_INV,
    DELTA,
    ZETA,
    R,
    R2,
    R3
);
impl_sum_prod!(Fr);

#[cfg(not(feature = "asm"))]
field_arithmetic!(Fr, MODULUS, INV, sparse);
#[cfg(feature = "asm")]
field_arithmetic_asm!(Fr, MODULUS, INV);

#[cfg(target_pointer_width = "64")]
field_bits!(Fr, MODULUS);
#[cfg(not(target_pointer_width = "64"))]
field_bits!(Fr, MODULUS, MODULUS_LIMBS_32);

/// Implementation of the `Fr` type.
impl Fr {
    pub const fn from_raw(val: [u64; 4]) -> Self {
        Fr(val)
    }

    pub const fn size() -> usize {
        32
    }
}

/// Implement arithmetic traits for `Fr`
impl Add for Fr {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut result = self;
        for i in 0..4 {
            result.0[i] = result.0[i].wrapping_add(rhs.0[i]);
        }
        result
    }
}

impl AddAssign for Fr {
    fn add_assign(&mut self, rhs: Self) {
        for i in 0..4 {
            self.0[i] = self.0[i].wrapping_add(rhs.0[i]);
        }
    }
}

impl Sub for Fr {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut result = self;
        for i in 0..4 {
            result.0[i] = result.0[i].wrapping_sub(rhs.0[i]);
        }
        result
    }
}

impl SubAssign for Fr {
    fn sub_assign(&mut self, rhs: Self) {
        for i in 0..4 {
            self.0[i] = self.0[i].wrapping_sub(rhs.0[i]);
        }
    }
}

impl Mul for Fr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut result = self;
        for i in 0..4 {
            result.0[i] = result.0[i].wrapping_mul(rhs.0[i]);
        }
        result
    }
}

impl MulAssign for Fr {
    fn mul_assign(&mut self, rhs: Self) {
        for i in 0..4 {
            self.0[i] = self.0[i].wrapping_mul(rhs.0[i]);
        }
    }
}

impl Neg for Fr {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let mut result = Fr([0; 4]);
        for i in 0..4 {
            result.0[i] = self.0[i].wrapping_neg();
        }
        result
    }
}

impl From<u64> for Fr {
    fn from(val: u64) -> Self {
        Fr([val, 0, 0, 0]) * R2 // 转换到 Montgomery 表示
    }
}

impl Field for Fr {
    const ZERO: Self = Self([0, 0, 0, 0]);
    const ONE: Self = R;

    fn random(mut rng: impl RngCore) -> Self {
        let mut buf = [0u64; 4];
        for i in 0..4 {
            buf[i] = rng.next_u64();
        }
        Fr(buf)
    }

    fn square(&self) -> Self {
        *self * *self
    }

    fn double(&self) -> Self {
        *self + *self
    }

    fn invert(&self) -> CtOption<Self> {
        let tmp = self.pow([
            0x43e1f593efffffff,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ]);

        CtOption::new(tmp, !self.ct_eq(&Self::ZERO))
    }

    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        ff::helpers::sqrt_ratio_generic(num, div)
    }
}

impl PrimeField for Fr {
    type Repr = [u8; 32];

    const NUM_BITS: u32 = 254;
    const CAPACITY: u32 = 253;
    const MODULUS: &'static str = MODULUS_STR;
    const MULTIPLICATIVE_GENERATOR: Self = GENERATOR;
    const ROOT_OF_UNITY: Self = ROOT_OF_UNITY;
    const ROOT_OF_UNITY_INV: Self = ROOT_OF_UNITY_INV;
    const TWO_INV: Self = TWO_INV;
    const DELTA: Self = DELTA;
    const S: u32 = S;

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let mut tmp = Fr([0; 4]);
        for i in 0..4 {
            tmp.0[i] = u64::from_le_bytes(repr[i * 8..(i + 1) * 8].try_into().unwrap());
        }
        CtOption::new(tmp, Choice::from(1)) // 校验简化
    }

    fn to_repr(&self) -> Self::Repr {
        let mut res = [0u8; 32];
        for i in 0..4 {
            res[i * 8..(i + 1) * 8].copy_from_slice(&self.0[i].to_le_bytes());
        }
        res
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr()[0] & 1)
    }
}