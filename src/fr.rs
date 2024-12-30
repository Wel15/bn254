use core::convert::TryInto;
use core::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Neg};
use ff::{Field, PrimeField, FromUniformBytes, WithSmallOrderMulGroup};
use rand::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

// 如果启用了 asm 特性，使用特定的宏
#[cfg(feature = "asm")]
use crate::assembly::field_arithmetic_asm;

// 默认情况使用通用实现
#[cfg(not(feature = "asm"))]
use crate::{field_arithmetic, field_specific};

use crate::{
    field_bits, field_common, impl_add_binop_specify_output, impl_binops_additive,
    impl_binops_additive_specify_output, impl_binops_multiplicative,
    impl_binops_multiplicative_mixed, impl_sub_binop_specify_output, impl_sum_prod,
};

// `Fr` 类型的定义，代表 BN254 曲线标量场上的元素
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct Fr(pub(crate) [u64; 4]);

/// 常量定义
const MODULUS: Fr = Fr([
    0x43e1f593f0000001,
    0x2833e84879b97091,
    0xb85045b68181585d,
    0x30644e72e131a029,
]);

const MODULUS_STR: &str = "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";
const INV: u64 = 0xc2e1f593efffffff;
const R: Fr = Fr([
    0xac96341c4ffffffb,
    0x36fc76959f60cd29,
    0x666ea36f7879462e,
    0x0e0a77c19a07df2f,
]);
const R2: Fr = Fr([
    0x1bb8e645ae216da7,
    0x53fe3ab1e35c59e3,
    0x8c49833d53bb8085,
    0x0216d0b17f4e44a5,
]);
const GENERATOR: Fr = Fr::from_raw([0x07, 0x00, 0x00, 0x00]);
const S: u32 = 28;
const ROOT_OF_UNITY: Fr = Fr::from_raw([
    0xd34f1ed960c37c9c,
    0x3215cf6dd39329c8,
    0x98865ea93dd31f74,
    0x03ddb9f5166d18b7,
]);
const TWO_INV: Fr = Fr::from_raw([
    0xa1f0fac9f8000001,
    0x9419f4243cdcb848,
    0xdc2822db40c0ac2e,
    0x183227397098d014,
]);
const ROOT_OF_UNITY_INV: Fr = Fr::from_raw([
    0x0ed3e50a414e6dba,
    0xb22625f59115aba7,
    0x1bbe587180f34361,
    0x048127174daabc26,
]);
const DELTA: Fr = Fr::from_raw([
    0x870e56bbe533e9a2,
    0x5b5f898e5e963f25,
    0x64ec26aad4c86e71,
    0x09226b6e22c6f0ca,
]);

/// `Fr` 的实现
impl Fr {
    pub const fn from_raw(val: [u64; 4]) -> Self {
        Fr(val)
    }

    pub fn pow(&self, exp: [u64; 4]) -> Self {
        let mut res = Fr::ONE;
        for i in (0..4).rev() {
            for j in (0..64).rev() {
                res = res.square();
                if (exp[i] >> j) & 1 == 1 {
                    res *= self;
                }
            }
        }
        res
    }
}

/// 运算符实现
impl<'a> Add<&'a Fr> for Fr {
    type Output = Self;

    fn add(self, rhs: &'a Self) -> Self::Output {
        let mut result = self;
        result += rhs;
        result
    }
}

impl<'a> Add<&'a Fr> for &'a Fr {
    type Output = Fr;

    fn add(self, rhs: &'a Fr) -> Fr {
        let mut result = (*self).clone();
        result += rhs;
        result
    }
}

impl<'a> AddAssign<&'a Fr> for Fr {
    fn add_assign(&mut self, rhs: &'a Self) {
        for i in 0..4 {
            self.0[i] = self.0[i].wrapping_add(rhs.0[i]);
        }
    }
}

impl Add for Fr {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut result = self;
        result += &rhs;
        result
    }
}

impl AddAssign for Fr {
    fn add_assign(&mut self, rhs: Self) {
        *self += &rhs;
    }
}

impl<'a> Sub<&'a Fr> for Fr {
    type Output = Self;

    fn sub(self, rhs: &'a Self) -> Self::Output {
        let mut result = self;
        result -= rhs;
        result
    }
}

impl<'a> Sub<&'a Fr> for &'a Fr {
    type Output = Fr;

    fn sub(self, rhs: &'a Fr) -> Fr {
        let mut result = (*self).clone();
        result -= rhs;
        result
    }
}

impl<'a> SubAssign<&'a Fr> for Fr {
    fn sub_assign(&mut self, rhs: &'a Self) {
        for i in 0..4 {
            self.0[i] = self.0[i].wrapping_sub(rhs.0[i]);
        }
    }
}

impl Sub for Fr {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut result = self;
        result -= &rhs;
        result
    }
}

impl SubAssign for Fr {
    fn sub_assign(&mut self, rhs: Self) {
        *self -= &rhs;
    }
}

impl<'a> Mul<&'a Fr> for Fr {
    type Output = Self;

    fn mul(self, rhs: &'a Self) -> Self::Output {
        let mut result = self;
        result *= rhs;
        result
    }
}

impl<'a> Mul<&'a Fr> for &'a Fr {
    type Output = Fr;

    fn mul(self, rhs: &'a Fr) -> Fr {
        let mut result = (*self).clone();
        result *= rhs;
        result
    }
}

impl<'a> MulAssign<&'a Fr> for Fr {
    fn mul_assign(&mut self, rhs: &'a Self) {
        for i in 0..4 {
            self.0[i] = self.0[i].wrapping_mul(rhs.0[i]);
        }
    }
}

impl Mul for Fr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut result = self;
        result *= &rhs;
        result
    }
}

impl MulAssign for Fr {
    fn mul_assign(&mut self, rhs: Self) {
        *self *= &rhs;
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

/// `Field` 和 `PrimeField` 的实现
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
        CtOption::new(tmp, Choice::from(1)) // 简化校验
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