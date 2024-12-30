use core::convert::TryInto;
use core::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Neg};
use ff::{Field, PrimeField};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

// `Fr` 类型定义
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct Fr(pub(crate) [u64; 4]);

// 常量定义
const MODULUS: Fr = Fr([
    0x43e1f593f0000001,
    0x2833e84879b97091,
    0xb85045b68181585d,
    0x30644e72e131a029,
]);

const INV: u64 = 0xc2e1f593efffffff;
const R: Fr = Fr([
    0xac96341c4ffffffb,
    0x36fc76959f60cd29,
    0x666ea36f7879462e,
    0x0e0a77c19a07df2f,
]);

// `Fr` 类型的实现
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

// 运算符实现
impl<'a> Add<&'a Fr> for Fr {
    type Output = Self;

    fn add(self, rhs: &'a Self) -> Self::Output {
        let mut result = self;
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

impl<'a> Mul<&'a Fr> for Fr {
    type Output = Self;

    fn mul(self, rhs: &'a Self) -> Self::Output {
        let mut result = self;
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

// 常量时间比较
impl ConstantTimeEq for Fr {
    fn ct_eq(&self, other: &Self) -> Choice {
        let mut result = 1u8;
        for i in 0..4 {
            result &= (self.0[i] == other.0[i]) as u8;
        }
        Choice::from(result)
    }
}

// 条件选择
impl ConditionallySelectable for Fr {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let mut result = [0u64; 4];
        for i in 0..4 {
            result[i] = u64::conditional_select(&a.0[i], &b.0[i], choice);
        }
        Fr(result)
    }
}

// `Field` 和 `PrimeField` 的实现
impl Field for Fr {
    const ZERO: Self = Self([0, 0, 0, 0]);
    const ONE: Self = R;

    fn random(mut rng: impl rand::RngCore) -> Self {
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
    const MODULUS: &'static str = "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";
    const MULTIPLICATIVE_GENERATOR: Self = Fr::from_raw([0x07, 0x00, 0x00, 0x00]);

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let mut tmp = Fr([0; 4]);
        for i in 0..4 {
            tmp.0[i] = u64::from_le_bytes(repr[i * 8..(i + 1) * 8].try_into().unwrap());
        }
        CtOption::new(tmp, Choice::from(1))
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