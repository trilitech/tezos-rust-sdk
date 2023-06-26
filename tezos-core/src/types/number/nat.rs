use derive_more::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Octal, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};
use lazy_static::lazy_static;
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{FromPrimitive, Num, ToPrimitive};
use regex::Regex;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::{
    fmt::{Debug, Display},
    ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Sub},
    str::FromStr,
};

use crate::{
    internal::{
        coder::{ConsumingDecoder, Decoder, Encoder, NaturalBytesCoder},
        consumable_list::ConsumableList,
    },
    types::{mutez::Mutez, number::Int},
    Error, Result,
};

lazy_static! {
    static ref REGEX: Regex = Regex::new(r"^[0-9]+$").unwrap();
}

/// An unsigned integer that can be encoded to a Zarith number
#[derive(
    Add,
    AddAssign,
    PartialEq,
    PartialOrd,
    Ord,
    Debug,
    Eq,
    Clone,
    BitAnd,
    BitAndAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
    Div,
    DivAssign,
    Mul,
    MulAssign,
    Octal,
    Rem,
    RemAssign,
    Shl,
    ShlAssign,
    Shr,
    ShrAssign,
    Sub,
    SubAssign,
)]
#[div(forward)]
#[div_assign(forward)]
#[mul(forward)]
#[mul_assign(forward)]
#[rem(forward)]
#[rem_assign(forward)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(try_from = "String"),
    serde(into = "String")
)]
pub struct Nat(BigUint);

impl Nat {
    pub fn from<S: Into<String>>(value: S) -> Result<Self> {
        let value: String = value.into();
        if Self::is_valid(&value) {
            return Ok(Self(BigUint::from_str_radix(&value, 10)?));
        }
        Err(Error::InvalidIntegerString)
    }

    pub fn from_string(value: String) -> Result<Self> {
        Self::from(value)
    }

    pub fn is_valid(value: &str) -> bool {
        REGEX.is_match(value)
    }

    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        NaturalBytesCoder::encode(self)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        NaturalBytesCoder::decode(bytes)
    }

    pub fn from_consumable_bytes<CL: ConsumableList<u8>>(bytes: &mut CL) -> Result<Self> {
        NaturalBytesCoder::decode_consuming(bytes)
    }

    pub fn to_string(&self) -> String {
        self.0.to_string()
    }

    pub fn value(&self) -> &BigUint {
        &self.0
    }
}

impl From<BigUint> for Nat {
    fn from(value: BigUint) -> Self {
        Self(value)
    }
}

impl Display for Nat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl ToPrimitive for Nat {
    fn to_i64(&self) -> Option<i64> {
        None
    }

    fn to_u64(&self) -> Option<u64> {
        TryInto::<u64>::try_into(self.0.clone()).ok()
    }

    fn to_i128(&self) -> Option<i128> {
        None
    }

    fn to_u128(&self) -> Option<u128> {
        TryInto::<u128>::try_into(self.0.clone()).ok()
    }
}

impl FromPrimitive for Nat {
    fn from_i64(n: i64) -> Option<Nat> {
        if n >= 0 {
            // Safe to use [Self] constructor since [n >= 0]
            Some(Self(BigUint::from(n as u64)))
        } else {
            None
        }
    }

    fn from_u64(n: u64) -> Option<Nat> {
        Some(Self(BigUint::from(n)))
    }
}

impl FromStr for Nat {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        Self::from_string(s.into())
    }
}

macro_rules! impl_try_from_nat {
    ($T:ty) => {
        impl TryFrom<&Nat> for $T {
            type Error = Error;

            fn try_from(value: &Nat) -> Result<$T> {
                Ok(value.0.clone().try_into()?)
            }
        }

        impl TryFrom<Nat> for $T {
            type Error = Error;

            fn try_from(value: Nat) -> Result<$T> {
                <$T>::try_from(&value)
            }
        }
    };
}

impl_try_from_nat!(u8);
impl_try_from_nat!(u16);
impl_try_from_nat!(u32);
impl_try_from_nat!(u64);
impl_try_from_nat!(u128);
impl_try_from_nat!(usize);

macro_rules! impl_nat_from_uint {
    ($T:ty) => {
        impl From<$T> for Nat {
            fn from(value: $T) -> Self {
                Self(BigUint::from(value))
            }
        }
    };
}

impl_nat_from_uint!(u8);
impl_nat_from_uint!(u16);
impl_nat_from_uint!(u32);
impl_nat_from_uint!(u64);
impl_nat_from_uint!(u128);
impl_nat_from_uint!(usize);

macro_rules! impl_nat_try_from_int {
    ($T:ty, $from_ty:path) => {
        impl TryFrom<$T> for Nat {
            type Error = Error;

            fn try_from(value: $T) -> Result<Nat> {
                $from_ty(value).ok_or(Error::InvalidConversion)
            }
        }
    };
}

impl_nat_try_from_int!(i8, FromPrimitive::from_i8);
impl_nat_try_from_int!(i16, FromPrimitive::from_i16);
impl_nat_try_from_int!(i32, FromPrimitive::from_i32);
impl_nat_try_from_int!(i64, FromPrimitive::from_i64);
impl_nat_try_from_int!(i128, FromPrimitive::from_i128);
impl_nat_try_from_int!(isize, FromPrimitive::from_isize);

impl TryFrom<Int> for Nat {
    type Error = Error;

    fn try_from(value: Int) -> Result<Nat> {
        let (s, n) = value.into_parts();
        match s {
            Sign::Minus => Err(Error::InvalidConversion),
            Sign::NoSign => Ok(n),
            Sign::Plus => Ok(n),
        }
    }
}

impl From<&Mutez> for Nat {
    fn from(mutez: &Mutez) -> Self {
        Self(mutez.into())
    }
}

impl From<Mutez> for Nat {
    fn from(mutez: Mutez) -> Self {
        From::<&Mutez>::from(&mutez)
    }
}

impl From<Nat> for String {
    fn from(value: Nat) -> Self {
        value.to_string()
    }
}

impl TryFrom<String> for Nat {
    type Error = Error;

    fn try_from(value: String) -> Result<Self> {
        Self::from_string(value)
    }
}

impl TryFrom<&str> for Nat {
    type Error = Error;

    fn try_from(value: &str) -> Result<Self> {
        Self::from_string(value.to_string())
    }
}

impl TryFrom<&Vec<u8>> for Nat {
    type Error = Error;

    fn try_from(value: &Vec<u8>) -> Result<Self> {
        NaturalBytesCoder::decode(value)
    }
}

impl TryFrom<&Nat> for Vec<u8> {
    type Error = Error;

    fn try_from(value: &Nat) -> Result<Self> {
        value.to_bytes()
    }
}

impl From<Nat> for BigInt {
    fn from(value: Nat) -> Self {
        value.0.into()
    }
}

impl From<&Nat> for BigInt {
    fn from(value: &Nat) -> Self {
        value.0.clone().into()
    }
}

impl From<&Nat> for BigUint {
    fn from(value: &Nat) -> Self {
        value.0.clone()
    }
}

impl From<Nat> for BigUint {
    fn from(value: Nat) -> Self {
        value.0
    }
}

// Fix pending on https://github.com/JelteF/derive_more/issues/156
macro_rules! impl_op_as_ref {
    ($O:ident, $op:ident) => {
        impl<'a, 'b> $O<&'b Nat> for &'a Nat {
            type Output = Nat;

            fn $op(self, rhs: &'b Nat) -> Self::Output {
                Nat($O::$op(&self.0, &rhs.0))
            }
        }
    };
}

impl_op_as_ref!(Add, add);
impl_op_as_ref!(Sub, sub);
impl_op_as_ref!(Div, div);
impl_op_as_ref!(Mul, mul);
impl_op_as_ref!(Rem, rem);
impl_op_as_ref!(BitOr, bitor);
impl_op_as_ref!(BitAnd, bitand);
impl_op_as_ref!(BitXor, bitxor);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_valid_naturals() -> Result<()> {
        let values = vec![
            "0",
            "1",
            "127",
            "32767",
            "2147483647",
            "9223372036854775807",
            "9223372036854775808",
        ];
        let _result: Vec<Nat> = values
            .into_iter()
            .map(|item| item.try_into())
            .collect::<Result<Vec<_>>>()?;
        Ok(())
    }

    #[test]
    fn test_invalid_naturals() -> Result<()> {
        let values = vec![
            "",
            "abc",
            "1.",
            "1.0",
            " 10",
            " -10",
            "- 10",
            "10%",
            "-9223372036854775809",
            "-9223372036854775808",
            "-2147483648",
            "-32768",
            "-128",
            "-1",
        ];
        let results: Vec<Result<Nat>> = values.into_iter().map(|item| item.try_into()).collect();

        for result in results {
            assert!(result.is_err())
        }

        Ok(())
    }
}
