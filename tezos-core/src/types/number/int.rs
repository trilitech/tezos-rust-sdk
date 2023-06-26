use derive_more::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Neg, Not, Octal, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
    SubAssign,
};
use lazy_static::lazy_static;
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{Num, ToPrimitive};
use regex::Regex;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::{
    fmt::{Debug, Display},
    ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Sub},
    str::FromStr,
};

use crate::{
    internal::coder::{Decoder, Encoder, IntegerBytesCoder},
    Error, Result,
};

use super::Nat;

lazy_static! {
    static ref REGEX: Regex = Regex::new(r"^-?[0-9]+$").unwrap();
}

/// An integer that can be encoded to a Zarith number
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
    Neg,
    Not,
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
pub struct Int(BigInt);

impl Int {
    pub fn from<S: Into<String>>(value: S) -> Result<Self> {
        let value: String = value.into();
        if Self::is_valid(&value) {
            return Ok(Self(BigInt::from_str_radix(&value, 10)?));
        }
        Err(Error::InvalidIntegerString)
    }

    pub fn from_string(value: String) -> Result<Self> {
        Self::from(value)
    }

    pub fn is_valid(value: &str) -> bool {
        REGEX.is_match(value)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        IntegerBytesCoder::decode(bytes)
    }

    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        IntegerBytesCoder::encode(self)
    }

    pub fn to_string(&self) -> String {
        self.0.to_string()
    }

    pub fn value<'a>(&'a self) -> &'a BigInt {
        &self.0
    }

    pub fn into_parts(self) -> (Sign, Nat) {
        let (s, uint) = self.0.into_parts();
        (s, uint.into())
    }

    pub fn abs(self) -> Nat {
        self.into_parts().1.into()
    }
}

impl From<BigInt> for Int {
    fn from(value: BigInt) -> Self {
        Self(value)
    }
}

impl Display for Int {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl ToPrimitive for Int {
    fn to_i64(&self) -> Option<i64> {
        TryInto::<i64>::try_into(self.0.clone()).ok()
    }

    fn to_u64(&self) -> Option<u64> {
        TryInto::<u64>::try_into(self.0.clone()).ok()
    }

    fn to_i128(&self) -> Option<i128> {
        TryInto::<i128>::try_into(self.0.clone()).ok()
    }

    fn to_u128(&self) -> Option<u128> {
        TryInto::<u128>::try_into(self.0.clone()).ok()
    }
}

impl FromStr for Int {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        Self::from_string(s.into())
    }
}

macro_rules! impl_try_from_int {
    ($T:ty) => {
        impl TryFrom<&Int> for $T {
            type Error = Error;

            fn try_from(value: &Int) -> Result<$T> {
                Ok(value.0.clone().try_into()?)
            }
        }

        impl TryFrom<Int> for $T {
            type Error = Error;

            fn try_from(value: Int) -> Result<$T> {
                <$T>::try_from(&value)
            }
        }
    };
}

impl_try_from_int!(i8);
impl_try_from_int!(u8);
impl_try_from_int!(i16);
impl_try_from_int!(u16);
impl_try_from_int!(i32);
impl_try_from_int!(u32);
impl_try_from_int!(i64);
impl_try_from_int!(u64);
impl_try_from_int!(i128);
impl_try_from_int!(u128);
impl_try_from_int!(isize);
impl_try_from_int!(usize);

macro_rules! impl_int_from_int {
    ($T:ty) => {
        impl From<$T> for Int {
            fn from(value: $T) -> Self {
                Self(BigInt::from(value))
            }
        }
    };
}

impl_int_from_int!(i8);
impl_int_from_int!(u8);
impl_int_from_int!(i16);
impl_int_from_int!(u16);
impl_int_from_int!(i32);
impl_int_from_int!(u32);
impl_int_from_int!(i64);
impl_int_from_int!(u64);
impl_int_from_int!(i128);
impl_int_from_int!(u128);
impl_int_from_int!(isize);
impl_int_from_int!(usize);

impl From<Nat> for Int {
    fn from(value: Nat) -> Self {
        Self(value.into())
    }
}

impl From<&Nat> for Int {
    fn from(value: &Nat) -> Self {
        Self(value.into())
    }
}

impl From<Int> for String {
    fn from(value: Int) -> Self {
        value.to_string()
    }
}

impl TryFrom<String> for Int {
    type Error = Error;

    fn try_from(value: String) -> Result<Self> {
        Self::from_string(value)
    }
}

impl TryFrom<&str> for Int {
    type Error = Error;

    fn try_from(value: &str) -> Result<Self> {
        Self::from_string(value.to_string())
    }
}

impl TryFrom<&Vec<u8>> for Int {
    type Error = Error;

    fn try_from(value: &Vec<u8>) -> Result<Self> {
        IntegerBytesCoder::decode(value)
    }
}

impl TryFrom<&Int> for Vec<u8> {
    type Error = Error;

    fn try_from(value: &Int) -> Result<Self> {
        value.to_bytes()
    }
}

impl From<Int> for BigInt {
    fn from(value: Int) -> Self {
        value.0
    }
}

impl From<&Int> for BigInt {
    fn from(value: &Int) -> Self {
        value.0.clone()
    }
}

impl TryFrom<&Int> for BigUint {
    type Error = Error;

    fn try_from(value: &Int) -> Result<Self> {
        value
            .0
            .clone()
            .try_into()
            .map_err(|source| Error::TryFromBigInt { source })
    }
}

impl TryFrom<Int> for BigUint {
    type Error = Error;

    fn try_from(value: Int) -> Result<Self> {
        value
            .0
            .try_into()
            .map_err(|source| Error::TryFromBigInt { source })
    }
}

// Fix pending on https://github.com/JelteF/derive_more/issues/156
macro_rules! impl_op_as_ref {
    ($O:ident, $op:ident) => {
        impl<'a, 'b> $O<&'b Int> for &'a Int {
            type Output = Int;

            fn $op(self, rhs: &'b Int) -> Self::Output {
                Int($O::$op(&self.0, &rhs.0))
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
    fn bigint_into() -> Result<()> {
        let n: BigInt = BigInt::from(0);
        let _i: Int = n.into();
        Ok(())
    }

    #[test]
    fn test_valid_integers() -> Result<()> {
        let integer_strings = vec![
            "-9223372036854775809",
            "-9223372036854775808",
            "-2147483648",
            "-32768",
            "-128",
            "-1",
            "0",
            "1",
            "127",
            "32767",
            "2147483647",
            "9223372036854775807",
            "9223372036854775808",
        ];
        let _integers: Vec<Int> = integer_strings
            .into_iter()
            .map(|item| item.try_into())
            .collect::<Result<Vec<_>>>()?;
        Ok(())
    }

    #[test]
    fn test_invalid_integers() -> Result<()> {
        let integer_strings = vec!["", "abc", "1.", "1.0", " 10", " -10", "- 10", "10%"];
        let results: Vec<Result<Int>> = integer_strings
            .into_iter()
            .map(|item| item.try_into())
            .collect();

        for result in results {
            assert!(result.is_err())
        }

        Ok(())
    }
}
