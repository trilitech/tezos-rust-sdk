//! Tezos Mutez type.

use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Sub, Rem};
use std::{fmt::Debug, str::FromStr};

use derive_more::{Display, Octal};
use lazy_static::lazy_static;
use num_bigint::{BigInt, BigUint};
use num_traits::{FromPrimitive, ToPrimitive};
use regex::Regex;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::internal::coder::{ConsumingDecoder, Decoder, Encoder, MutezBytesCoder};
use crate::internal::consumable_list::ConsumableList;
use crate::{Error, Result};

use super::number::{Int, Nat};

lazy_static! {
    static ref REGEX: Regex = Regex::new(r"^[0-9]+$").unwrap();
}

/// Tezos Mutez type. It can be encoded into and initialized from bytes and many other number
/// representations.
///
/// # Example
///
/// ```
/// use tezos_core::types::mutez::Mutez;
/// let amount_1: Mutez = "24".try_into().expect("valid number string can be converted to Mutez");
/// let amount_2: Mutez = 42u8.into();
/// ```
///
/// Internally the number is represented with an [i64], but negative values are invalid.
#[derive(PartialEq, PartialOrd, Ord, Debug, Eq, Clone, Copy, Display, Octal)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(try_from = "String"),
    serde(into = "String")
)]
pub struct Mutez(i64);

impl Mutez {
    /// Creates the [Mutez] value from an [i64] integer [value].
    /// Fails if [value < 0].
    pub fn new(value: i64) -> Result<Self> {
        if value < 0 {
            return Err(Error::InvalidMutez);
        }
        Ok(Self(value))
    }

    pub fn is_valid(value: &str) -> bool {
        REGEX.is_match(value)
    }
    /// Encodes the [Mutez] value to bytes.
    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        MutezBytesCoder::encode(self)
    }
    /// Creates the [Mutez] value from bytes that were previously generated using [Mutez::to_bytes].
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        MutezBytesCoder::decode(bytes)
    }

    pub fn from_consumable_bytes<CL: ConsumableList<u8>>(bytes: &mut CL) -> Result<Self> {
        MutezBytesCoder::decode_consuming(bytes)
    }
}

impl Default for Mutez {
    fn default() -> Self {
        Self(0)
    }
}

impl ToPrimitive for Mutez {
    fn to_i64(&self) -> Option<i64> {
        self.0.to_i64()
    }

    fn to_u64(&self) -> Option<u64> {
        self.0.to_u64()
    }

    fn to_i128(&self) -> Option<i128> {
        self.0.to_i128()
    }

    fn to_u128(&self) -> Option<u128> {
        self.0.to_u128()
    }
}

impl FromPrimitive for Mutez {
    fn from_i64(n: i64) -> Option<Mutez> {
        if n >= 0 {
            // Safe to use [Self] constructor since [n >= 0]
            Some(Self(n))
        } else {
            None
        }
    }

    fn from_u64(n: u64) -> Option<Mutez> {
        Self::from_i64(n.to_i64()?)
    }
}

impl FromStr for Mutez {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        Self::new(s.parse()?)
    }
}

macro_rules! impl_try_from_mutez {
    ($T:ty, $to_ty:path) => {
        impl TryFrom<&Mutez> for $T {
            type Error = Error;

            fn try_from(value: &Mutez) -> Result<$T> {
                $to_ty(value).ok_or(Error::InvalidConversion)
            }
        }

        impl TryFrom<Mutez> for $T {
            type Error = Error;

            fn try_from(value: Mutez) -> Result<$T> {
                <$T>::try_from(&value)
            }
        }
    };
}

impl_try_from_mutez!(u8, ToPrimitive::to_u8);
impl_try_from_mutez!(i8, ToPrimitive::to_i8);
impl_try_from_mutez!(u16, ToPrimitive::to_u16);
impl_try_from_mutez!(i16, ToPrimitive::to_i16);
impl_try_from_mutez!(u32, ToPrimitive::to_u32);
impl_try_from_mutez!(i32, ToPrimitive::to_i32);
impl_try_from_mutez!(u64, ToPrimitive::to_u64);
impl_try_from_mutez!(i64, ToPrimitive::to_i64);
impl_try_from_mutez!(u128, ToPrimitive::to_u128);
impl_try_from_mutez!(i128, ToPrimitive::to_i128);
impl_try_from_mutez!(usize, ToPrimitive::to_usize);
impl_try_from_mutez!(isize, ToPrimitive::to_isize);

macro_rules! impl_mutez_from_uint {
    ($T:ty) => {
        impl From<$T> for Mutez {
            fn from(value: $T) -> Self {
                Self(value as i64)
            }
        }
    };
}

impl_mutez_from_uint!(u8);
impl_mutez_from_uint!(u16);
impl_mutez_from_uint!(u32);

macro_rules! impl_mutez_try_from_int {
    ($T:ty, $from_ty:path) => {
        impl TryFrom<$T> for Mutez {
            type Error = Error;

            fn try_from(value: $T) -> Result<Mutez> {
                $from_ty(value).ok_or(Error::InvalidConversion)
            }
        }
    };
}

impl_mutez_try_from_int!(i8, FromPrimitive::from_i8);
impl_mutez_try_from_int!(i16, FromPrimitive::from_i16);
impl_mutez_try_from_int!(i32, FromPrimitive::from_i32);
impl_mutez_try_from_int!(u64, FromPrimitive::from_u64);
impl_mutez_try_from_int!(i64, FromPrimitive::from_i64);
impl_mutez_try_from_int!(u128, FromPrimitive::from_u128);
impl_mutez_try_from_int!(i128, FromPrimitive::from_i128);
impl_mutez_try_from_int!(usize, FromPrimitive::from_usize);
impl_mutez_try_from_int!(isize, FromPrimitive::from_isize);

impl TryFrom<BigUint> for Mutez {
    type Error = Error;

    fn try_from(value: BigUint) -> Result<Self> {
        // Safe to use [Self] since [value.try_into()] will fail if
        // we overflow
        Ok(Self(value.try_into()?))
    }
}

impl TryFrom<Nat> for Mutez {
    type Error = Error;
    fn try_from(value: Nat) -> Result<Self> {
        TryFrom::<BigUint>::try_from(value.value().clone())
    }
}

impl TryFrom<BigInt> for Mutez {
    type Error = Error;

    fn try_from(value: BigInt) -> Result<Self> {
        Ok(Self(value.try_into()?))
    }
}


impl TryFrom<Int> for Mutez {
    type Error = Error;
    fn try_from(value: Int) -> Result<Self> {
        TryFrom::<BigInt>::try_from(value.value().clone())
    }
}

impl From<&Mutez> for BigUint {
    fn from(value: &Mutez) -> Self {
        // Coercion to [u64] is safe here since it is known
        // that [value.0 >= 0]
        BigUint::from(value.0 as u64)
    }
}

impl From<Mutez> for BigUint {
    fn from(value: Mutez) -> Self {
        From::<&Mutez>::from(&value)
    }
}

impl From<&Mutez> for Int {
    fn from(value: &Mutez) -> Self {
        value.0.into()
    }
}

impl From<Mutez> for Int {
    fn from(value: Mutez) -> Self {
        From::<&Mutez>::from(&value)
    }
}

impl TryFrom<&Nat> for Mutez {
    type Error = Error;

    fn try_from(value: &Nat) -> Result<Self> {
        value.value().clone().try_into()
    }
}

impl From<Mutez> for String {
    fn from(mutez: Mutez) -> Self {
        mutez.0.to_string()
    }
}

impl TryFrom<String> for Mutez {
    type Error = Error;

    fn try_from(value: String) -> Result<Self> {
        Ok(Self::from_str(&value)?)
    }
}

impl TryFrom<&str> for Mutez {
    type Error = Error;

    fn try_from(value: &str) -> Result<Self> {
        Ok(Self::from_str(value)?)
    }
}

impl TryFrom<&Vec<u8>> for Mutez {
    type Error = Error;

    fn try_from(value: &Vec<u8>) -> Result<Self> {
        MutezBytesCoder::decode(value)
    }
}

impl TryFrom<&Mutez> for Vec<u8> {
    type Error = Error;

    fn try_from(value: &Mutez) -> Result<Self> {
        value.to_bytes()
    }
}

macro_rules! impl_op {
    ($O:path, $op:ident) => {
        impl $O for Mutez {
            type Output = Result<Mutez>;

            fn $op(self, rhs: Mutez) -> Self::Output {
                Self::new(self.0.$op(rhs.0))
            }
        }
    };
}

impl_op!(Add, add);
impl_op!(Sub, sub);
impl_op!(Div, div);
impl_op!(Mul, mul);
impl_op!(Rem, rem);
impl_op!(BitOr, bitor);
impl_op!(BitAnd, bitand);
impl_op!(BitXor, bitxor);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_add_1() -> Result<()> {
        let v1: Mutez = 1u8.into();
        let v2: Mutez = "2".try_into()?;

        assert_eq!((v1 + v2).unwrap(), 3u32.into());

        Ok(())
    }

    #[test]
    fn test_add_2() -> Result<()> {
        let v1: Mutez = 1u8.into();
        let v2: Mutez = 2u8.into();

        assert_eq!((v1 + v2).unwrap(), 3u32.into());

        Ok(())
    }

    #[test]
    fn test_cmp() -> Result<()> {
        let v1: Mutez = 1u8.into();
        let v2: Mutez = 2u8.into();

        assert!(v1 < v2);

        Ok(())
    }
}
