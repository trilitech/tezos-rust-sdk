use derive_more::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Octal, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};
use lazy_static::lazy_static;
use num_bigint::{BigInt, BigUint};
use num_traits::{Num, ToPrimitive};
use regex::Regex;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::{
    fmt::{Debug, Display},
    str::FromStr,
};

use crate::{
    internal::{
        coder::{ConsumingDecoder, Decoder, Encoder, NaturalBytesCoder},
        consumable_list::ConsumableList,
    },
    types::mutez::Mutez,
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

impl FromStr for Nat {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        Self::from_string(s.into())
    }
}

impl From<u8> for Nat {
    fn from(value: u8) -> Self {
        Self(BigUint::from(value))
    }
}

impl From<u16> for Nat {
    fn from(value: u16) -> Self {
        Self(BigUint::from(value))
    }
}

impl From<u32> for Nat {
    fn from(value: u32) -> Self {
        Self(BigUint::from(value))
    }
}

impl From<u64> for Nat {
    fn from(value: u64) -> Self {
        Self(BigUint::from(value))
    }
}

impl From<u128> for Nat {
    fn from(value: u128) -> Self {
        Self(BigUint::from(value))
    }
}

impl From<BigUint> for Nat {
    fn from(value: BigUint) -> Self {
        Self(value)
    }
}

impl From<&Mutez> for Nat {
    fn from(mutez: &Mutez) -> Self {
        Self(BigUint::from(mutez.value()))
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
