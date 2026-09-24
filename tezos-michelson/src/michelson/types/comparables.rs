use crate::{michelson::Michelson, Error, Result};

use super::macros::{make_type, make_types};

make_types!(
    [
        fn fallback(_value: PrimitiveApplication) -> Result<Self> {
            Err(Error::InvalidPrimitiveApplication)
        }
    ],
    conversion_fallback: fallback,
    (Unit, unit, super_enum: crate::michelson::types::Type, Comparable),
    (Never, never, super_enum: crate::michelson::types::Type, Comparable),
    (Bool, bool, super_enum: crate::michelson::types::Type, Comparable),
    (Int, int, super_enum: crate::michelson::types::Type, Comparable),
    (Nat, nat, super_enum: crate::michelson::types::Type, Comparable),
    (String, string, super_enum: crate::michelson::types::Type, Comparable),
    (ChainId, chain_id, super_enum: crate::michelson::types::Type, Comparable),
    (Bytes, bytes, super_enum: crate::michelson::types::Type, Comparable),
    (Mutez, mutez, super_enum: crate::michelson::types::Type, Comparable),
    (KeyHash, key_hash, super_enum: crate::michelson::types::Type, Comparable),
    (Key, key, super_enum: crate::michelson::types::Type, Comparable),
    (Signature, signature, super_enum: crate::michelson::types::Type, Comparable),
    (Timestamp, timestamp, super_enum: crate::michelson::types::Type, Comparable),
    (Address, address, super_enum: crate::michelson::types::Type, Comparable),
    (Option, option, super_enum: crate::michelson::types::Type, Comparable, boxed: (r#type: Type)),
    (Or, or, super_enum: crate::michelson::types::Type, Comparable, boxed: (lhs: Type), boxed: (rhs: Type)),
    (Pair, pair, super_enum: crate::michelson::types::Type, Comparable, vec: (types: Type)),
);

impl From<Type> for super::Type {
    fn from(value: Type) -> Self {
        Self::Comparable(value)
    }
}

impl TryFrom<super::Type> for Type {
    type Error = Error;

    fn try_from(value: super::Type) -> Result<Self> {
        if let super::Type::Comparable(value) = value {
            return Ok(value);
        }
        Err(Error::InvalidMichelsonType)
    }
}

impl From<Type> for Michelson {
    fn from(value: Type) -> Self {
        Self::Type(value.into())
    }
}

impl TryFrom<Michelson> for Type {
    type Error = Error;

    fn try_from(value: Michelson) -> Result<Self> {
        let value: super::Type = value.try_into()?;
        value.try_into()
    }
}

impl From<Primitive> for crate::michelson::Primitive {
    fn from(value: Primitive) -> Self {
        Self::ComparableType(value)
    }
}
