use crate::{Error, Result};

/// Every Michelson primitive in the order the protocol's binary encoding
/// numbers them: a primitive's tag is its index here. Copied from
/// `prim_encoding` in Octez's `michelson_v1_primitives.ml` for protocol 025
/// (`PsUshuai`), which requires a new primitive to go at the end so that bytes
/// every earlier protocol encoded still decode. A primitive a later protocol
/// adds is therefore absent here and refused, never given another's tag.
///
/// It is the only statement of the tags: the Micheline byte coder reads it for
/// every primitive, including those no typed Michelson table models, and the
/// typed tables take their discriminants from it through [`tag_of`].
const PRIMITIVES: [&str; 161] = [
    // 0
    "parameter",
    "storage",
    "code",
    "False",
    "Elt",
    "Left",
    "None",
    "Pair",
    "Right",
    "Some",
    // 10
    "True",
    "Unit",
    "PACK",
    "UNPACK",
    "BLAKE2B",
    "SHA256",
    "SHA512",
    "ABS",
    "ADD",
    "AMOUNT",
    // 20
    "AND",
    "BALANCE",
    "CAR",
    "CDR",
    "CHECK_SIGNATURE",
    "COMPARE",
    "CONCAT",
    "CONS",
    "CREATE_ACCOUNT",
    "CREATE_CONTRACT",
    // 30
    "IMPLICIT_ACCOUNT",
    "DIP",
    "DROP",
    "DUP",
    "EDIV",
    "EMPTY_MAP",
    "EMPTY_SET",
    "EQ",
    "EXEC",
    "FAILWITH",
    // 40
    "GE",
    "GET",
    "GT",
    "HASH_KEY",
    "IF",
    "IF_CONS",
    "IF_LEFT",
    "IF_NONE",
    "INT",
    "LAMBDA",
    // 50
    "LE",
    "LEFT",
    "LOOP",
    "LSL",
    "LSR",
    "LT",
    "MAP",
    "MEM",
    "MUL",
    "NEG",
    // 60
    "NEQ",
    "NIL",
    "NONE",
    "NOT",
    "NOW",
    "OR",
    "PAIR",
    "PUSH",
    "RIGHT",
    "SIZE",
    // 70
    "SOME",
    "SOURCE",
    "SENDER",
    "SELF",
    "STEPS_TO_QUOTA",
    "SUB",
    "SWAP",
    "TRANSFER_TOKENS",
    "SET_DELEGATE",
    "UNIT",
    // 80
    "UPDATE",
    "XOR",
    "ITER",
    "LOOP_LEFT",
    "ADDRESS",
    "CONTRACT",
    "ISNAT",
    "CAST",
    "RENAME",
    "bool",
    // 90
    "contract",
    "int",
    "key",
    "key_hash",
    "lambda",
    "list",
    "map",
    "big_map",
    "nat",
    "option",
    // 100
    "or",
    "pair",
    "set",
    "signature",
    "string",
    "bytes",
    "mutez",
    "timestamp",
    "unit",
    "operation",
    // 110
    "address",
    "SLICE",
    "DIG",
    "DUG",
    "EMPTY_BIG_MAP",
    "APPLY",
    "chain_id",
    "CHAIN_ID",
    "LEVEL",
    "SELF_ADDRESS",
    // 120
    "never",
    "NEVER",
    "UNPAIR",
    "VOTING_POWER",
    "TOTAL_VOTING_POWER",
    "KECCAK",
    "SHA3",
    "PAIRING_CHECK",
    "bls12_381_g1",
    "bls12_381_g2",
    // 130
    "bls12_381_fr",
    "sapling_state",
    "sapling_transaction_deprecated",
    "SAPLING_EMPTY_STATE",
    "SAPLING_VERIFY_UPDATE",
    "ticket",
    "TICKET_DEPRECATED",
    "READ_TICKET",
    "SPLIT_TICKET",
    "JOIN_TICKETS",
    // 140
    "GET_AND_UPDATE",
    "chest",
    "chest_key",
    "OPEN_CHEST",
    "VIEW",
    "view",
    "constant",
    "SUB_MUTEZ",
    "tx_rollup_l2_address",
    "MIN_BLOCK_TIME",
    // 150
    "sapling_transaction",
    "EMIT",
    "Lambda_rec",
    "LAMBDA_REC",
    "TICKET",
    "BYTES",
    "NAT",
    "Ticket",
    "IS_IMPLICIT_ACCOUNT",
    "INDEX_ADDRESS",
    // 160
    "GET_ADDRESS_INDEX",
];

pub fn tag(name: &str) -> Result<u8> {
    position(name).ok_or(Error::InvalidStringValue)
}

/// [`tag`] at compile time, for a typed table's discriminant, so a typed
/// primitive the protocol does not list fails the build.
pub(crate) const fn tag_of(name: &str) -> u8 {
    match position(name) {
        Some(tag) => tag,
        None => panic!("not a Michelson primitive of this protocol"),
    }
}

pub fn name(tag: u8) -> Result<&'static str> {
    PRIMITIVES
        .get(usize::from(tag))
        .copied()
        .ok_or(Error::InvalidBytes)
}

const fn position(name: &str) -> Option<u8> {
    let mut index = 0;
    while index < PRIMITIVES.len() {
        if equal(PRIMITIVES[index].as_bytes(), name.as_bytes()) {
            return Some(index as u8);
        }
        index += 1;
    }
    None
}

const fn equal(lhs: &[u8], rhs: &[u8]) -> bool {
    if lhs.len() != rhs.len() {
        return false;
    }
    let mut index = 0;
    while index < lhs.len() {
        if lhs[index] != rhs[index] {
            return false;
        }
        index += 1;
    }
    true
}
