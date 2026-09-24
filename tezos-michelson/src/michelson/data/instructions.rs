mod macros;
mod sequence;

use macros::{make_instruction, make_instructions};

make_instructions!(
    (Never, NEVER, never),
    (Swap, SWAP, swap),
    (GetAndUpdate, GET_AND_UPDATE, get_and_update),
    (Apply, APPLY, apply),
    (FailWith, FAILWITH, failwith),
    (
        Rename,
        RENAME,
        rename,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Car,
        CAR,
        car,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Cast,
        CAST,
        cast,
        metadata_type: crate::michelson::metadata::VariableMetadata,
        (r#type: crate::michelson::types::Type)
    ),
    (
        Cdr,
        CDR,
        cdr,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Cons,
        CONS,
        cons,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Exec,
        EXEC,
        exec,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Mem,
        MEM,
        mem,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Size,
        SIZE,
        size,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Some,
        SOME,
        some,
        metadata_type: crate::michelson::metadata::TypeVariableMetadata
    ),
    (
        Unit,
        UNIT,
        unit,
        metadata_type: crate::michelson::metadata::TypeVariableMetadata
    ),
    (Dig, DIG, dig, (n: crate::michelson::data::Nat)),
    (
        Drop,
        DROP,
        drop,
        optional: (n: crate::michelson::data::Nat)
    ),
    (Dug, DUG, dug, (n: crate::michelson::data::Nat)),
    (
        Iter,
        ITER,
        iter,
        (expression: crate::michelson::data::instructions::Sequence)
    ),
    (
        LoopLeft,
        LOOP_LEFT,
        loop_left,
        (body: crate::michelson::data::instructions::Sequence)
    ),
    (
        Loop,
        LOOP,
        r#loop,
        (body: crate::michelson::data::instructions::Sequence)
    ),
    (
        Concat,
        CONCAT,
        concat,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (Slice, SLICE, slice),
    (Pack, PACK, pack),
    (
        Unpack,
        UNPACK,
        unpack,
        metadata_type: crate::michelson::metadata::TypeVariableMetadata,
        (r#type: crate::michelson::types::Type)
    ),
    (
        Add,
        ADD,
        add,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Dip,
        DIP,
        dip,
        (instruction: crate::michelson::data::instructions::Sequence),
        optional: (n: crate::michelson::data::Nat)
    ),
    (
        Dup,
        DUP,
        dup,
        metadata_type: crate::michelson::metadata::VariableMetadata,
        optional: (n: crate::michelson::data::Nat)
    ),
    (
        EmptyBigMap,
        EMPTY_BIG_MAP,
        empty_big_map,
        metadata_type: crate::michelson::metadata::TypeVariableMetadata,
        (key_type: crate::michelson::types::Type),
        (value_type: crate::michelson::types::Type)
    ),
    (
        EmptyMap,
        EMPTY_MAP,
        empty_map,
        metadata_type: crate::michelson::metadata::TypeVariableMetadata,
        (key_type: crate::michelson::types::Type),
        (value_type: crate::michelson::types::Type)
    ),
    (
        EmptySet,
        EMPTY_SET,
        empty_set,
        metadata_type: crate::michelson::metadata::TypeVariableMetadata,
        (r#type: crate::michelson::types::Type)
    ),
    (
        Get,
        GET,
        get,
        metadata_type: crate::michelson::metadata::VariableMetadata,
        optional: (n: crate::michelson::data::Nat)
    ),
    (
        IfCons,
        IF_CONS,
        if_cons,
        (if_branch: crate::michelson::data::instructions::Sequence),
        (else_branch: crate::michelson::data::instructions::Sequence)
    ),
    (
        IfLeft,
        IF_LEFT,
        if_left,
        (if_branch: crate::michelson::data::instructions::Sequence),
        (else_branch: crate::michelson::data::instructions::Sequence)
    ),
    (
        IfNone,
        IF_NONE,
        if_none,
        (if_branch: crate::michelson::data::instructions::Sequence),
        (else_branch: crate::michelson::data::instructions::Sequence)
    ),
    (
        If,
        IF,
        r#if,
        (if_branch: crate::michelson::data::instructions::Sequence),
        (else_branch: crate::michelson::data::instructions::Sequence)
    ),
    (
        Lambda,
        LAMBDA,
        lambda,
        metadata_type: crate::michelson::metadata::VariableMetadata,
        (parameter_type: crate::michelson::types::Type),
        (return_type: crate::michelson::types::Type),
        (body: crate::michelson::data::instructions::Sequence)
    ),
    (
        Left,
        LEFT,
        left,
        metadata_type: crate::michelson::metadata::TypeVariableMetadata,
        (r#type: crate::michelson::types::Type)
    ),
    (
        Right,
        RIGHT,
        right,
        metadata_type: crate::michelson::metadata::TypeVariableMetadata,
        (r#type: crate::michelson::types::Type)
    ),
    (
        Map,
        MAP,
        map,
        metadata_type: crate::michelson::metadata::VariableMetadata,
        (expression: crate::michelson::data::instructions::Sequence)
    ),
    (
        Nil,
        NIL,
        nil,
        metadata_type: crate::michelson::metadata::TypeVariableMetadata,
        (r#type: crate::michelson::types::Type)
    ),
    (
        None,
        NONE,
        none,
        metadata_type: crate::michelson::metadata::TypeVariableMetadata,
        (r#type: crate::michelson::types::Type)
    ),
    (
        Pair,
        PAIR,
        pair,
        metadata_type: crate::michelson::metadata::TypeVariableMetadata,
        optional: (n: crate::michelson::data::Nat)
    ),
    (
        Unpair,
        UNPAIR,
        unpair,
        metadata_type: crate::michelson::metadata::TypeVariableMetadata,
        optional: (n: crate::michelson::data::Nat)
    ),
    (
        Push,
        PUSH,
        push,
        metadata_type: crate::michelson::metadata::VariableMetadata,
        (r#type: crate::michelson::types::Type),
        boxed: (value: crate::michelson::Data)
    ),
    (
        Update,
        UPDATE,
        update,
        metadata_type: crate::michelson::metadata::VariableMetadata,
        optional: (n: crate::michelson::data::Nat)
    ),
    (
        Sub,
        SUB,
        sub,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        SubMutez,
        SUB_MUTEZ,
        sub_mutez,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Mul,
        MUL,
        mul,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Ediv,
        EDIV,
        ediv,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Abs,
        ABS,
        abs,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        IsNat,
        ISNAT,
        isnat,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Int,
        INT,
        int,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Neg,
        NEG,
        neg,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Lsl,
        LSL,
        lsl,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Lsr,
        LSR,
        lsr,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Or,
        OR,
        or,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        And,
        AND,
        and,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Xor,
        XOR,
        xor,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Not,
        NOT,
        not,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Compare,
        COMPARE,
        compare,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Eq,
        EQ,
        eq,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Neq,
        NEQ,
        neq,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Lt,
        LT,
        lt,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Gt,
        GT,
        gt,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Le,
        LE,
        le,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Ge,
        GE,
        ge,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Self_,
        SELF,
        self_,
        metadata_type: crate::michelson::metadata::FieldMetadata
    ),
    (
        SelfAddress,
        SELF_ADDRESS,
        self_address,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Contract,
        CONTRACT,
        contract,
        metadata_type: crate::michelson::metadata::FieldMetadata,
        (r#type: crate::michelson::types::Type)
    ),
    (TransferTokens, TRANSFER_TOKENS, transfer_tokens),
    (
        SetDelegate,
        SET_DELEGATE,
        set_delegate,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        CreateContract,
        CREATE_CONTRACT,
        create_contract,
        metadata_type: crate::michelson::metadata::TwoVariableMetadata,
        (parameter_type: crate::michelson::types::Type),
        (storage_type: crate::michelson::types::Type),
        (code: crate::michelson::data::instructions::Sequence)
    ),
    (
        ImplicitAccount,
        IMPLICIT_ACCOUNT,
        implicit_account,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (VotingPower, VOTING_POWER, voting_power),
    (
        Now,
        NOW,
        now,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Level,
        LEVEL,
        level,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Amount,
        AMOUNT,
        amount,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Balance,
        BALANCE,
        balance,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        CheckSignature,
        CHECK_SIGNATURE,
        check_signature,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Blake2B,
        BLAKE2B,
        blake2b,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Keccak,
        KECCAK,
        keccak,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Sha3,
        SHA3,
        sha3,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Sha256,
        SHA256,
        sha256,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Sha512,
        SHA512,
        sha512,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        HashKey,
        HASH_KEY,
        hash_key,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Source,
        SOURCE,
        source,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Sender,
        SENDER,
        sender,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        Address,
        ADDRESS,
        address,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        ChainId,
        CHAIN_ID,
        chain_id,
        metadata_type: crate::michelson::metadata::VariableMetadata
    ),
    (
        TotalVotingPower,
        TOTAL_VOTING_POWER,
        total_voting_power
    ),
    (PairingCheck, PAIRING_CHECK, pairing_check),
    (
        SaplingEmptyState,
        SAPLING_EMPTY_STATE,
        sapling_empty_state,
        (memo_size: crate::michelson::data::Nat)
    ),
    (
        SaplingVerifyUpdate,
        SAPLING_VERIFY_UPDATE,
        sapling_verify_update
    ),
    (Ticket, TICKET, ticket),
    (ReadTicket, READ_TICKET, read_ticket),
    (SplitTicket, SPLIT_TICKET, split_ticket),
    (JoinTickets, JOIN_TICKETS, join_ticket),
    (OpenChest, OPEN_CHEST, open_chest),
    (IndexAddress, INDEX_ADDRESS, index_address),
    (GetAddressIndex, GET_ADDRESS_INDEX, get_address_index),
);

impl From<Primitive> for crate::michelson::Primitive {
    fn from(value: Primitive) -> Self {
        Self::Instruction(value)
    }
}
