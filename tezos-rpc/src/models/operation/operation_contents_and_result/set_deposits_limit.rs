use {
    crate::models::{
        balance_update::BalanceUpdate, operation::kind::OperationKind,
        operation::operation_result::operations::set_deposits_limit::SetDepositsLimitOperationResult,
    },
    serde::{Deserialize, Serialize},
    tezos_core::types::{encoded::ImplicitAddress, mutez::Mutez},
};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct SetDepositsLimit {
    /// [OperationKind::SetDepositsLimit]
    pub kind: OperationKind,
    /// Public key hash (Base58Check-encoded)
    pub source: ImplicitAddress,
    pub fee: Mutez,
    pub counter: String,
    pub gas_limit: String,
    pub storage_limit: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub limit: Option<Mutez>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<SetDepositsLimitsMetadata>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct SetDepositsLimitsMetadata {
    pub operation_result: SetDepositsLimitOperationResult,
    #[serde(default)]
    pub balance_updates: Vec<BalanceUpdate>,
}
