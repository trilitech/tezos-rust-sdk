use {
    crate::models::{
        balance_update::BalanceUpdate, operation::kind::OperationKind,
        operation::operation_result::operations::tx_rollup_submit_batch::TxRollupSubmitBatchOperationResult,
    },
    serde::{Deserialize, Serialize},
    tezos_core::types::{
        encoded::{ImplicitAddress, TxRollupId},
        mutez::Mutez,
    },
};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct TxRollupSubmitBatch {
    /// [OperationKind::TxRollupSubmitBatch]
    pub kind: OperationKind,
    /// Public key hash (Base58Check-encoded)
    pub source: ImplicitAddress,
    pub fee: Mutez,
    pub counter: String,
    pub gas_limit: String,
    pub storage_limit: String,
    pub rollup: TxRollupId,
    pub content: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub burn_limit: Option<Mutez>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<TxRollupSubmitBatchMetadata>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct TxRollupSubmitBatchMetadata {
    pub operation_result: TxRollupSubmitBatchOperationResult,
    #[serde(default)]
    pub balance_updates: Vec<BalanceUpdate>,
}
