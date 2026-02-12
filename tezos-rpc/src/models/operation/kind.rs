use {
    derive_more::Display,
    serde::{Deserialize, Serialize},
};

#[derive(Debug, Serialize, Deserialize, Clone, Copy, PartialEq, Display)]
#[serde(rename_all = "snake_case")]
pub enum OperationKind {
    #[serde(alias = "attestation")]
    Endorsement,
    #[serde(alias = "preattestation")]
    Preendorsement,
    SeedNonceRevelation,
    #[serde(alias = "double_attestation_evidence")]
    DoubleEndorsementEvidence,
    #[serde(alias = "double_preattestation_evidence")]
    DoublePreendorsementEvidence,
    DoubleBakingEvidence,
    ActivateAccount,
    Proposals,
    Ballot,
    Reveal,
    Transaction,
    Event,
    Origination,
    Delegation,
    RegisterGlobalConstant,
    SetDepositsLimit,
    FailingNoop,
    TxRollupOrigination,
    TxRollupSubmitBatch,
    TxRollupCommit,
    TxRollupReturnBond,
    TxRollupFinalizeCommitment,
    TxRollupRemoveCommitment,
    TxRollupRejection,
    TxRollupDispatchTickets,
    TransferTicket,
    ScRollupOriginate,
    ScRollupAddMessages,
    ScRollupCement,
    ScRollupPublish,
}
