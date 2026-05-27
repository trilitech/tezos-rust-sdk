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
    /// Tallinn (proto 024) introduces attestations that also carry a DAL
    /// attestation payload; the on-chain kind name is `attestation_with_dal`.
    AttestationWithDal,
    /// Tallinn aggregate of multiple preattestations into a single BLS-signed
    /// operation.
    PreattestationsAggregate,
    /// Tallinn aggregate of multiple attestations into a single BLS-signed
    /// operation.
    AttestationsAggregate,
    SeedNonceRevelation,
    /// Pre-Seoul (≤ proto 021) used split kinds; Seoul (023) and Tallinn (024)
    /// unify them as `double_consensus_operation_evidence`.
    #[serde(alias = "double_attestation_evidence")]
    DoubleEndorsementEvidence,
    #[serde(alias = "double_preattestation_evidence")]
    DoublePreendorsementEvidence,
    DoubleConsensusOperationEvidence,
    DalEntrapmentEvidence,
    DoubleBakingEvidence,
    VdfRevelation,
    DrainDelegate,
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
    DalPublishCommitment,
}
