use {
    derive_more::Display,
    serde::{Deserialize, Serialize},
};

#[derive(Debug, Serialize, Deserialize, Clone, Copy, PartialEq, Display)]
#[serde(rename_all = "snake_case")]
pub enum OperationKind {
    Endorsement,
    /// Tallinn-era spelling of [Self::Endorsement].
    Attestation,
    Preendorsement,
    /// Tallinn-era spelling of [Self::Preendorsement].
    Preattestation,
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
    DoubleEndorsementEvidence,
    /// Tallinn-era spelling of [Self::DoubleEndorsementEvidence].
    DoubleAttestationEvidence,
    DoublePreendorsementEvidence,
    /// Tallinn-era spelling of [Self::DoublePreendorsementEvidence].
    DoublePreattestationEvidence,
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

#[cfg(test)]
mod test {
    use super::OperationKind;

    fn roundtrip(name: &str, expected: OperationKind) {
        let json = format!("\"{name}\"");
        let parsed: OperationKind =
            serde_json::from_str(&json).expect("kind name must deserialize");
        assert_eq!(parsed, expected);
        let reserialized = serde_json::to_string(&parsed).expect("kind must serialize");
        assert_eq!(reserialized, json);
    }

    #[test]
    fn attestation_roundtrip() {
        roundtrip("attestation", OperationKind::Attestation);
    }

    #[test]
    fn preattestation_roundtrip() {
        roundtrip("preattestation", OperationKind::Preattestation);
    }

    #[test]
    fn double_attestation_evidence_roundtrip() {
        roundtrip(
            "double_attestation_evidence",
            OperationKind::DoubleAttestationEvidence,
        );
    }

    #[test]
    fn double_preattestation_evidence_roundtrip() {
        roundtrip(
            "double_preattestation_evidence",
            OperationKind::DoublePreattestationEvidence,
        );
    }
}
