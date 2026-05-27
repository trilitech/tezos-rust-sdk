use {
    super::attestations_aggregate::{AggregateConsensusContent, AttestationsAggregateMetadata},
    crate::models::operation::kind::OperationKind,
    serde::{Deserialize, Serialize},
};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct PreattestationsAggregate {
    /// [OperationKind::PreattestationsAggregate]
    pub kind: OperationKind,
    pub consensus_content: AggregateConsensusContent,
    /// Preattestations don't carry DAL state, so the committee is just slots.
    pub committee: Vec<u16>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<AttestationsAggregateMetadata>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> serde_json::Value {
        serde_json::json!({
            "kind": "preattestations_aggregate",
            "consensus_content": {
                "level": 1839178,
                "round": 0,
                "block_payload_hash": "vh1he5NXZcwZmGe3cGdepQU83C6Qky7m1tWJsShNnjT7amg8X7Jy"
            },
            "committee": [1, 2, 3]
        })
    }

    #[test]
    fn test_deserialize() {
        let parsed: PreattestationsAggregate =
            serde_json::from_value(sample()).expect("sample must deserialize");
        assert_eq!(parsed.kind, OperationKind::PreattestationsAggregate);
        assert_eq!(parsed.consensus_content.level, 1839178);
        assert_eq!(parsed.committee, vec![1, 2, 3]);
        assert!(parsed.metadata.is_none());
    }

    #[test]
    fn test_roundtrip_structural() {
        let original = sample();
        let parsed: PreattestationsAggregate =
            serde_json::from_value(original.clone()).expect("sample must deserialize");
        let reserialized =
            serde_json::to_value(&parsed).expect("must serialize back to JSON value");
        assert_eq!(reserialized, original);
    }
}
