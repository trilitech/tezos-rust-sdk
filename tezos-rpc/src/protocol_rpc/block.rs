use crate::{client::TezosRpcChainId, http::Http};

pub mod context;
pub mod hash;
pub mod helpers;

use {
    crate::models::block::BlockId,
    crate::{client::TezosRpcContext, error::Error, models::block::Block},
    derive_more::Display,
    serde::{Deserialize, Serialize},
};

fn path<S: AsRef<str>>(chain_id: S, block_id: &BlockId) -> String {
    format!("/chains/{}/blocks/{}", chain_id.as_ref(), block_id.value())
}

/// A builder to construct the properties of a request to get all the information about a block.
#[derive(Clone, Copy)]
pub struct RpcRequestBuilder<'a, HttpClient: Http> {
    ctx: &'a TezosRpcContext<HttpClient>,
    chain_id: &'a TezosRpcChainId,
    block_id: &'a BlockId,
    metadata: MetadataArg,
}

impl<'a, HttpClient: Http> RpcRequestBuilder<'a, HttpClient> {
    pub fn new(ctx: &'a TezosRpcContext<HttpClient>) -> Self {
        RpcRequestBuilder {
            ctx,
            chain_id: ctx.chain_id(),
            block_id: &BlockId::Head,
            metadata: MetadataArg::Always,
        }
    }

    /// Modify chain identifier to be used in the request.
    pub fn chain_id(mut self, chain_id: &'a TezosRpcChainId) -> Self {
        self.chain_id = chain_id;

        self
    }

    /// Modify the block identifier to be used in the request.
    pub fn block_id(mut self, block_id: &'a BlockId) -> Self {
        self.block_id = block_id;

        self
    }

    /// Specify whether or not if the operations metadata should be returned.
    /// By default, the metadata will be returned depending on the node's metadata size limit policy.
    ///
    /// To get the metadata, even if it is needed to recompute them, use [MetadataArg::Always].
    ///
    /// To avoid getting the metadata, use [MetadataArg::Never].
    pub fn metadata(mut self, metadata: MetadataArg) -> Self {
        self.metadata = metadata;

        self
    }

    pub async fn send(&self) -> Result<Block, Error> {
        let path = self::path(self.chain_id.value(), self.block_id);

        let mut query: Vec<(&str, &'static str)> = vec![];

        // Add `metadata` query parameter
        query.push(("metadata", self.metadata.to_str()));

        self.ctx
            .http_client()
            .get_with_query(path.as_str(), &Some(query))
            .await
    }
}

/// * [MetadataArg::Always] - Block metadata is included in the response.
/// * [MetadataArg::Never] - Block metadata is not included in the response.
#[derive(Clone, Copy, Display, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum MetadataArg {
    Always,
    Never,
}

impl MetadataArg {
    fn to_str(&self) -> &'static str {
        match self {
            Self::Always => "always",
            Self::Never => "never",
        }
    }
}

/// Get all the information about a block.
/// The associated metadata may not be present depending on the history mode and block's distance from the head.
///
/// Optional query arguments:
/// * `metadata` : Specifies whether or not if the operations metadata should be returned. To get the metadata, even if it is needed to recompute them, use `always`. To avoid getting the metadata, use `never`. By default, the metadata will be returned depending on the node's metadata size limit policy.
///
/// [`GET /chains/<chain_id>/blocks/<block_id>?[metadata=<metadata_rpc_arg>]`](https://tezos.gitlab.io/active/rpc.html#get-block-id)
pub fn get<HttpClient: Http>(ctx: &TezosRpcContext<HttpClient>) -> RpcRequestBuilder<HttpClient> {
    RpcRequestBuilder::new(ctx)
}

#[cfg(all(test, feature = "http"))]
mod tests {
    use {
        super::*,
        crate::{client::TezosRpc, error::Error, models::block::TestChainStatusName},
        httpmock::prelude::*,
    };

    #[tokio::test]
    async fn test_get_genesis_block() -> Result<(), Error> {
        let server = MockServer::start();
        let rpc_url = server.base_url();

        let block_id = BlockId::Genesis;

        server.mock(|when, then| {
            when.method(GET)
                .path(super::path(TezosRpcChainId::Main.value(), &block_id));
            then.status(200)
                .header("content-type", "application/json")
                .body(include_str!("block/__TEST_DATA__/block_genesis.json"));
        });
        let client = TezosRpc::new(rpc_url);

        let response = client
            .get_block()
            .block_id(&block_id)
            .metadata(super::MetadataArg::Always)
            .send()
            .await?;

        assert_eq!(
            response.protocol,
            "PrihK96nBAFSxVL1GLJTVhu9YnzkMFiBeuJRPA8NwuZVZCE1L6i"
                .try_into()
                .unwrap()
        );
        assert_eq!(response.chain_id, "NetXdQprcVkpaWU".try_into().unwrap());
        assert_eq!(
            response.hash,
            "BLockGenesisGenesisGenesisGenesisGenesisf79b5d1CoW2"
                .try_into()
                .unwrap()
        );
        assert_eq!(
            response.header.context,
            "CoV8SQumiVU9saiu3FVNeDNewJaJH8yWdsGF3WLdsRr2P9S7MzCj"
                .try_into()
                .unwrap()
        );

        let block_metadata = response.metadata.expect("Block has metadata");
        assert_eq!(
            block_metadata.protocol,
            "PrihK96nBAFSxVL1GLJTVhu9YnzkMFiBeuJRPA8NwuZVZCE1L6i"
                .try_into()
                .unwrap()
        );
        assert_eq!(block_metadata.baker, None);
        assert_eq!(
            block_metadata.test_chain_status.status,
            TestChainStatusName::NotRunning
        );

        assert_eq!(
            response.operations.len(),
            0,
            "No operations on genesis block."
        );

        Ok(())
    }

    #[tokio::test]
    async fn test_get_2nd_block() -> Result<(), Error> {
        let server = MockServer::start();
        let rpc_url = server.base_url();

        let block_id = BlockId::Level(1);

        server.mock(|when, then| {
            when.method(GET)
                .path(super::path(TezosRpcChainId::Main.value(), &block_id));
            then.status(200)
                .header("content-type", "application/json")
                .body(include_str!("block/__TEST_DATA__/block_1.json"));
        });
        let client = TezosRpc::new(rpc_url);

        client
            .get_block()
            .block_id(&block_id)
            .metadata(super::MetadataArg::Always)
            .send()
            .await?;

        Ok(())
    }

    #[tokio::test]
    async fn test_get_ithaca_block() -> Result<(), Error> {
        let server = MockServer::start();
        let rpc_url = server.base_url();

        let block_id = BlockId::Level(2490368);

        server.mock(|when, then| {
            when.method(GET)
                .path(super::path(TezosRpcChainId::Main.value(), &block_id));
            then.status(200)
                .header("content-type", "application/json")
                .body(include_str!("block/__TEST_DATA__/block_ithaca.json"));
        });
        let client = TezosRpc::new(rpc_url);

        client
            .get_block()
            .block_id(&block_id)
            .metadata(super::MetadataArg::Always)
            .send()
            .await?;

        Ok(())
    }

    #[tokio::test]
    async fn test_get_jakarta_block() -> Result<(), Error> {
        let server = MockServer::start();
        let rpc_url = server.base_url();

        let block_id = BlockId::Level(2504461);

        server.mock(|when, then| {
            when.method(GET)
                .path(super::path(TezosRpcChainId::Main.value(), &block_id));
            then.status(200)
                .header("content-type", "application/json")
                .body(include_str!("block/__TEST_DATA__/block_jakarta.json"));
        });
        let client = TezosRpc::new(rpc_url);

        let block = client
            .get_block()
            .block_id(&block_id)
            .metadata(super::MetadataArg::Always)
            .send()
            .await?;

        assert_eq!(block.operations[3].last().unwrap().contents.len(), 6);

        Ok(())
    }

    #[tokio::test]
    async fn test_get_tallinn_block() -> Result<(), Error> {
        use crate::models::operation::kind::OperationKind;
        use crate::models::operation::OperationContent;
        use tezos_core::types::encoded::{Encoded, ImplicitAddress};

        let server = MockServer::start();
        let rpc_url = server.base_url();

        let block_id = BlockId::Level(1839179);

        server.mock(|when, then| {
            when.method(GET)
                .path(super::path(TezosRpcChainId::Main.value(), &block_id));
            then.status(200)
                .header("content-type", "application/json")
                .body(include_str!("block/__TEST_DATA__/block_tallinn.json"));
        });
        let client = TezosRpc::new(rpc_url);

        let block = client
            .get_block()
            .block_id(&block_id)
            .metadata(super::MetadataArg::Always)
            .send()
            .await?;

        assert_eq!(
            block.protocol,
            "PtTALLiNtPec7mE7yY4m3k26J8Qukef3E3ehzhfXgFZKGtDdAXu"
                .try_into()
                .unwrap()
        );
        assert_eq!(block.chain_id, "NetXe8DbhW9A1eS".try_into().unwrap());
        assert_eq!(block.header.level, 1839179);
        assert_eq!(block.operations.len(), 4);

        let metadata = block.metadata.expect("Block has metadata");
        assert_eq!(
            metadata.next_protocol,
            "PtTALLiNtPec7mE7yY4m3k26J8Qukef3E3ehzhfXgFZKGtDdAXu"
                .try_into()
                .unwrap()
        );
        assert_eq!(
            metadata.baker,
            Some("tz1TnEtqDV9mZyts2pfMy6Jw1BTPs4LMjL8M".try_into().unwrap())
        );

        let consensus_ops = &block.operations[0];
        assert_eq!(consensus_ops.len(), 7);

        for op in consensus_ops.iter().flat_map(|o| o.contents.iter()) {
            assert!(
                !matches!(op, OperationContent::Unknown(_)),
                "Tallinn consensus operation deserialized as Unknown: {op:?}"
            );
        }

        let attestation_with_dal_count = consensus_ops
            .iter()
            .flat_map(|o| o.contents.iter())
            .filter(|c| {
                matches!(
                    c,
                    OperationContent::Endorsement(e) if e.kind == OperationKind::AttestationWithDal
                )
            })
            .count();
        assert_eq!(attestation_with_dal_count, 5);

        let plain_attestation_count = consensus_ops
            .iter()
            .flat_map(|o| o.contents.iter())
            .filter(|c| {
                matches!(
                    c,
                    OperationContent::Endorsement(e) if e.kind == OperationKind::Attestation
                )
            })
            .count();
        assert_eq!(plain_attestation_count, 1);

        let aggregate = consensus_ops
            .iter()
            .flat_map(|o| o.contents.iter())
            .find_map(|c| match c {
                OperationContent::AttestationsAggregate(agg) => Some(agg),
                _ => None,
            })
            .expect("attestations_aggregate present");
        assert_eq!(aggregate.kind, OperationKind::AttestationsAggregate);
        assert_eq!(aggregate.consensus_content.level, 1839178);
        assert_eq!(aggregate.committee.len(), 6);
        let agg_meta = aggregate
            .metadata
            .as_ref()
            .expect("aggregate metadata present");
        assert_eq!(agg_meta.committee.len(), 6);
        assert_eq!(
            agg_meta.total_consensus_power.baking_power.as_deref(),
            Some("749416333659474")
        );
        assert!(
            matches!(agg_meta.committee[0].consensus_pkh, ImplicitAddress::TZ4(_)),
            "expected committee[0].consensus_pkh to be a tz4 address, got {:?}",
            agg_meta.committee[0].consensus_pkh
        );

        let endorsement = consensus_ops
            .iter()
            .flat_map(|o| o.contents.iter())
            .find_map(|c| match c {
                OperationContent::Endorsement(e) if e.kind == OperationKind::AttestationWithDal => {
                    Some(e)
                }
                _ => None,
            })
            .expect("attestation_with_dal present");
        let consensus_power = endorsement
            .metadata
            .as_ref()
            .and_then(|m| m.consensus_power.as_ref())
            .expect("consensus_power present on attestation_with_dal");
        assert_eq!(consensus_power.slots, 439);
        assert_eq!(
            consensus_power.baking_power.as_deref(),
            Some("135574626860539")
        );

        let manager_ops = &block.operations[3];
        let dal_publish = manager_ops
            .iter()
            .flat_map(|o| o.contents.iter())
            .find_map(|c| match c {
                OperationContent::DalPublishCommitment(dp) => Some(dp),
                _ => None,
            })
            .expect("dal_publish_commitment present");
        assert_eq!(dal_publish.kind, OperationKind::DalPublishCommitment);
        assert_eq!(dal_publish.slot_header.slot_index, 8);

        let aggregate_signature = consensus_ops
            .iter()
            .find(|o| {
                o.contents
                    .iter()
                    .any(|c| matches!(c, OperationContent::AttestationsAggregate(_)))
            })
            .and_then(|o| o.signature.as_ref())
            .expect("aggregate signature present");
        let bls_bytes = aggregate_signature
            .to_bytes()
            .expect("BLS signature must round-trip to bytes");
        assert_eq!(bls_bytes.len(), 96);

        Ok(())
    }
}
