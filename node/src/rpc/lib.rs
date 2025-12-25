use jsonrpc_derive::rpc;
use sp_core::H256;
use sp_runtime::traits::Block as BlockT;
use substrate_validator_set::AccountId;
use std::sync::Arc;

#[rpc]
pub trait LeaderRpc {
    #[rpc(name = "current_leader")]
    fn current_leader(&self) -> Result<Option<AccountId>, jsonrpc_core::Error>;
}

pub struct LeaderRpcImpl<C, M> {
    client: Arc<C>,
    _marker: std::marker::PhantomData<M>,
}

impl<C, Block> LeaderRpcImpl<C, Block>
where
    Block: BlockT,
    C: Send + Sync + 'static + ProvideRuntimeApi<Block>,
    C::Api: LeaderApi<Block>,
{
    pub fn new(client: Arc<C>) -> Self {
        Self {
            client,
            _marker: Default::default(),
        }
    }
}

impl<C, Block> LeaderRpc for LeaderRpcImpl<C, Block>
where
    Block: BlockT,
    C: Send + Sync + 'static + ProvideRuntimeApi<Block>,
    C::Api: LeaderApi<Block>,
{
    fn current_leader(&self) -> Result<Option<AccountId>, jsonrpc_core::Error> {
        let api = self.client.runtime_api();
        let at = BlockId::hash(self.client.info().best_hash);

        api.current_leader(&at).map_err(|e| {
            jsonrpc_core::Error::new(jsonrpc_core::ErrorCode::ServerError(1))
                .data(format!("{:?}", e))
        })
    }
}
