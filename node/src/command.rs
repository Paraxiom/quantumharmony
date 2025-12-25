// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use futures::TryFutureExt;
// Substrate
use sc_cli::{ChainSpec, SubstrateCli};
use sc_service::DatabaseSource;
// FRONTIER REMOVED: governance-only node
// // Frontier
// use fc_db::kv::frontier_database_dir;

use crate::{
    chain_spec,
    cli::{Cli, Subcommand},
    // FRONTIER REMOVED: governance-only node
    // service::{self, db_config_dir},
    service,
};

#[cfg(feature = "runtime-benchmarks")]
use crate::chain_spec::get_account_id_from_seed;

impl SubstrateCli for Cli {
    fn impl_name() -> String {
        "quantumharmony Node".into()
    }

    fn impl_version() -> String {
        env!("SUBSTRATE_CLI_IMPL_VERSION").into()
    }

    fn description() -> String {
        env!("CARGO_PKG_DESCRIPTION").into()
    }

    fn author() -> String {
        env!("CARGO_PKG_AUTHORS").into()
    }

    fn support_url() -> String {
        "support.anonymous.an".into()
    }

    fn copyright_start_year() -> i32 {
        2021
    }

    fn load_spec(&self, id: &str) -> Result<Box<dyn ChainSpec>, String> {
        Ok(match id {
            "dev" => {
                let enable_manual_seal = self.sealing.map(|_| true).unwrap_or_default();
                Box::new(chain_spec::development_config(enable_manual_seal))
            }
            "dev3" => Box::new(chain_spec::dev_3validators_config()),
            "prod3" => {
                // Production 3-validator network with actual SPHINCS+ keys
                // Keys generated from quantumharmony-validator-keys-v2
                Box::new(chain_spec::production_3validators_config(
                    "80393d87b88dece50bb28212ed23619c2a8565021d5844226b7f265d45cfa225045080aac4ba5b82725545e2c0bea5120a6a30ffb7737f1f2f9f3415875ebf45",
                    "5712c6ddc0e1fa5c33a501fd020300d0a5317c364524b50153d97c2a62d6fe3856a80d584bffb96c3e64dc32d91748dd2be15956e4281f32db3d3cca6413aac3",
                    "b117e681f1e1e0e82fa47e1a6c1ed90da59633c4e43ad797e26794905a94f3da9ed09995d50b70bb955ca9025ed5a3744e60426e432c8ca7dddc14cb41e7b845",
                ))
            }
            "" | "local" => Box::new(chain_spec::local_testnet_config()),
            "testnet" => Box::new(chain_spec::testnet_config()),
            path => Box::new(chain_spec::ChainSpec::from_json_file(
                std::path::PathBuf::from(path),
            )?),
        })
    }
}

/// Parse and run command line arguments
pub fn run() -> sc_cli::Result<()> {
    let cli = Cli::from_args();

    match &cli.subcommand {
        Some(Subcommand::SphincsKey(cmd)) => {
            cmd.run().map_err(|e| sc_cli::Error::Application(e.into()))
        }
        Some(Subcommand::Key(cmd)) => cmd.run(&cli),
        Some(Subcommand::BuildSpec(cmd)) => {
            let runner = cli.create_runner(cmd)?;
            runner.sync_run(|config| cmd.run(config.chain_spec, config.network))
        }
        // FRONTIER REMOVED: governance-only node
        // Some(Subcommand::CheckBlock(cmd)) => {
        //     let runner = cli.create_runner(cmd)?;
        //     runner.async_run(|mut config| {
        //         let (client, _, import_queue, task_manager, _) =
        //             service::new_chain_ops(&mut config, &cli.eth)?;
        //         Ok((cmd.run(client, import_queue), task_manager))
        //     })
        // }
        // Some(Subcommand::ExportBlocks(cmd)) => {
        //     let runner = cli.create_runner(cmd)?;
        //     runner.async_run(|mut config| {
        //         let (client, _, _, task_manager, _) =
        //             service::new_chain_ops(&mut config, &cli.eth)?;
        //         Ok((cmd.run(client, config.database), task_manager))
        //     })
        // }
        // Some(Subcommand::ExportState(cmd)) => {
        //     let runner = cli.create_runner(cmd)?;
        //     runner.async_run(|mut config| {
        //         let (client, _, _, task_manager, _) =
        //             service::new_chain_ops(&mut config, &cli.eth)?;
        //         Ok((cmd.run(client, config.chain_spec), task_manager))
        //     })
        // }
        // Some(Subcommand::ImportBlocks(cmd)) => {
        //     let runner = cli.create_runner(cmd)?;
        //     runner.async_run(|mut config| {
        //         let (client, _, import_queue, task_manager, _) =
        //             service::new_chain_ops(&mut config, &cli.eth)?;
        //         Ok((cmd.run(client, import_queue), task_manager))
        //     })
        // }
        Some(Subcommand::PurgeChain(cmd)) => {
            let runner = cli.create_runner(cmd)?;
            runner.sync_run(|config| {
                // FRONTIER REMOVED: governance-only node
                // // Remove Frontier offchain db
                // let db_config_dir = db_config_dir(&config);
                // match cli.eth.frontier_backend_type {
                //     crate::eth::BackendType::KeyValue => {
                //         let frontier_database_config = match config.database {
                //             DatabaseSource::RocksDb { .. } => DatabaseSource::RocksDb {
                //                 path: frontier_database_dir(&db_config_dir, "db"),
                //                 cache_size: 0,
                //             },
                //             DatabaseSource::ParityDb { .. } => DatabaseSource::ParityDb {
                //                 path: frontier_database_dir(&db_config_dir, "paritydb"),
                //             },
                //             _ => {
                //                 return Err(format!(
                //                     "Cannot purge `{:?}` database",
                //                     config.database
                //                 )
                //                 .into())
                //             }
                //         };
                //         cmd.run(frontier_database_config)?;
                //     }
                //     crate::eth::BackendType::Sql => {
                //         let db_path = db_config_dir.join("sql");
                //         match std::fs::remove_dir_all(&db_path) {
                //             Ok(_) => {
                //                 println!("{:?} removed.", &db_path);
                //             }
                //             Err(ref err) if err.kind() == std::io::ErrorKind::NotFound => {
                //                 eprintln!("{:?} did not exist.", &db_path);
                //             }
                //             Err(err) => {
                //                 return Err(format!(
                //                     "Cannot purge `{:?}` database: {:?}",
                //                     db_path, err,
                //                 )
                //                 .into())
                //             }
                //         };
                //     }
                // };
                cmd.run(config.database)
            })
        }
        // FRONTIER REMOVED: governance-only node
        // Some(Subcommand::Revert(cmd)) => {
        //     let runner = cli.create_runner(cmd)?;
        //     runner.async_run(|mut config| {
        //         let (client, backend, _, task_manager, _) =
        //             service::new_chain_ops(&mut config, &cli.eth)?;
        //         let aux_revert = Box::new(move |client, _, blocks| {
        //             sc_consensus_grandpa::revert(client, blocks)?;
        //             Ok(())
        //         });
        //         Ok((cmd.run(client, backend, Some(aux_revert)), task_manager))
        //     })
        // }
        // FRONTIER REMOVED: governance-only node
        // #[cfg(feature = "runtime-benchmarks")]
        // Some(Subcommand::Benchmark(cmd)) => {
        //     use crate::benchmarking::{
        //         inherent_benchmark_data, RemarkBuilder, TransferKeepAliveBuilder,
        //     };
        //     use frame_benchmarking_cli::{
        //         BenchmarkCmd, ExtrinsicFactory, SUBSTRATE_REFERENCE_HARDWARE,
        //     };
        //     use quantumharmony_runtime::{ExistentialDeposit, Hashing};
        //
        //     let runner = cli.create_runner(cmd)?;
        //     match cmd {
        //         BenchmarkCmd::Pallet(cmd) => {
        //             runner.sync_run(|config| cmd.run::<Hashing, ()>(config))
        //         }
        //         BenchmarkCmd::Block(cmd) => runner.sync_run(|mut config| {
        //             let (client, _, _, _, _) = service::new_chain_ops(&mut config, &cli.eth)?;
        //             cmd.run(client)
        //         }),
        //         BenchmarkCmd::Storage(cmd) => runner.sync_run(|mut config| {
        //             let (client, backend, _, _, _) = service::new_chain_ops(&mut config, &cli.eth)?;
        //             let db = backend.expose_db();
        //             let storage = backend.expose_storage();
        //             cmd.run(config, client, db, storage)
        //         }),
        //         BenchmarkCmd::Overhead(cmd) => runner.sync_run(|mut config| {
        //             let (client, _, _, _, _) = service::new_chain_ops(&mut config, &cli.eth)?;
        //             let ext_builder = RemarkBuilder::new(client.clone());
        //             cmd.run(
        //                 config,
        //                 client,
        //                 inherent_benchmark_data()?,
        //                 Vec::new(),
        //                 &ext_builder,
        //             )
        //         }),
        //         BenchmarkCmd::Extrinsic(cmd) => runner.sync_run(|mut config| {
        //             let (client, _, _, _, _) = service::new_chain_ops(&mut config, &cli.eth)?;
        //             // Register the *Remark* and *TKA* builders.
        //             let ext_factory = ExtrinsicFactory(vec![
        //                 Box::new(RemarkBuilder::new(client.clone())),
        //                 Box::new(TransferKeepAliveBuilder::new(
        //                     client.clone(),
        //                     get_account_id_from_seed::<sp_core::ecdsa::Public>("Alice"),
        //                     ExistentialDeposit::get(),
        //                 )),
        //             ]);
        //
        //             cmd.run(client, inherent_benchmark_data()?, Vec::new(), &ext_factory)
        //         }),
        //         BenchmarkCmd::Machine(cmd) => {
        //             runner.sync_run(|config| cmd.run(&config, SUBSTRATE_REFERENCE_HARDWARE.clone()))
        //         }
        //     }
        // }
        #[cfg(not(feature = "runtime-benchmarks"))]
        Some(Subcommand::Benchmark) => Err("Benchmarking wasn't enabled when building the node. \
			You can enable it with `--features runtime-benchmarks`."
            .into()),
        None => {
            let runner = cli.create_runner(&cli.run)?;

            // Build PQTG configuration from CLI flags - only if devices are specified
            // When no devices are configured, pass None to use mock device shares for finalization
            let pqtg_config = if cli.pqtg_devices.is_some() {
                Some(service::PqtgConfiguration {
                    endpoint: cli.pqtg_endpoint.clone(),
                    qkd_mode: cli.qkd_mode.clone(),
                    devices: cli.pqtg_devices.clone(),
                    threshold_k: cli.pqtg_threshold_k,
                })
            } else {
                log::info!("No PQTG devices configured - using mock finality mode");
                None
            };

            runner.run_node_until_exit(|config| async move {
                service::build_full(config, pqtg_config)
                    .map_err(Into::into)
                    .await
            })
        }
        _ => Err("Unsupported subcommand".into())
    }
}
