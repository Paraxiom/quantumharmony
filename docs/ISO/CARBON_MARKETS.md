# ISO/TC 307/AHG 4 Carbon Markets Specification

## Overview

This document outlines QuantumHarmony's preparation for participation in ISO/TC 307 Ad Hoc Group 4 (AHG 4) on blockchain-based carbon markets.

**Working Group:** ISO/TC 307/AHG 4 - Blockchain for carbon markets and environmental assets

**Status:** Preliminary design for future implementation

---

## Background

### AHG 4 Objectives

The ISO/TC 307/AHG 4 working group focuses on:

1. **Standardizing** digital carbon credit representation on DLT
2. **Interoperability** between carbon registries
3. **Transparency** in carbon credit lifecycle
4. **Verification** mechanisms for emission reductions
5. **Prevention** of double-counting across jurisdictions

### Alignment with UN SDGs

| SDG | Target | QH Contribution |
|-----|--------|-----------------|
| SDG 7 | Clean Energy | Energy-efficient consensus (post-quantum, no PoW) |
| SDG 12 | Responsible Consumption | Supply chain tracking via attestations |
| SDG 13 | Climate Action | Carbon credit tokenization and tracking |
| SDG 17 | Partnerships | Open standards, cross-chain interoperability |

---

## Proposed Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    CARBON MARKETS ARCHITECTURE                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                      EXTERNAL REGISTRIES                             │    │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐            │    │
│  │  │  Verra   │  │Gold Std. │  │ CAR      │  │  ACR     │            │    │
│  │  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘            │    │
│  │       │             │             │             │                   │    │
│  └───────┼─────────────┼─────────────┼─────────────┼───────────────────┘    │
│          │             │             │             │                        │
│          ▼             ▼             ▼             ▼                        │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                      ORACLE BRIDGE LAYER                             │    │
│  │  • Registry API integrations                                        │    │
│  │  • Credit verification oracles                                       │    │
│  │  • Price feed oracles                                                │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                      PALLET-CARBON-CREDITS                           │    │
│  │                                                                       │    │
│  │  Storage:                                                            │    │
│  │  ├── CarbonCredits: Map<CreditId, CarbonCredit>                     │    │
│  │  ├── Projects: Map<ProjectId, CarbonProject>                        │    │
│  │  ├── Retirements: Map<RetirementId, Retirement>                     │    │
│  │  └── Balances: Map<(AccountId, CreditType), Balance>                │    │
│  │                                                                       │    │
│  │  Extrinsics:                                                         │    │
│  │  ├── register_project()                                             │    │
│  │  ├── issue_credits()                                                │    │
│  │  ├── transfer_credits()                                             │    │
│  │  ├── retire_credits()                                               │    │
│  │  └── verify_retirement()                                            │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                      APPLICATIONS                                    │    │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │    │
│  │  │ Carbon       │  │ Enterprise   │  │ Compliance   │              │    │
│  │  │ Marketplace  │  │ Offsetting   │  │ Reporting    │              │    │
│  │  └──────────────┘  └──────────────┘  └──────────────┘              │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

### Carbon Credit Token

```rust
/// ISO/TC 307/AHG 4 Compliant Carbon Credit
///
/// Represents a verified emission reduction or removal unit.
#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub struct CarbonCredit<AccountId, BlockNumber> {
    /// Unique identifier (registry + serial number)
    pub credit_id: CreditId,

    /// Associated carbon project
    pub project_id: ProjectId,

    /// Credit type classification
    pub credit_type: CreditType,

    /// Vintage year (when reduction occurred)
    pub vintage_year: u16,

    /// Quantity in tonnes CO2e (with 3 decimal precision)
    pub quantity_millitonnes: u64,

    /// Current owner
    pub owner: AccountId,

    /// Issuing registry
    pub registry: Registry,

    /// Verification standard
    pub standard: VerificationStandard,

    /// Status in lifecycle
    pub status: CreditStatus,

    /// Block when issued on-chain
    pub issued_at: BlockNumber,

    /// Original registry serial numbers
    pub registry_serial: BoundedVec<u8, ConstU32<64>>,

    /// IPFS hash of supporting documentation
    pub documentation_cid: Option<[u8; 32]>,
}

#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub enum CreditType {
    /// Emission reduction (avoided emissions)
    Reduction,
    /// Carbon removal (sequestration)
    Removal,
    /// Avoidance (prevented emissions)
    Avoidance,
}

#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub enum CreditStatus {
    /// Active and tradeable
    Active,
    /// Locked for pending transaction
    Locked,
    /// Permanently retired (offset claim)
    Retired,
    /// Cancelled (e.g., reversal, error)
    Cancelled,
}

#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub enum Registry {
    Verra,
    GoldStandard,
    ClimateActionReserve,
    AmericanCarbonRegistry,
    CleanDevelopmentMechanism,
    Other(BoundedVec<u8, ConstU32<32>>),
}

#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub enum VerificationStandard {
    VCS,           // Verified Carbon Standard
    GS,            // Gold Standard
    CDM,           // Clean Development Mechanism
    CORSIA,        // Carbon Offsetting Scheme for Intl Aviation
    ArticleSix,    // Paris Agreement Article 6
    Other(BoundedVec<u8, ConstU32<32>>),
}
```

### Carbon Project

```rust
/// Carbon Project Metadata
#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub struct CarbonProject<AccountId> {
    pub project_id: ProjectId,

    /// Project name
    pub name: BoundedVec<u8, ConstU32<128>>,

    /// Project type/methodology
    pub project_type: ProjectType,

    /// Geographic location (ISO 3166-1 alpha-3)
    pub country: [u8; 3],

    /// Project developer/proponent
    pub developer: AccountId,

    /// Registry project ID
    pub registry_id: BoundedVec<u8, ConstU32<64>>,

    /// Crediting period start
    pub crediting_start: u16,  // Year

    /// Crediting period end
    pub crediting_end: u16,    // Year

    /// Total expected credits (lifetime)
    pub expected_credits_millitonnes: u64,

    /// SDG contributions (bitmap of 17 SDGs)
    pub sdg_contributions: u32,

    /// Verification body
    pub verifier: BoundedVec<u8, ConstU32<64>>,
}

#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub enum ProjectType {
    Forestry,
    Renewable,
    EnergyEfficiency,
    WasteManagement,
    Agriculture,
    IndustrialGas,
    Transport,
    BlueCarbon,
    DirectAirCapture,
    Other(BoundedVec<u8, ConstU32<32>>),
}
```

### Retirement Record

```rust
/// Immutable Retirement Record
///
/// Created when credits are permanently retired for offsetting.
#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub struct Retirement<AccountId, BlockNumber> {
    pub retirement_id: RetirementId,

    /// Credits retired
    pub credit_ids: BoundedVec<CreditId, ConstU32<100>>,

    /// Total quantity retired
    pub quantity_millitonnes: u64,

    /// Beneficiary of the offset
    pub beneficiary: RetirementBeneficiary<AccountId>,

    /// Reason for retirement
    pub reason: RetirementReason,

    /// Retirement year (for accounting)
    pub retirement_year: u16,

    /// Block when retired
    pub retired_at: BlockNumber,

    /// Retiring account
    pub retired_by: AccountId,

    /// Certificate hash (if issued)
    pub certificate_cid: Option<[u8; 32]>,
}

#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub enum RetirementBeneficiary<AccountId> {
    /// Specific on-chain account
    Account(AccountId),
    /// Named organization (off-chain)
    Organization(BoundedVec<u8, ConstU32<128>>),
    /// General/unspecified
    General,
}

#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub enum RetirementReason {
    /// Corporate sustainability commitment
    CorporateOffset,
    /// Regulatory compliance (e.g., CORSIA)
    Compliance,
    /// Voluntary individual offset
    VoluntaryIndividual,
    /// Event offsetting
    EventOffset,
    /// Product carbon neutrality
    ProductNeutrality,
    /// Other specified reason
    Other(BoundedVec<u8, ConstU32<64>>),
}
```

---

## Pallet Interface

### Extrinsics

```rust
#[pallet::call]
impl<T: Config> Pallet<T> {
    /// Register a new carbon project
    ///
    /// # Requirements
    /// - Caller must be approved project developer
    /// - Project must be verified by recognized registry
    #[pallet::call_index(0)]
    pub fn register_project(
        origin: OriginFor<T>,
        project: CarbonProject<T::AccountId>,
        verification_proof: VerificationProof,
    ) -> DispatchResult;

    /// Issue credits from verified project
    ///
    /// # Requirements
    /// - Caller must be project developer
    /// - Must have oracle confirmation from registry
    /// - Vintage and quantity must match registry issuance
    #[pallet::call_index(1)]
    pub fn issue_credits(
        origin: OriginFor<T>,
        project_id: ProjectId,
        vintage_year: u16,
        quantity_millitonnes: u64,
        registry_serials: Vec<RegistrySerial>,
    ) -> DispatchResult;

    /// Transfer credits between accounts
    ///
    /// # Requirements
    /// - Caller must own the credits
    /// - Credits must be Active status
    /// - Recipient must have valid account
    #[pallet::call_index(2)]
    pub fn transfer_credits(
        origin: OriginFor<T>,
        credit_ids: Vec<CreditId>,
        recipient: T::AccountId,
    ) -> DispatchResult;

    /// Retire credits for offset claim
    ///
    /// # Requirements
    /// - Caller must own the credits
    /// - Credits must be Active status
    /// - Creates permanent, immutable retirement record
    #[pallet::call_index(3)]
    pub fn retire_credits(
        origin: OriginFor<T>,
        credit_ids: Vec<CreditId>,
        beneficiary: RetirementBeneficiary<T::AccountId>,
        reason: RetirementReason,
        retirement_year: u16,
    ) -> DispatchResult;

    /// Request retirement verification certificate
    ///
    /// Generates verifiable certificate for off-chain use
    #[pallet::call_index(4)]
    pub fn request_certificate(
        origin: OriginFor<T>,
        retirement_id: RetirementId,
    ) -> DispatchResult;
}
```

### Events

```rust
#[pallet::event]
pub enum Event<T: Config> {
    /// Project registered on-chain
    ProjectRegistered {
        project_id: ProjectId,
        developer: T::AccountId,
        registry: Registry,
    },

    /// Credits issued from project
    CreditsIssued {
        project_id: ProjectId,
        credit_ids: Vec<CreditId>,
        quantity_millitonnes: u64,
        vintage_year: u16,
    },

    /// Credits transferred
    CreditsTransferred {
        credit_ids: Vec<CreditId>,
        from: T::AccountId,
        to: T::AccountId,
    },

    /// Credits retired (permanent)
    CreditsRetired {
        retirement_id: RetirementId,
        credit_ids: Vec<CreditId>,
        quantity_millitonnes: u64,
        beneficiary: RetirementBeneficiary<T::AccountId>,
    },

    /// Retirement certificate generated
    CertificateIssued {
        retirement_id: RetirementId,
        certificate_cid: [u8; 32],
    },
}
```

---

## Oracle Integration

### Registry Verification Oracle

```rust
/// Oracle feed for registry verification
pub struct RegistryOracleFeed {
    /// Feed identifier
    feed_id: "carbon:registry:verification",

    /// Data format
    data: RegistryVerification {
        registry: Registry,
        project_id: RegistryProjectId,
        serial_numbers: Vec<SerialNumber>,
        quantity_tonnes: Decimal,
        vintage: u16,
        status: VerificationStatus,
        timestamp: u64,
    },
}
```

### Price Oracle

```rust
/// Oracle feed for carbon credit prices
pub struct CarbonPriceOracleFeed {
    /// Feed identifier (e.g., "carbon:price:VCS:Nature")
    feed_id: String,

    /// Price data
    data: CarbonPrice {
        credit_type: CreditType,
        standard: VerificationStandard,
        project_type: ProjectType,
        price_usd_cents: u64,  // Price per tonne in USD cents
        volume_24h_tonnes: u64,
        sources: Vec<String>,
        timestamp: u64,
    },
}
```

---

## Interoperability

### Cross-Registry Bridging

```
┌─────────────────────────────────────────────────────────────────┐
│                    REGISTRY BRIDGE FLOW                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  1. Lock credits in source registry                             │
│     └── Registry Oracle confirms lock                           │
│                                                                  │
│  2. Mint bridged credits on QuantumHarmony                      │
│     └── Maintains link to source registry serial                │
│                                                                  │
│  3. Trade/transfer on-chain                                     │
│     └── Full on-chain provenance                                │
│                                                                  │
│  4. Retirement or bridge back                                   │
│     ├── Retire: Permanent on-chain record                       │
│     └── Bridge: Burn on QH, unlock in registry                  │
│                                                                  │
│  DOUBLE-COUNTING PREVENTION:                                    │
│  • Unique serial mapping: 1 registry credit = 1 on-chain token  │
│  • Lock verification before minting                             │
│  • Retirement synced back to registry                           │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Article 6 Corresponding Adjustments

For credits traded under Paris Agreement Article 6:

```rust
/// Article 6 Corresponding Adjustment Tracking
pub struct CorrespondingAdjustment {
    /// Transferring country (ISO 3166-1 alpha-3)
    pub from_country: [u8; 3],

    /// Acquiring country
    pub to_country: [u8; 3],

    /// Credits transferred
    pub credit_ids: Vec<CreditId>,

    /// Quantity in tonnes CO2e
    pub quantity_tonnes: u64,

    /// Year for NDC accounting
    pub adjustment_year: u16,

    /// Authorization reference
    pub authorization_ref: BoundedVec<u8, ConstU32<64>>,
}
```

---

## Compliance Considerations

### Regulatory Alignment

| Regulation | Requirement | QH Implementation |
|------------|-------------|-------------------|
| EU ETS | Registry linkage | Oracle bridge to EU Transaction Log |
| CORSIA | Eligible units tracking | Standard field in CarbonCredit |
| California Cap-and-Trade | ARB compliance | Registry field support |
| Voluntary markets | Transparency | Full on-chain provenance |

### Audit Trail

All operations emit events with:
- Timestamp (block number)
- Actor (signed account)
- Previous state
- New state
- External references (registry serials, etc.)

---

## Implementation Roadmap

| Phase | Timeline | Deliverables |
|-------|----------|--------------|
| 1 | Q2 2026 | Data model finalization, pallet skeleton |
| 2 | Q3 2026 | Oracle integrations (Verra, Gold Standard) |
| 3 | Q4 2026 | Testnet deployment, audit |
| 4 | Q1 2027 | Mainnet launch, first projects |

---

## References

- [ISO/TC 307/AHG 4](https://www.iso.org/committee/6266604.html) - Carbon Markets Working Group
- [Paris Agreement Article 6](https://unfccc.int/process-and-meetings/the-paris-agreement/article-64-mechanism)
- [Verra Registry](https://registry.verra.org/)
- [Gold Standard Registry](https://registry.goldstandard.org/)
- [ICAO CORSIA](https://www.icao.int/environmental-protection/CORSIA)
