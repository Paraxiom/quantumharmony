# QuantumHarmony Cloud Deployment Plan

**Date**: November 19, 2025
**Purpose**: Deploy 3-validator testnet to cloud infrastructure
**Goal**: Bypass Substrate localhost bug and achieve working multi-validator consensus

---

## 🎯 Deployment Requirements

### Hardware Per Validator

Based on toroidal mesh architecture requirements:

| Component | Specification | Reasoning |
|-----------|--------------|-----------|
| **CPU** | 8 cores (16 recommended) | Toroidal mesh parallel processing |
| **RAM** | 16 GB minimum (32 GB recommended) | Mesh state + runtime |
| **Storage** | 100 GB SSD | Fast state access, blockchain data |
| **Network** | 1 Gbps+ | Block propagation, P2P gossip |
| **OS** | Ubuntu 22.04 LTS | Stable, well-supported |

### Network Ports

| Port | Protocol | Purpose | Security |
|------|----------|---------|----------|
| **30333** | TCP | P2P libp2p networking | Public |
| **9944** | WebSocket | JSON-RPC (legacy) | Firewall (optional) |
| **9933** | HTTP | HTTP RPC (optional) | Firewall |
| **5555-5557** | TCP | Priority Queue RPC | Firewall recommended |

---

## ☁️ Cloud Provider Comparison

### Option 1: **AWS (Amazon Web Services)**

**Recommended Instance**: `c6i.2xlarge`
- **vCPU**: 8 cores
- **RAM**: 16 GB
- **Network**: Up to 12.5 Gbps
- **Cost**: ~$0.34/hour × 3 = **$1.02/hour** (~$734/month)

**Pros**:
- ✅ Industry leader, very reliable
- ✅ Global data centers
- ✅ Excellent documentation
- ✅ Advanced networking (VPC, security groups)
- ✅ Auto-scaling available

**Cons**:
- ❌ Most expensive option
- ❌ Complex pricing structure
- ❌ Learning curve for AWS console

**Setup**:
```bash
# Install AWS CLI
brew install awscli  # macOS
aws configure

# Launch EC2 instances (3 validators)
aws ec2 run-instances \
  --image-id ami-0c55b159cbfafe1f0 \
  --instance-type c6i.2xlarge \
  --count 3 \
  --key-name quantumharmony-key \
  --security-group-ids sg-xxxxxx \
  --tag-specifications 'ResourceType=instance,Tags=[{Key=Name,Value=QuantumHarmony-Alice}]'
```

---

### Option 2: **Google Cloud Platform (GCP)**

**Recommended Instance**: `n2-standard-8`
- **vCPU**: 8 cores
- **RAM**: 32 GB
- **Network**: 16 Gbps
- **Cost**: ~$0.39/hour × 3 = **$1.17/hour** (~$842/month)

**Pros**:
- ✅ Excellent network performance
- ✅ Good pricing for sustained use (discounts after 30 days)
- ✅ Simple UI
- ✅ Strong Kubernetes support

**Cons**:
- ❌ Slightly more expensive than AWS
- ❌ Fewer data center options

**Setup**:
```bash
# Install gcloud CLI
brew install google-cloud-sdk
gcloud init

# Create instances
gcloud compute instances create quantumharmony-alice \
  --machine-type=n2-standard-8 \
  --image-family=ubuntu-2204-lts \
  --image-project=ubuntu-os-cloud \
  --boot-disk-size=100GB \
  --boot-disk-type=pd-ssd \
  --tags=quantumharmony-validator
```

---

### Option 3: **DigitalOcean** (⭐ RECOMMENDED)

**Recommended Droplet**: `c2-8vcpu-16gb`
- **vCPU**: 8 dedicated cores
- **RAM**: 16 GB
- **SSD**: 100 GB
- **Network**: Unlimited transfer
- **Cost**: ~$96/month × 3 = **$288/month**

**Pros**:
- ✅ **Best price/performance ratio**
- ✅ Simple, predictable pricing
- ✅ Easy-to-use dashboard
- ✅ Excellent documentation
- ✅ Fast SSD storage
- ✅ Free bandwidth (no egress charges)
- ✅ Managed Kubernetes available

**Cons**:
- ❌ Fewer advanced features than AWS/GCP
- ❌ Fewer data center locations

**Setup**:
```bash
# Install doctl CLI
brew install doctl
doctl auth init

# Create droplets
doctl compute droplet create quantumharmony-alice \
  --image ubuntu-22-04-x64 \
  --size c2-8vcpu-16gb \
  --region nyc3 \
  --ssh-keys YOUR_SSH_KEY_ID \
  --tag-names quantumharmony-validator
```

---

### Option 4: **Hetzner Cloud** (💰 BUDGET OPTION)

**Recommended Server**: `CCX33`
- **vCPU**: 8 dedicated AMD cores
- **RAM**: 32 GB
- **NVMe**: 240 GB
- **Network**: 20 TB traffic
- **Cost**: €27.90/month × 3 = **€83.70/month (~$90/month)**

**Pros**:
- ✅ **Cheapest option** (70% cheaper than AWS!)
- ✅ Dedicated CPU cores (not shared)
- ✅ Fast NVMe storage
- ✅ European data centers (GDPR compliant)
- ✅ Simple pricing

**Cons**:
- ❌ Limited to European + US locations
- ❌ Less mature than AWS/GCP
- ❌ Smaller ecosystem

**Setup**:
```bash
# Install hcloud CLI
brew install hcloud
hcloud context create quantumharmony

# Create servers
hcloud server create \
  --name quantumharmony-alice \
  --type ccx33 \
  --image ubuntu-22.04 \
  --ssh-key quantumharmony-key \
  --location nbg1
```

---

## 📊 Cost Comparison (3 Validators, 1 Month)

| Provider | Instance Type | RAM | Monthly Cost | Notes |
|----------|--------------|-----|--------------|-------|
| **Hetzner** | CCX33 | 32 GB | **$90** | 🥇 Best value |
| **DigitalOcean** | c2-8vcpu-16gb | 16 GB | **$288** | 🥈 Recommended |
| **AWS** | c6i.2xlarge | 16 GB | **$734** | Enterprise-grade |
| **GCP** | n2-standard-8 | 32 GB | **$842** | Good performance |

---

## 🏆 Recommendation

### For Development/Testing: **DigitalOcean**
- **Cost**: $288/month
- **Ease of use**: Excellent
- **Performance**: More than sufficient
- **Setup time**: < 1 hour

### For Production/Enterprise: **AWS**
- **Cost**: $734/month
- **Reliability**: Industry-leading
- **Scalability**: Unlimited
- **Support**: 24/7 enterprise support available

### For Budget-Conscious: **Hetzner**
- **Cost**: $90/month
- **Performance**: Excellent (dedicated cores)
- **Location**: Europe-focused
- **Risk**: Smaller provider, less enterprise support

---

## 🚀 Deployment Architecture

### Network Topology

```
┌─────────────────────────────────────────────┐
│         Internet (Public IPs)               │
└──────┬──────────────┬──────────────┬────────┘
       │              │              │
   ┌───▼───┐      ┌───▼───┐      ┌───▼───┐
   │ Alice │      │  Bob  │      │Charlie│
   │NYC1   │      │NYC2   │      │NYC3   │
   │IP1    │      │IP2    │      │IP3    │
   └───┬───┘      └───┬───┘      └───┬───┘
       │              │              │
       └──────────────┼──────────────┘
              P2P Mesh Network
           (libp2p on port 30333)
```

### Firewall Rules

**Alice (Bootnode)**:
```
Inbound:
  - 22 (SSH) from YOUR_IP only
  - 30333 (P2P) from 0.0.0.0/0
  - 9944 (RPC) from YOUR_IP only
  - 5555 (PQ-RPC) from YOUR_IP only

Outbound:
  - ALL
```

**Bob & Charlie**:
```
Inbound:
  - 22 (SSH) from YOUR_IP only
  - 30333 (P2P) from Alice + each other
  - 9944 (RPC) from YOUR_IP only
  - 5556/5557 (PQ-RPC) from YOUR_IP only

Outbound:
  - ALL
```

---

## 📝 Deployment Checklist

### Pre-Deployment
- [ ] Select cloud provider (Recommended: DigitalOcean)
- [ ] Create cloud account
- [ ] Set up SSH keys
- [ ] Configure payment method
- [ ] Choose data center regions (close together for low latency)

### Instance Setup
- [ ] Create 3 VM instances
- [ ] Assign static/reserved IPs
- [ ] Configure firewall rules
- [ ] Set up SSH access
- [ ] Install Docker on each instance
- [ ] Test SSH connectivity

### Blockchain Deployment
- [ ] Copy quantumharmony-node binary to each VM
- [ ] Generate chain spec with correct validator keys
- [ ] Configure Alice as bootnode
- [ ] Start Alice validator
- [ ] Get Alice's peer ID
- [ ] Configure Bob/Charlie to connect to Alice
- [ ] Start Bob and Charlie validators
- [ ] Verify block production
- [ ] Test priority queue RPC endpoints

### Monitoring
- [ ] Set up logging (journalctl or external service)
- [ ] Monitor block production
- [ ] Check peer connections
- [ ] Verify priority queue RPC working
- [ ] Monitor resource usage (CPU, RAM, disk)

---

## 🔧 Quick Start Commands

### 1. DigitalOcean Deployment (Recommended)

```bash
# Install CLI
brew install doctl
doctl auth init

# Create SSH key
ssh-keygen -t ed25519 -f ~/.ssh/quantumharmony_ed25519
doctl compute ssh-key import quantumharmony-key \
  --public-key-file ~/.ssh/quantumharmony_ed25519.pub

# Get SSH key ID
doctl compute ssh-key list

# Create 3 droplets
for validator in alice bob charlie; do
  doctl compute droplet create quantumharmony-$validator \
    --image ubuntu-22-04-x64 \
    --size c2-8vcpu-16gb \
    --region nyc3 \
    --ssh-keys YOUR_SSH_KEY_ID \
    --tag-names quantumharmony-validator \
    --wait
done

# Get IP addresses
doctl compute droplet list --tag-name quantumharmony-validator
```

### 2. Install Docker on Each VM

```bash
# SSH into each validator
ssh root@VALIDATOR_IP

# Install Docker
curl -fsSL https://get.docker.com -o get-docker.sh
sh get-docker.sh
docker --version

# Install Docker Compose
sudo curl -L "https://github.com/docker/compose/releases/latest/download/docker-compose-$(uname -s)-$(uname -m)" -o /usr/local/bin/docker-compose
sudo chmod +x /usr/local/bin/docker-compose
```

### 3. Deploy QuantumHarmony

```bash
# On your local machine, build and copy binary
cargo build --release -p quantumharmony-node

# Copy to each validator
scp target/release/quantumharmony-node root@ALICE_IP:/usr/local/bin/
scp target/release/quantumharmony-node root@BOB_IP:/usr/local/bin/
scp target/release/quantumharmony-node root@CHARLIE_IP:/usr/local/bin/

# Copy startup scripts
scp start-3validators.sh root@ALICE_IP:/root/
# ... modify for distributed deployment
```

---

## 📈 Success Metrics

After deployment, verify:

✅ **Block Production**: All 3 validators producing blocks
✅ **Peer Connectivity**: Each validator sees 2 peers
✅ **Priority Queue RPC**: All 3 endpoints (5555-5557) responding
✅ **SPHINCS+ Keys**: Non-zero keys generated for all validators
✅ **Falcon1024**: Vote signatures working
✅ **No Crashes**: Bob and Charlie running without "SelectNextSome" error

---

## 🎯 Timeline

| Task | Duration | Notes |
|------|----------|-------|
| Cloud provider selection | 1 hour | Review this document |
| Account setup | 30 min | Sign up, payment |
| VM creation | 30 min | 3 droplets |
| Docker installation | 30 min | All 3 VMs |
| Binary deployment | 1 hour | Build + copy |
| Configuration | 2 hours | Chain spec, keys, networking |
| Testing & debugging | 2 hours | Verify everything works |
| **Total** | **~8 hours** | Can be done in 1 day |

---

## 💡 Next Steps

1. **This Week** (Nov 19-26):
   - Select cloud provider (Recommended: DigitalOcean)
   - Create 3 VM instances
   - Deploy validators
   - Verify working

2. **Next Week** (Nov 27 - Dec 3):
   - Add monitoring
   - Document process
   - Create automation scripts
   - Prepare for mainnet

---

**Last Updated**: November 19, 2025
**Contact**: Check docs/COMPREHENSIVE_TODO_LIST.md for project status
**Budget Recommendation**: DigitalOcean ($288/month) or Hetzner ($90/month) for development
