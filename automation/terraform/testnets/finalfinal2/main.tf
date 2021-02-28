terraform {
  required_version = ">= 0.14.0"
  backend "s3" {
    key     = "terraform-finalfinal2.tfstate"
    encrypt = true
    region  = "us-west-2"
    bucket  = "o1labs-terraform-state"
    acl     = "bucket-owner-full-control"
  }
}

provider "aws" {
  region = "us-west-2"
}

provider "google" {
  alias   = "google-us-east4"
  project = "o1labs-192920"
  region  = "us-east4"
  zone    = "us-east4-b"
}

provider "google" {
  alias   = "google-us-east1"
  project = "o1labs-192920"
  region  = "us-east1"
  zone    = "us-east1-b"
}

provider "google" {
  alias   = "google-us-central1"
  project = "o1labs-192920"
  region  = "us-central1"
  zone    = "us-central1-c"
}


variable "whale_count" {
  type = number

  description = "Number of online whales for the network to run"
  default     = 0
}

variable "fish_count" {
  type = number

  description = "Number of online fish for the network to run"
  default     = 0
}

variable "seed_count" {
  default     = 6
}

locals {
  testnet_name = "finalfinal2"
  coda_image = "gcr.io/o1labs-192920/coda-daemon:0.4.3-compatible-5e78a42"
  coda_archive_image = "gcr.io/o1labs-192920/coda-archive:0.4.3-compatible-5e78a42"

  # replace with `make_report_discord_webhook_url = ""` if not in use (will fail if file not present)
  make_report_discord_webhook_url = <<EOT
    ${file("../../../discord_webhook_url.txt")}
  EOT

  # replace with `make_report_accounts = ""` if not in use (will fail if file not present)
  # make_report_accounts = <<EOT
  #   ${file("../../../${local.testnet_name}-accounts.csv")}
  # EOT
  make_report_accounts = ""
}

module "testnet_east" {
  providers = { google.gke = google.google-us-central1 }
  source    = "../../modules/o1-testnet"

  artifact_path = abspath(path.module)

  cluster_name   = "coda-infra-central1"
  cluster_region = "us-central1"
  k8s_context    = "gke_o1labs-192920_us-east4_coda-infra-central1"
  testnet_name   = local.testnet_name

  coda_image         = local.coda_image
  coda_archive_image = local.coda_archive_image
  coda_agent_image   = "codaprotocol/coda-user-agent:0.1.8"
  coda_bots_image    = "codaprotocol/coda-bots:0.0.13-beta-1"
  coda_points_image  = "codaprotocol/coda-points-hack:32b.4"
  watchdog_image     = "gcr.io/o1labs-192920/watchdog:0.3.9"

  archive_node_count  = 3
  mina_archive_schema = "https://raw.githubusercontent.com/MinaProtocol/mina/5e78a42b8e6abd0534300d9b9540360e0d67fed0/src/app/archive/create_schema.sql" 

  archive_configs       = [
    {
      name = "archive-1"
      enableLocalDaemon = false
      enablePostgresDB  = true
      postgresHost      = "archive-1-postgresql"
    },
    {
      name = "archive-2"
      enableLocalDaemon = false
      enablePostgresDB  = false
      postgresHost      = "archive-1-postgresql"
    },
    {
      name = "archive-3"
      enableLocalDaemon = false
      enablePostgresDB  = true
      postgresHost      = "archive-3-postgresql"
    }
  ]

  seed_zone   = local.seed_zone
  seed_region = local.seed_region

  log_level           = "Info"
  log_txn_pool_gossip = false

  snark_worker_replicas = 0
  whale_count           = var.whale_count
  fish_count            = var.fish_count
  seed_count            = var.seed_count

  upload_blocks_to_gcloud         = true
  restart_nodes                   = false
  restart_nodes_every_mins        = "60"
  make_reports                    = true
  make_report_every_mins          = "5"
  make_report_discord_webhook_url = local.make_report_discord_webhook_url
  make_report_accounts            = local.make_report_accounts
  seed_peers_url                  = "https://storage.googleapis.com/seed-lists/final_final_2_(3)_seeds.txt?123"
}