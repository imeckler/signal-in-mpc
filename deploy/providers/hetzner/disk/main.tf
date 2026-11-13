# Hetzner Cloud: one data disk (volume) for a node. Kept by `deploy.py destroy` (it lives in the
# separate `disks` stack) unless --delete-data. Unformatted: the node formats it only if blank.
terraform {
  required_providers {
    hcloud = { source = "hetznercloud/hcloud" }
  }
}

variable "name" { type = string }
variable "region" { type = string }
variable "size_gb" { type = number }

resource "hcloud_volume" "data" {
  name     = var.name
  size     = var.size_gb
  location = var.region
  labels   = { "managed-by" = "tls-mpc-deploy" }
  lifecycle { prevent_destroy = false }
}

output "disk_id" { value = tostring(hcloud_volume.data.id) }
output "device" { value = hcloud_volume.data.linux_device }
