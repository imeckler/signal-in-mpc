# UpCloud: one data disk (block storage) for a node, kept by `deploy.py destroy` unless
# --delete-data. Unformatted: the node formats it only if blank.
terraform {
  required_providers {
    upcloud = { source = "UpCloudLtd/upcloud" }
  }
}

variable "name" { type = string }
variable "region" { type = string }
variable "size_gb" { type = number }

resource "upcloud_storage" "data" {
  title = var.name
  size  = var.size_gb
  tier  = "maxiops"
  zone  = var.region
}

output "disk_id" { value = upcloud_storage.data.id }
# UpCloud attaches it as the second virtio disk (after the system disk).
output "device" { value = "/dev/vdb" }
